/*
 * %CopyrightBegin%
 *
 * Copyright Ericsson 2023. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * %CopyrightEnd%
 */

extern "C"
{
#include <erl_nif.h>
#include <z3.h>
}

constexpr bool HARD_DEBUG = false;

#include <type_traits>
#include <algorithm>
#include <optional>
#include <atomic>
#include <limits>
#include <string>
#include <vector>
#include <tuple>
#include <map>

ERL_NIF_TERM am_ok;
ERL_NIF_TERM am_error;
ERL_NIF_TERM am_badarg;

ERL_NIF_TERM am_sat;
ERL_NIF_TERM am_unsat;
ERL_NIF_TERM am_unknown;

ERL_NIF_TERM am_true;
ERL_NIF_TERM am_false;

ERL_NIF_TERM am_conversion_needed;

ERL_NIF_TERM am_log_file;
ERL_NIF_TERM am_recursion_limit;

typedef int ExprHandle;

template<typename T>
static constexpr bool is_ast_type() {
    return std::is_same_v<T, Z3_app> || std::is_same_v<T, Z3_ast> ||
           std::is_same_v<T, Z3_func_decl> || std::is_same_v<T, Z3_sort>;
}

class ASTWrapper {
    Z3_context context;
    Z3_ast wrapped;

public:
    ASTWrapper() : context(nullptr), wrapped(nullptr) {
    }

    ASTWrapper(ASTWrapper &&other)
            : context(other.context), wrapped(other.wrapped) {
        other.wrapped = nullptr;
    }

    ASTWrapper(const ASTWrapper &other)
            : ASTWrapper(other.context, other.wrapped) {
    }

    template<typename T, typename = std::enable_if_t<is_ast_type<T>()>>
    ASTWrapper(Z3_context context_, T handle_)
            : ASTWrapper(context_, reinterpret_cast<Z3_ast>(handle_)) {
    }

    ASTWrapper(Z3_context context_, Z3_ast handle_)
            : context(context_), wrapped(handle_) {
        Z3_inc_ref(context, wrapped);
    }

    ~ASTWrapper() {
        Z3_dec_ref(context, wrapped);
    }

    template<Z3_ast_kind Expected>
    bool is() const {
        return Z3_get_ast_kind(context, wrapped) == Expected;
    }

    template<typename T, typename = std::enable_if_t<is_ast_type<T>()>>
    operator T() const {
        return reinterpret_cast<T>(wrapped);
    }
};

struct ASTVector : public std::vector<ASTWrapper> {
    template<typename T>
    auto handles() const {
        std::vector<T> result;
        for (auto handle : *this) {
            result.push_back(handle);
        }
        return result;
    }
};

template<typename T>
using ExprMap = std::map<ExprHandle, T>;

struct Z3Nif {
    std::atomic_bool in_use;

    bool logging_enabled;
    int symbol_counter;
    unsigned fence;

    bool closed;

    Z3_context context;
    Z3_solver solver;

    ExprMap<ASTWrapper> nodes;
    ExprMap<Z3_constructor> constructors;
    ExprMap<Z3_symbol> symbols;

    template<typename T>
    inline auto get(int id, const ExprMap<T> &expressions) {
        auto it = expressions.find(id);
        if (it != expressions.end()) {
            return std::optional<T>(it->second);
        }
        return std::optional<T>{};
    }

    template<typename T>
    inline bool add(int id, T expression, ExprMap<T> &expressions) {
        if (expressions.find(id) == expressions.end()) {
            expressions.emplace(id, expression);
            return true;
        }

        return false;
    }

    void close() {
        for (auto [_ignored, constructor] : constructors) {
            Z3_del_constructor(context, constructor);
        }

        constructors.clear();
        symbols.clear();
        nodes.clear();

        Z3_solver_dec_ref(context, solver);
        Z3_del_context(context);

        closed = true;
    }

    Z3Nif(Z3_context context_, Z3_solver solver_, bool logging_)
            : in_use(false), logging_enabled(logging_), symbol_counter(0),
              fence(0), closed(false), context(context_), solver(solver_) {
    }

    ~Z3Nif() {
        if (!closed) {
            close();
        }
    }
};

static ErlNifResourceType *resource_type;

static auto make_context(ErlNifEnv *env,
                         ERL_NIF_TERM options,
                         Z3_context &context) {
    struct Z3Config {
        Z3_config config;

        Z3Config() : config(Z3_mk_config()) {
        }

        ~Z3Config() {
            Z3_del_config(config);
        }

        operator Z3_config() {
            return config;
        }
    } config;

    (void)options;
    (void)env;

    context = Z3_mk_context_rc(config);
    return Z3_get_error_code(context) == Z3_OK;
}

static bool make_solver(ErlNifEnv *env,
                        ERL_NIF_TERM options,
                        Z3_context context,
                        Z3_solver &solver,
                        bool &logging_enabled) {
    struct Z3Params {
        Z3_context context;
        Z3_params params;

        Z3Params(Z3_context context_) : context(context_) {
            params = Z3_mk_params(context);
            Z3_params_inc_ref(context, params);
        }

        ~Z3Params() {
            Z3_params_dec_ref(context, params);
        }

        operator Z3_params() {
            return params;
        }
    } params(context);

    ERL_NIF_TERM option_value;

    unsigned recursion_limit = 100000000;
    if (enif_get_map_value(env, options, am_recursion_limit, &option_value)) {
        if (!enif_get_uint(env, option_value, &recursion_limit)) {
            return false;
        }
    }

    Z3_params_set_uint(context,
                       params,
                       Z3_mk_string_symbol(context, "rlimit"),
                       recursion_limit);

    if (Z3_get_error_code(context) != Z3_OK) {
        return false;
    }

    logging_enabled = false;
    if (enif_get_map_value(env, options, am_log_file, &option_value)) {
        ErlNifBinary log_file;

        if (!enif_inspect_iolist_as_binary(env, option_value, &log_file)) {
            return false;
        }

        std::string as_string((const char *)log_file.data, log_file.size);
        Z3_params_set_symbol(context,
                             params,
                             Z3_mk_string_symbol(context, "smtlib2_log"),
                             Z3_mk_string_symbol(context, as_string.c_str()));

        if (Z3_get_error_code(context) != Z3_OK) {
            return false;
        }

        logging_enabled = true;
    }

    /* Disable the CTRL+C interrupt handler. */
    auto ctrl_c = Z3_mk_string_symbol(context, "ctrl_c");
    Z3_params_set_bool(context, params, ctrl_c, false);

    if (Z3_get_error_code(context) != Z3_OK) {
        return false;
    }

    {
        /* TODO: Clean this up and expose a neat interface for picking tactics,
         * this is a good enough default for experimentation but we'll most
         * likely want something different in the future.
         *
         * (Also note that not all solvers support the smtlib2_log option) */
        struct Z3Tactic {
            Z3_context context;
            Z3_tactic tactic;

            Z3Tactic(const Z3Tactic &other)
                    : context(other.context), tactic(other.tactic) {
                Z3_tactic_inc_ref(context, tactic);
            }

            Z3Tactic(Z3_context context_, Z3_tactic tactic_)
                    : context(context_), tactic(tactic_) {
                Z3_tactic_inc_ref(context, tactic);
            }

            ~Z3Tactic() {
                Z3_tactic_dec_ref(context, tactic);
            }

            operator Z3_tactic() {
                return tactic;
            }
        };

        std::vector<Z3Tactic> tactics;

        for (auto name : {"elim-and", "reduce-args", "smt"}) {
            auto tactic = Z3_mk_tactic(context, name);

            if (Z3_get_error_code(context) != Z3_OK) {
                return false;
            }

            tactics.emplace_back(context, tactic);
        }

        Z3Tactic combined = tactics[0];

        for (unsigned i = 1, last = tactics.size(); i < last; i++) {
            auto tactic = Z3_tactic_and_then(context, combined, tactics[i]);

            if (Z3_get_error_code(context) != Z3_OK) {
                return false;
            }

            combined = Z3Tactic(context, tactic);
        }

        /* FIXME: The tactic used to create the solver has to live as long as
         * the solver itself: the latter does not maintain a reference to it.
         * Let this leak for now. */
        Z3_tactic_inc_ref(context, combined);

        solver = Z3_mk_solver_from_tactic(context, combined);
        Z3_solver_inc_ref(context, solver);
    }

    Z3_solver_set_params(context, solver, params);

    if (Z3_get_error_code(context) != Z3_OK) {
        Z3_solver_dec_ref(context, solver);
        return false;
    }

    return true;
}

static ERL_NIF_TERM new_nif(ErlNifEnv *env,
                            int argc,
                            const ERL_NIF_TERM argv[]) {
    ERL_NIF_TERM result;
    Z3_context context;

    if (make_context(env, argv[0], context)) {
        bool logging_enabled;
        Z3_solver solver;

        if (make_solver(env, argv[0], context, solver, logging_enabled)) {
            if constexpr (!HARD_DEBUG) {
                /* Make sure we get error returns instead of crashing the
                 * emulator. */
                Z3_set_error_handler(context, nullptr);
            }

            void *resource =
                    new (enif_alloc_resource(resource_type, sizeof(Z3Nif)))
                            Z3Nif(context, solver, logging_enabled);
            result = enif_make_resource(env, resource);
            enif_release_resource(resource);
        } else {
            result = enif_raise_exception(env, am_badarg);
            Z3_del_context(context);
        }
    } else {
        result = enif_raise_exception(env, am_badarg);
    }

    return result;
}

static ERL_NIF_TERM close_nif(Z3Nif *state,
                              ErlNifEnv *env,
                              int argc,
                              const ERL_NIF_TERM argv[]) {
    state->close();
    return am_ok;
}

template<typename T, typename U>
static bool unwrap_list(Z3Nif *state,
                        const ExprMap<T> &expressions,
                        ErlNifEnv *env,
                        const ERL_NIF_TERM term,
                        U &result) {
    ERL_NIF_TERM head, tail = term;

    while (enif_get_list_cell(env, tail, &head, &tail)) {
        int id;

        if (!enif_get_int(env, head, &id)) {
            return false;
        }

        auto item = state->get(id, expressions);
        if (!item) {
            return false;
        }

        result.emplace_back(*item);
    }

    return enif_is_empty_list(env, tail);
}

static ERL_NIF_TERM symbol_nif(Z3Nif *state,
                               int expression_id,
                               ErlNifEnv *env,
                               int argc,
                               const ERL_NIF_TERM argv[]) {
    Z3_symbol symbol;

    if (!state->logging_enabled) {
        symbol = Z3_mk_int_symbol(state->context, state->symbol_counter++);
    } else {
        /* When logging is enabled, make an attempt to have sensible names. Far
         * from all names are atoms, but some of the most important ones
         * are. */
        char name[256];

        if (enif_get_atom(env, argv[0], name, 256, ERL_NIF_UTF8)) {
            symbol = Z3_mk_string_symbol(state->context, name);
        } else {
            symbol = Z3_mk_int_symbol(state->context, state->symbol_counter++);
        }
    }

    if (Z3_get_error_code(state->context) == Z3_OK) {
        if (state->add(expression_id, symbol, state->symbols)) {
            return am_ok;
        }
    }

    return am_error;
}

template<Z3_sort(Func)(Z3_context)>
static ERL_NIF_TERM primitive_sort_nif(Z3Nif *state,
                                       int expression_id,
                                       ErlNifEnv *env,
                                       int argc,
                                       const ERL_NIF_TERM argv[]) {
    auto result = Func(state->context);

    if (Z3_get_error_code(state->context) == Z3_OK) {
        if (state->add(expression_id,
                       ASTWrapper(state->context, result),
                       state->nodes)) {
            return am_ok;
        }
    }

    return am_error;
}

template<Z3_ast(Func)(Z3_context, unsigned, const Z3_ast *)>
static ERL_NIF_TERM unary_vararg_nif(Z3Nif *state,
                                     int expression_id,
                                     ErlNifEnv *env,
                                     int argc,
                                     const ERL_NIF_TERM argv[]) {
    ASTVector expressions;

    if (unwrap_list(state, state->nodes, env, argv[0], expressions)) {
        auto op = Func(state->context,
                       expressions.size(),
                       expressions.handles<Z3_ast>().data());

        if (Z3_get_error_code(state->context) == Z3_OK) {
            if (state->add(expression_id,
                           ASTWrapper(state->context, op),
                           state->nodes)) {
                return am_ok;
            }
        }
    }

    return am_error;
}

template<Z3_ast(Func)(Z3_context, Z3_ast)>
static ERL_NIF_TERM unary_nif(Z3Nif *state,
                              int expression_id,
                              ErlNifEnv *env,
                              int argc,
                              const ERL_NIF_TERM argv[]) {
    int argument_id;

    if (enif_get_int(env, argv[0], &argument_id)) {
        auto argument = state->get(argument_id, state->nodes);

        if (argument) {
            auto result = Func(state->context, *argument);

            if (Z3_get_error_code(state->context) == Z3_OK) {
                if (state->add(expression_id,
                               ASTWrapper(state->context, result),
                               state->nodes)) {
                    return am_ok;
                }
            }
        }
    }

    return am_error;
}

template<Z3_ast(Func)(Z3_context, Z3_ast, Z3_ast)>
static ERL_NIF_TERM binary_nif(Z3Nif *state,
                               int expression_id,
                               ErlNifEnv *env,
                               int argc,
                               const ERL_NIF_TERM argv[]) {
    int lhs_id, rhs_id;

    if (enif_get_int(env, argv[0], &lhs_id) &&
        enif_get_int(env, argv[1], &rhs_id)) {
        auto lhs = state->get(lhs_id, state->nodes),
             rhs = state->get(rhs_id, state->nodes);
        if (lhs && rhs) {
            auto result = Func(state->context, *lhs, *rhs);

            if (Z3_get_error_code(state->context) == Z3_OK) {
                if (state->add(expression_id,
                               ASTWrapper(state->context, result),
                               state->nodes)) {
                    return am_ok;
                }
            }
        }
    }

    return am_error;
}

template<Z3_func_decl(Func)(Z3_context c,
                            Z3_symbol s,
                            unsigned domain_size,
                            Z3_sort const *domain,
                            Z3_sort range)>
static ERL_NIF_TERM function_declaration_nif(Z3Nif *state,
                                             int expression_id,
                                             ErlNifEnv *env,
                                             int argc,
                                             const ERL_NIF_TERM argv[]) {
    int symbol_id, range_id;

    if (enif_get_int(env, argv[0], &symbol_id) &&
        enif_get_int(env, argv[2], &range_id)) {
        auto symbol = state->get(symbol_id, state->symbols);
        auto range = state->get(range_id, state->nodes);

        if (symbol && range && range->is<Z3_SORT_AST>()) {
            ASTVector domain;

            if (unwrap_list(state, state->nodes, env, argv[1], domain) &&
                std::all_of(domain.cbegin(),
                            domain.cend(),
                            [](const ASTWrapper &element) {
                                return element.is<Z3_SORT_AST>();
                            })) {
                auto result = Func(state->context,
                                   *symbol,
                                   domain.size(),
                                   domain.handles<Z3_sort>().data(),
                                   *range);

                if (Z3_get_error_code(state->context) == Z3_OK) {
                    if (state->add(expression_id,
                                   ASTWrapper(state->context, result),
                                   state->nodes)) {
                        return am_ok;
                    }
                }
            }
        }
    }

    return am_error;
}

static ERL_NIF_TERM array_sort_nif(Z3Nif *state,
                                   int expression_id,
                                   ErlNifEnv *env,
                                   int argc,
                                   const ERL_NIF_TERM argv[]) {
    ASTVector domain;

    if (unwrap_list(state, state->nodes, env, argv[0], domain) &&
        std::all_of(domain.cbegin(),
                    domain.cend(),
                    [](const ASTWrapper &element) {
                        return element.is<Z3_SORT_AST>();
                    })) {
        int range_id;

        if (enif_get_int(env, argv[1], &range_id)) {
            auto range = state->get(range_id, state->nodes);

            if (range && range->is<Z3_SORT_AST>()) {
                auto op = Z3_mk_array_sort_n(state->context,
                                             domain.size(),
                                             domain.handles<Z3_sort>().data(),
                                             *range);

                if (Z3_get_error_code(state->context) == Z3_OK) {
                    if (state->add(expression_id,
                                   ASTWrapper(state->context, op),
                                   state->nodes)) {
                        return am_ok;
                    }
                }
            }
        }
    }

    return am_error;
}

static ERL_NIF_TERM array_select_nif(Z3Nif *state,
                                     int expression_id,
                                     ErlNifEnv *env,
                                     int argc,
                                     const ERL_NIF_TERM argv[]) {
    ASTVector arguments;
    int array_id;

    if (enif_get_int(env, argv[0], &array_id)) {
        auto array = state->get(array_id, state->nodes);

        if (array &&
            unwrap_list(state, state->nodes, env, argv[1], arguments)) {
            auto op = Z3_mk_select_n(state->context,
                                     *array,
                                     arguments.size(),
                                     arguments.handles<Z3_ast>().data());

            if (Z3_get_error_code(state->context) == Z3_OK) {
                if (state->add(expression_id,
                               ASTWrapper(state->context, op),
                               state->nodes)) {
                    return am_ok;
                }
            }
        }
    }

    return am_error;
}

static ERL_NIF_TERM array_store_nif(Z3Nif *state,
                                    int expression_id,
                                    ErlNifEnv *env,
                                    int argc,
                                    const ERL_NIF_TERM argv[]) {
    ASTVector arguments;
    int array_id, value_id;

    if (enif_get_int(env, argv[0], &array_id) &&
        enif_get_int(env, argv[2], &value_id)) {
        auto array = state->get(array_id, state->nodes),
             value = state->get(value_id, state->nodes);

        if (array && value &&
            unwrap_list(state, state->nodes, env, argv[1], arguments)) {
            auto op = Z3_mk_store_n(state->context,
                                    *array,
                                    arguments.size(),
                                    arguments.handles<Z3_ast>().data(),
                                    *value);

            if (Z3_get_error_code(state->context) == Z3_OK) {
                if (state->add(expression_id,
                               ASTWrapper(state->context, op),
                               state->nodes)) {
                    return am_ok;
                }
            }
        }
    }

    return am_error;
}

static ERL_NIF_TERM sequence_sort_nif(Z3Nif *state,
                                      int expression_id,
                                      ErlNifEnv *env,
                                      int argc,
                                      const ERL_NIF_TERM argv[]) {
    int sort_id;

    if (enif_get_int(env, argv[0], &sort_id)) {
        auto sort = state->get(sort_id, state->nodes);

        if (sort && sort->is<Z3_SORT_AST>()) {
            auto result = Z3_mk_seq_sort(state->context, *sort);

            if (Z3_get_error_code(state->context) == Z3_OK) {
                if (state->add(expression_id,
                               ASTWrapper(state->context, result),
                               state->nodes)) {
                    return am_ok;
                }
            }
        }
    }

    return am_error;
}

static ERL_NIF_TERM sequence_empty_nif(Z3Nif *state,
                                       int expression_id,
                                       ErlNifEnv *env,
                                       int argc,
                                       const ERL_NIF_TERM argv[]) {
    int sort_id;

    if (enif_get_int(env, argv[0], &sort_id)) {
        auto sort = state->get(sort_id, state->nodes);

        if (sort && sort->is<Z3_SORT_AST>()) {
            auto result = Z3_mk_seq_empty(state->context, *sort);

            if (Z3_get_error_code(state->context) == Z3_OK) {
                if (state->add(expression_id,
                               ASTWrapper(state->context, result),
                               state->nodes)) {
                    return am_ok;
                }
            }
        }
    }

    return am_error;
}

static ERL_NIF_TERM uninterpreted_sort_nif(Z3Nif *state,
                                           int expression_id,
                                           ErlNifEnv *env,
                                           int argc,
                                           const ERL_NIF_TERM argv[]) {
    int symbol_id;

    if (enif_get_int(env, argv[0], &symbol_id)) {
        if (auto symbol = state->get(symbol_id, state->symbols)) {
            auto result = Z3_mk_uninterpreted_sort(state->context, *symbol);

            if (Z3_get_error_code(state->context) == Z3_OK) {
                if (state->add(expression_id,
                               ASTWrapper(state->context, result),
                               state->nodes)) {
                    return am_ok;
                }
            }
        }
    }

    return am_error;
}

static ERL_NIF_TERM linear_order_nif(Z3Nif *state,
                                     int expression_id,
                                     ErlNifEnv *env,
                                     int argc,
                                     const ERL_NIF_TERM argv[]) {
    int sort_id, index;

    if (enif_get_int(env, argv[0], &sort_id) &&
        enif_get_int(env, argv[1], &index) && index >= 0) {
        if (auto sort = state->get(sort_id, state->nodes)) {
            auto result = Z3_mk_linear_order(state->context, *sort, index);

            if (Z3_get_error_code(state->context) == Z3_OK) {
                if (state->add(expression_id,
                               ASTWrapper(state->context, result),
                               state->nodes)) {
                    return am_ok;
                }
            }
        }
    }

    return am_error;
}

static ERL_NIF_TERM make_boolean_nif(Z3Nif *state,
                                     int expression_id,
                                     ErlNifEnv *env,
                                     int argc,
                                     const ERL_NIF_TERM argv[]) {
    bool is_true = enif_is_identical(argv[0], am_true),
         is_false = enif_is_identical(argv[0], am_false);

    if (is_true || is_false) {
        auto result = is_true ? Z3_mk_true(state->context)
                              : Z3_mk_false(state->context);

        if (Z3_get_error_code(state->context) == Z3_OK) {
            if (state->add(expression_id,
                           ASTWrapper(state->context, result),
                           state->nodes)) {
                return am_ok;
            }
        }
    }

    return am_error;
}

static ERL_NIF_TERM make_integer_nif(Z3Nif *state,
                                     int expression_id,
                                     ErlNifEnv *env,
                                     int argc,
                                     const ERL_NIF_TERM argv[]) {
    int sort_id;

    if (!enif_get_int(env, argv[0], &sort_id)) {
        return am_error;
    }

    auto sort = state->get(sort_id, state->nodes);
    if (!sort) {
        return am_error;
    }

    switch (enif_term_type(env, argv[1])) {
    case ERL_NIF_TERM_TYPE_INTEGER: {
        int value;

        if (!enif_get_int(env, argv[1], &value)) {
            return am_conversion_needed;
        }

        auto result = Z3_mk_int(state->context, value, *sort);

        if (Z3_get_error_code(state->context) == Z3_OK) {
            if (state->add(expression_id,
                           ASTWrapper(state->context, result),
                           state->nodes)) {
                return am_ok;
            }
        }
        break;
    }
    case ERL_NIF_TERM_TYPE_BITSTRING: {
        ErlNifBinary string;

        if (enif_inspect_binary(env, argv[1], &string) && string.size >= 1 &&
            string.data[string.size - 1] == '\0') {
            auto result = Z3_mk_numeral(state->context,
                                        (Z3_string)string.data,
                                        *sort);

            if (Z3_get_error_code(state->context) == Z3_OK) {
                if (state->add(expression_id,
                               ASTWrapper(state->context, result),
                               state->nodes)) {
                    return am_ok;
                }
            }
        }
        break;
    }
    default:
        break;
    }

    return am_error;
}

static ERL_NIF_TERM make_real_nif(Z3Nif *state,
                                  int expression_id,
                                  ErlNifEnv *env,
                                  int argc,
                                  const ERL_NIF_TERM argv[]) {
    switch (enif_term_type(env, argv[0])) {
    case ERL_NIF_TERM_TYPE_INTEGER: {
        int numerator, denominator;

        if (!enif_get_int(env, argv[0], &numerator) ||
            !enif_get_int(env, argv[1], &denominator)) {
            return am_conversion_needed;
        }

        auto result = Z3_mk_real(state->context, numerator, denominator);

        if (Z3_get_error_code(state->context) == Z3_OK) {
            if (state->add(expression_id,
                           ASTWrapper(state->context, result),
                           state->nodes)) {
                return am_ok;
            }
        }
        break;
    }
    case ERL_NIF_TERM_TYPE_BITSTRING: {
        ErlNifBinary string;

        if (enif_inspect_binary(env, argv[0], &string) && string.size >= 1 &&
            string.data[string.size - 1] == '\0') {
            auto result = Z3_mk_numeral(state->context,
                                        (Z3_string)string.data,
                                        Z3_mk_real_sort(state->context));

            if (Z3_get_error_code(state->context) == Z3_OK) {
                if (state->add(expression_id,
                               ASTWrapper(state->context, result),
                               state->nodes)) {
                    return am_ok;
                }
            }
        }
        break;
    }
    default:
        break;
    }

    return am_error;
}

static ERL_NIF_TERM make_string_nif(Z3Nif *state,
                                    int expression_id,
                                    ErlNifEnv *env,
                                    int argc,
                                    const ERL_NIF_TERM argv[]) {
    ErlNifBinary value;

    if (enif_inspect_binary(env, argv[0], &value) && value.size >= 0 &&
        value.size < std::numeric_limits<unsigned int>::max()) {
        auto result = Z3_mk_lstring(state->context,
                                    value.size,
                                    (Z3_string)value.data);

        if (Z3_get_error_code(state->context) == Z3_OK) {
            if (state->add(expression_id,
                           ASTWrapper(state->context, result),
                           state->nodes)) {
                return am_ok;
            }
        }
    }

    return am_error;
}

static ERL_NIF_TERM same_nif(Z3Nif *state,
                             int expression_id,
                             ErlNifEnv *env,
                             int argc,
                             const ERL_NIF_TERM argv[]) {
    ASTVector expressions;

    if (unwrap_list(state, state->nodes, env, argv[0], expressions)) {
        if (expressions.size() == 2) {
            auto result =
                    Z3_mk_eq(state->context, expressions[0], expressions[1]);

            if (Z3_get_error_code(state->context) == Z3_OK) {
                if (state->add(expression_id,
                               ASTWrapper(state->context, result),
                               state->nodes)) {
                    return am_ok;
                }
            }
        } else if (expressions.size() > 2) {
            auto distinct =
                    Z3_mk_distinct(state->context,
                                   expressions.size(),
                                   expressions.handles<Z3_ast>().data());

            if (Z3_get_error_code(state->context) == Z3_OK) {
                Z3_inc_ref(state->context, distinct);

                auto result = Z3_mk_not(state->context, distinct);
                auto succeeded = (Z3_get_error_code(state->context) == Z3_OK);

                Z3_dec_ref(state->context, distinct);

                if (succeeded) {
                    if (state->add(expression_id,
                                   ASTWrapper(state->context, result),
                                   state->nodes)) {
                        return am_ok;
                    }
                }
            }
        }
    }

    return am_error;
}

static ERL_NIF_TERM one_of_nif(Z3Nif *state,
                               int expression_id,
                               ErlNifEnv *env,
                               int argc,
                               const ERL_NIF_TERM argv[]) {
    ASTVector expressions;

    if (unwrap_list(state, state->nodes, env, argv[0], expressions)) {
        std::vector<int> coefficients(expressions.size());
        std::fill(coefficients.begin(), coefficients.end(), 1);

        auto result = Z3_mk_pbeq(state->context,
                                 expressions.size(),
                                 expressions.handles<Z3_ast>().data(),
                                 coefficients.data(),
                                 1);

        if (Z3_get_error_code(state->context) == Z3_OK) {
            if (state->add(expression_id,
                           ASTWrapper(state->context, result),
                           state->nodes)) {
                return am_ok;
            }
        }
    }

    return am_error;
}

static ERL_NIF_TERM if_then_else_nif(Z3Nif *state,
                                     int expression_id,
                                     ErlNifEnv *env,
                                     int argc,
                                     const ERL_NIF_TERM argv[]) {
    int cond_id, then_id, otherwise_id;

    if (enif_get_int(env, argv[0], &cond_id) &&
        enif_get_int(env, argv[1], &then_id) &&
        enif_get_int(env, argv[2], &otherwise_id)) {
        auto cond = state->get(cond_id, state->nodes),
             then = state->get(then_id, state->nodes),
             otherwise = state->get(otherwise_id, state->nodes);

        if (cond && then && otherwise) {
            auto result = Z3_mk_ite(state->context, *cond, *then, *otherwise);
            if (Z3_get_error_code(state->context) == Z3_OK) {
                if (state->add(expression_id,
                               ASTWrapper(state->context, result),
                               state->nodes)) {
                    return am_ok;
                }
            }
        }
    }

    return am_error;
}

static ERL_NIF_TERM application_nif(Z3Nif *state,
                                    int expression_id,
                                    ErlNifEnv *env,
                                    int argc,
                                    const ERL_NIF_TERM argv[]) {
    ASTVector arguments;
    int func_id;

    if (enif_get_int(env, argv[0], &func_id) &&
        unwrap_list(state, state->nodes, env, argv[1], arguments)) {
        auto func = state->get(func_id, state->nodes);

        if (func) {
            if (func->is<Z3_FUNC_DECL_AST>()) {
                auto result = Z3_mk_app(state->context,
                                        *func,
                                        arguments.size(),
                                        arguments.handles<Z3_ast>().data());

                if (Z3_get_error_code(state->context) == Z3_OK) {
                    if (state->add(expression_id,
                                   ASTWrapper(state->context, result),
                                   state->nodes)) {
                        return am_ok;
                    }
                }
            }
        }
    }

    return am_error;
}

static ERL_NIF_TERM constant_nif(Z3Nif *state,
                                 int expression_id,
                                 ErlNifEnv *env,
                                 int argc,
                                 const ERL_NIF_TERM argv[]) {
    int symbol_id, sort_id;

    if (enif_get_int(env, argv[0], &symbol_id) &&
        enif_get_int(env, argv[1], &sort_id)) {
        auto symbol = state->get(symbol_id, state->symbols);
        auto sort = state->get(sort_id, state->nodes);

        if (symbol && sort && sort->is<Z3_SORT_AST>()) {
            auto result = Z3_mk_const(state->context, *symbol, *sort);

            if (Z3_get_error_code(state->context) == Z3_OK) {
                if (state->add(expression_id,
                               ASTWrapper(state->context, result),
                               state->nodes)) {
                    return am_ok;
                }
            }
        }
    }

    return am_error;
}

static ERL_NIF_TERM define_function_nif(Z3Nif *state,
                                        ErlNifEnv *env,
                                        int argc,
                                        const ERL_NIF_TERM argv[]) {
    ASTVector arguments;
    int func_id, body_id;

    if (enif_get_int(env, argv[0], &func_id) &&
        enif_get_int(env, argv[2], &body_id)) {
        auto function = state->get(func_id, state->nodes);
        auto body = state->get(body_id, state->nodes);

        if (body && function && function->is<Z3_FUNC_DECL_AST>()) {
            if (unwrap_list(state, state->nodes, env, argv[1], arguments)) {
                Z3_add_rec_def(state->context,
                               *function,
                               arguments.size(),
                               arguments.handles<Z3_ast>().data(),
                               *body);

                if (Z3_get_error_code(state->context) == Z3_OK) {
                    return am_ok;
                }
            }
        }
    }

    return am_error;
}

/* **************************************************************************
 */

static ERL_NIF_TERM constructor_nif(Z3Nif *state,
                                    int expression_id,
                                    ErlNifEnv *env,
                                    int argc,
                                    const ERL_NIF_TERM argv[]) {
    std::vector<unsigned> field_sort_refs;
    std::vector<Z3_symbol> field_names;
    std::vector<Z3_sort> field_sorts;
    int name_id, recognizer_id;
    ERL_NIF_TERM head, tail;

    if (!enif_get_int(env, argv[0], &name_id) ||
        !enif_get_int(env, argv[1], &recognizer_id) ||
        !enif_is_list(env, argv[2])) {
        return am_error;
    }

    auto name = state->get(name_id, state->symbols),
         recognizer = state->get(recognizer_id, state->symbols);

    if (!name || !recognizer) {
        return am_error;
    }

    tail = argv[2];

    while (enif_get_list_cell(env, tail, &head, &tail)) {
        int field_name_id, field_sort_id;
        const ERL_NIF_TERM *spec;
        int arity;

        if (!enif_get_tuple(env, head, &arity, &spec) || arity != 2) {
            return am_error;
        }

        if (!enif_get_int(env, spec[0], &field_name_id) ||
            !enif_get_int(env, spec[1], &field_sort_id)) {
            return am_error;
        }

        auto field_name = state->get(field_name_id, state->symbols);
        if (!field_name) {
            return am_error;
        }

        field_names.emplace_back(*field_name);

        auto field_sort = state->get(field_sort_id, state->nodes);

        if (!field_sort || !field_sort->is<Z3_SORT_AST>()) {
            return am_error;
        }

        field_sorts.emplace_back(*field_sort);
        field_sort_refs.emplace_back(0);
    }

    if (enif_is_empty_list(env, tail)) {
        auto result = Z3_mk_constructor(state->context,
                                        *name,
                                        *recognizer,
                                        field_names.size(),
                                        field_names.data(),
                                        field_sorts.data(),
                                        field_sort_refs.data());

        if (Z3_get_error_code(state->context) == Z3_OK) {
            if (state->add(expression_id, result, state->constructors)) {
                return am_ok;
            }
        }
    }

    return am_error;
}

static ERL_NIF_TERM datatype_nif(Z3Nif *state,
                                 int expression_id,
                                 ErlNifEnv *env,
                                 int argc,
                                 const ERL_NIF_TERM argv[]) {
    std::vector<Z3_constructor> constructors;
    int name_id;

    if (enif_get_int(env, argv[0], &name_id)) {
        auto name = state->get(name_id, state->symbols);

        if (name && unwrap_list(state,
                                state->constructors,
                                env,
                                argv[1],
                                constructors)) {
            auto result = Z3_mk_datatype(state->context,
                                         *name,
                                         constructors.size(),
                                         constructors.data());

            if (Z3_get_error_code(state->context) == Z3_OK) {
                if (state->add(expression_id,
                               ASTWrapper(state->context, result),
                               state->nodes)) {
                    return am_ok;
                }
            }
        }
    }

    return am_error;
}

static ERL_NIF_TERM datatype_sort_nif(Z3Nif *state,
                                      int expression_id,
                                      ErlNifEnv *env,
                                      int argc,
                                      const ERL_NIF_TERM argv[]) {
    int name_id;

    if (enif_get_int(env, argv[0], &name_id)) {
        auto name = state->get(name_id, state->symbols);

        if (name) {
            auto result = Z3_mk_datatype_sort(state->context, *name);

            if (Z3_get_error_code(state->context) == Z3_OK) {
                if (state->add(expression_id,
                               ASTWrapper(state->context, result),
                               state->nodes)) {
                    return am_ok;
                }
            }
        }
    }

    return am_error;
}

static ERL_NIF_TERM query_constructor_nif(Z3Nif *state,
                                          ErlNifEnv *env,
                                          int argc,
                                          const ERL_NIF_TERM argv[]) {
    int constructor_id, constructor_func_id, tester_func_id;

    if (!enif_get_int(env, argv[0], &constructor_id) ||
        !enif_get_int(env, argv[1], &constructor_func_id) ||
        !enif_get_int(env, argv[2], &tester_func_id) ||
        !enif_is_list(env, argv[3])) {
        return am_error;
    }

    auto constructor = state->get(constructor_id, state->constructors);

    if (!constructor) {
        return am_error;
    }

    std::vector<int> accessor_ids;
    ERL_NIF_TERM head, tail;

    tail = argv[3];
    while (enif_get_list_cell(env, tail, &head, &tail)) {
        int id;

        if (!enif_get_int(env, head, &id)) {
            return false;
        }

        accessor_ids.emplace_back(id);
    }

    std::vector<Z3_func_decl> accessors(accessor_ids.size());
    Z3_func_decl constructor_func, tester_func;

    Z3_query_constructor(state->context,
                         *constructor,
                         accessors.size(),
                         &constructor_func,
                         &tester_func,
                         accessors.data());

    if (Z3_get_error_code(state->context) != Z3_OK) {
        return am_error;
    }

    if (!state->add(constructor_func_id,
                    ASTWrapper(state->context, constructor_func),
                    state->nodes)) {
        return am_error;
    }

    if (!state->add(tester_func_id,
                    ASTWrapper(state->context, tester_func),
                    state->nodes)) {
        return am_error;
    }

    for (size_t i = 0; i < accessors.size(); i++) {
        if (!state->add(accessor_ids[i],
                        ASTWrapper(state->context, accessors[i]),
                        state->nodes)) {
            return am_error;
        }
    }

    return am_ok;
}

static ERL_NIF_TERM update_field_nif(Z3Nif *state,
                                     int expression_id,
                                     ErlNifEnv *env,
                                     int argc,
                                     const ERL_NIF_TERM argv[]) {
    int accessor_id, record_id, value_id;

    if (enif_get_int(env, argv[0], &accessor_id) &&
        enif_get_int(env, argv[1], &record_id) &&
        enif_get_int(env, argv[2], &value_id)) {
        auto accessor = state->get(accessor_id, state->nodes),
             record = state->get(record_id, state->nodes),
             value = state->get(value_id, state->nodes);

        if (accessor && accessor->is<Z3_FUNC_DECL_AST>() && record && value) {
            auto result = Z3_datatype_update_field(state->context,
                                                   *accessor,
                                                   *record,
                                                   *value);

            if (Z3_get_error_code(state->context) == Z3_OK) {
                if (state->add(expression_id,
                               ASTWrapper(state->context, result),
                               state->nodes)) {
                    return am_ok;
                }
            }
        }
    }

    return am_error;
}

/* ************************************************************************* */

static ERL_NIF_TERM check_nif(Z3Nif *state,
                              ErlNifEnv *env,
                              int argc,
                              const ERL_NIF_TERM argv[]) {
    ASTVector assumptions;

    if (unwrap_list(state, state->nodes, env, argv[0], assumptions)) {
        auto result = Z3_solver_check_assumptions(
                state->context,
                state->solver,
                assumptions.size(),
                assumptions.handles<Z3_ast>().data());

        if (Z3_get_error_code(state->context) == Z3_OK) {
            switch (result) {
            case Z3_L_FALSE:
                return am_unsat;
            case Z3_L_TRUE:
                return am_sat;
            case Z3_L_UNDEF:
                return am_unknown;
            }
        }
    }

    return am_error;
}

static ERL_NIF_TERM push_nif(Z3Nif *state,
                             ErlNifEnv *env,
                             int argc,
                             const ERL_NIF_TERM argv[]) {
    Z3_solver_push(state->context, state->solver);

    if (Z3_get_error_code(state->context) == Z3_OK) {
        return am_ok;
    }

    return am_error;
}

static ERL_NIF_TERM pop_nif(Z3Nif *state,
                            ErlNifEnv *env,
                            int argc,
                            const ERL_NIF_TERM argv[]) {
    int count, from_id;

    if (enif_get_int(env, argv[0], &count) && count > 0 &&
        enif_get_int(env, argv[1], &from_id) && from_id > 0) {
        Z3_solver_pop(state->context, state->solver, count);

        if (Z3_get_error_code(state->context) == Z3_OK) {
            /* Remove our references to all declarations and expressions made
             * between the current state and the frame we just popped. */
            auto symbol_start = state->symbols.lower_bound(from_id);
            if (symbol_start != state->symbols.end()) {
                state->symbols.erase(symbol_start, state->symbols.end());
            }

            auto node_start = state->nodes.lower_bound(from_id);
            if (node_start != state->nodes.end()) {
                state->nodes.erase(node_start, state->nodes.end());
            }

            auto constructor_start = state->constructors.lower_bound(from_id);
            if (constructor_start != state->constructors.end()) {
                state->constructors.erase(constructor_start,
                                          state->constructors.end());
            }

            return am_ok;
        }
    }

    return am_error;
}

static ERL_NIF_TERM assert_nif(Z3Nif *state,
                               ErlNifEnv *env,
                               int argc,
                               const ERL_NIF_TERM argv[]) {
    int expr_id;

    if (enif_get_int(env, argv[0], &expr_id)) {
        if (auto expr = state->get(expr_id, state->nodes)) {
            Z3_solver_assert(state->context, state->solver, *expr);

            if (Z3_get_error_code(state->context) == Z3_OK) {
                return am_ok;
            }
        }
    }

    return am_error;
}

/* "Context NIF wrapper," handles the common part of all NIFs that accept a
 * Z3 context. */
typedef ERL_NIF_TERM(ContextNif)(Z3Nif *state,
                                 ErlNifEnv *env,
                                 int argc,
                                 const ERL_NIF_TERM argv[]);
template<ContextNif Func>
static ERL_NIF_TERM context_nif_wrapper(ErlNifEnv *env,
                                        int argc,
                                        const ERL_NIF_TERM argv[]) {
    Z3Nif *state;

    if (enif_get_resource(env, argv[0], resource_type, (void **)&state)) {
        bool current = false;

        if (state->in_use.compare_exchange_strong(current, true)) {
            ERL_NIF_TERM result;

            if (!state->closed) {
                result = Func(state, env, argc - 1, &argv[1]);
            } else {
                result = enif_raise_exception(env, am_badarg);
            }

            state->fence++;
            state->in_use.store(false);

            return result;
        }
    }

    return enif_raise_exception(env, am_badarg);
}

/* "Identifier NIF wrapper," as context NIF wrapper but also accepts another
 * integer identifier for tagging expressions and the like. */
typedef ERL_NIF_TERM(IdentifierNif)(Z3Nif *state,
                                    int expression_id,
                                    ErlNifEnv *env,
                                    int argc,
                                    const ERL_NIF_TERM argv[]);
template<IdentifierNif Func>
static ERL_NIF_TERM identifier_nif_wrapper(Z3Nif *state,
                                           ErlNifEnv *env,
                                           int argc,
                                           const ERL_NIF_TERM argv[]) {
    int expression_id;

    if (enif_get_int(env, argv[0], &expression_id)) {
        return Func(state, expression_id, env, argc - 1, &argv[1]);
    }

    return enif_raise_exception(env, am_badarg);
}

static ERL_NIF_TERM fence_nif(ErlNifEnv *env,
                              int argc,
                              const ERL_NIF_TERM argv[]) {
    ERL_NIF_TERM error;
    Z3Nif *state;

    if (enif_get_resource(env, argv[0], resource_type, (void **)&state)) {
        bool current = false;

        if (state->in_use.compare_exchange_strong(current, true)) {
            auto result = enif_make_uint(env, state->fence);
            state->in_use.store(false);

            return result;
        } else {
            error = enif_make_atom(env, "concurrent_access");
        }
    } else {
        error = enif_make_tuple(env,
                                2,
                                enif_make_atom(env, "inclosed_context"),
                                argv[0]);
    }

    return enif_raise_exception(env, error);
}

/* NIF interface declarations */
extern "C"
{
    static ErlNifFunc nif_funcs[] = {
            {"new", 1, new_nif, 0},

            {"close", 1, context_nif_wrapper<close_nif>, 0},

            {"fence", 1, fence_nif, 0},

            {"symbol",
             3,
             context_nif_wrapper<identifier_nif_wrapper<symbol_nif>>,
             0},

            {"simplify",
             3,
             context_nif_wrapper<
                     identifier_nif_wrapper<unary_nif<Z3_simplify>>>,
             0},

            /* Functions */
            {"application",
             4,
             context_nif_wrapper<identifier_nif_wrapper<application_nif>>,
             0},
            {"constant",
             4,
             context_nif_wrapper<identifier_nif_wrapper<constant_nif>>,
             0},
            {"define_interpreted_function",
             4,
             context_nif_wrapper<define_function_nif>,
             0},
            {"declare_interpreted_function",
             5,
             context_nif_wrapper<identifier_nif_wrapper<
                     function_declaration_nif<Z3_mk_rec_func_decl>>>,
             0},
            {"uninterpreted_function",
             5,
             context_nif_wrapper<identifier_nif_wrapper<
                     function_declaration_nif<Z3_mk_func_decl>>>,
             0},
            {"linear_order",
             4,
             context_nif_wrapper<identifier_nif_wrapper<linear_order_nif>>,
             0},

            /* Datatypes */
            {"constructor",
             5,
             context_nif_wrapper<identifier_nif_wrapper<constructor_nif>>,
             0},
            {"datatype",
             4,
             context_nif_wrapper<identifier_nif_wrapper<datatype_nif>>,
             0},
            {"datatype_sort",
             3,
             context_nif_wrapper<identifier_nif_wrapper<datatype_sort_nif>>,
             0},
            {"query_constructor",
             5,
             context_nif_wrapper<query_constructor_nif>,
             0},
            {"update_field",
             5,
             context_nif_wrapper<identifier_nif_wrapper<update_field_nif>>,
             0},

            /* Complex built-in types */
            {"array_sort",
             4,
             context_nif_wrapper<identifier_nif_wrapper<array_sort_nif>>,
             0},
            {"array_select",
             4,
             context_nif_wrapper<identifier_nif_wrapper<array_select_nif>>,
             0},
            {"array_store",
             5,
             context_nif_wrapper<identifier_nif_wrapper<array_store_nif>>,
             0},

            {"sequence_sort",
             3,
             context_nif_wrapper<identifier_nif_wrapper<sequence_sort_nif>>,
             0},
            {"sequence_concat",
             3,
             context_nif_wrapper<identifier_nif_wrapper<
                     unary_vararg_nif<Z3_mk_seq_concat>>>,
             0},
            {"sequence_empty",
             3,
             context_nif_wrapper<identifier_nif_wrapper<sequence_empty_nif>>,
             0},
            {"sequence_unit",
             3,
             context_nif_wrapper<
                     identifier_nif_wrapper<unary_nif<Z3_mk_seq_unit>>>,
             0},
            {"sequence_length",
             3,
             context_nif_wrapper<
                     identifier_nif_wrapper<unary_nif<Z3_mk_seq_length>>>,
             0},
            {"string_lt",
             4,
             context_nif_wrapper<
                     identifier_nif_wrapper<binary_nif<Z3_mk_str_lt>>>,
             0},
            {"string_le",
             4,
             context_nif_wrapper<
                     identifier_nif_wrapper<binary_nif<Z3_mk_str_le>>>,
             0},

            /* Sorts */
            {"boolean_sort",
             2,
             context_nif_wrapper<identifier_nif_wrapper<
                     primitive_sort_nif<Z3_mk_bool_sort>>>,
             0},
            {"integer_sort",
             2,
             context_nif_wrapper<identifier_nif_wrapper<
                     primitive_sort_nif<Z3_mk_int_sort>>>,
             0},
            {"real_sort",
             2,
             context_nif_wrapper<identifier_nif_wrapper<
                     primitive_sort_nif<Z3_mk_real_sort>>>,
             0},
            {"string_sort",
             2,
             context_nif_wrapper<identifier_nif_wrapper<
                     primitive_sort_nif<Z3_mk_string_sort>>>,
             0},
            {"uninterpreted_sort",
             3,
             context_nif_wrapper<
                     identifier_nif_wrapper<uninterpreted_sort_nif>>,
             0},

            /* Constant expressions */
            {"make_boolean",
             3,
             context_nif_wrapper<identifier_nif_wrapper<make_boolean_nif>>,
             0},
            {"make_integer",
             4,
             context_nif_wrapper<identifier_nif_wrapper<make_integer_nif>>,
             0},
            {"make_real",
             4,
             context_nif_wrapper<identifier_nif_wrapper<make_real_nif>>,
             0},
            {"make_string",
             3,
             context_nif_wrapper<identifier_nif_wrapper<make_string_nif>>,
             0},

            /* Logical expressions */
            {"one_of",
             3,
             context_nif_wrapper<identifier_nif_wrapper<one_of_nif>>,
             0},
            {"same",
             3,
             context_nif_wrapper<identifier_nif_wrapper<same_nif>>,
             0},
            {"distinct",
             3,
             context_nif_wrapper<
                     identifier_nif_wrapper<unary_vararg_nif<Z3_mk_distinct>>>,
             0},
            {"iff",
             4,
             context_nif_wrapper<identifier_nif_wrapper<binary_nif<Z3_mk_iff>>>,
             0},
            {"implies",
             4,
             context_nif_wrapper<
                     identifier_nif_wrapper<binary_nif<Z3_mk_implies>>>,
             0},
            {"negate",
             3,
             context_nif_wrapper<identifier_nif_wrapper<unary_nif<Z3_mk_not>>>,
             0},
            {"exclusive_or",
             4,
             context_nif_wrapper<identifier_nif_wrapper<binary_nif<Z3_mk_xor>>>,
             0},
            {"conjugation",
             3,
             context_nif_wrapper<
                     identifier_nif_wrapper<unary_vararg_nif<Z3_mk_and>>>,
             0},
            {"disjunction",
             3,
             context_nif_wrapper<
                     identifier_nif_wrapper<unary_vararg_nif<Z3_mk_or>>>,
             0},
            {"if_then_else",
             5,
             context_nif_wrapper<identifier_nif_wrapper<if_then_else_nif>>,
             0},

            /* Arithmetic operations */
            {"numeric_addition",
             3,
             context_nif_wrapper<
                     identifier_nif_wrapper<unary_vararg_nif<Z3_mk_add>>>,
             0},
            {"numeric_subtraction",
             3,
             context_nif_wrapper<
                     identifier_nif_wrapper<unary_vararg_nif<Z3_mk_sub>>>,
             0},
            {"numeric_multiplication",
             3,
             context_nif_wrapper<
                     identifier_nif_wrapper<unary_vararg_nif<Z3_mk_mul>>>,
             0},
            {"numeric_division",
             4,
             context_nif_wrapper<identifier_nif_wrapper<binary_nif<Z3_mk_div>>>,
             0},
            {"numeric_modulus",
             4,
             context_nif_wrapper<identifier_nif_wrapper<binary_nif<Z3_mk_mod>>>,
             0},
            {"numeric_remainder",
             4,
             context_nif_wrapper<identifier_nif_wrapper<binary_nif<Z3_mk_rem>>>,
             0},
            {"numeric_power",
             4,
             context_nif_wrapper<
                     identifier_nif_wrapper<binary_nif<Z3_mk_power>>>,
             0},
            {"numeric_lt",
             4,
             context_nif_wrapper<identifier_nif_wrapper<binary_nif<Z3_mk_lt>>>,
             0},
            {"numeric_le",
             4,
             context_nif_wrapper<identifier_nif_wrapper<binary_nif<Z3_mk_le>>>,
             0},
            {"numeric_gt",
             4,
             context_nif_wrapper<identifier_nif_wrapper<binary_nif<Z3_mk_gt>>>,
             0},
            {"numeric_ge",
             4,
             context_nif_wrapper<identifier_nif_wrapper<binary_nif<Z3_mk_ge>>>,
             0},

            /* Solver operations. Most of these run on dirty schedulers as they
             * can take a terribly long time to finish.
             *
             * To make debugging a bit easier (mainly being able to connect
             * the C and Erlang stacks), we'll run them on normal schedulers in
             * debug mode. */
            {"assert", 2, context_nif_wrapper<assert_nif>, 0},
            {"check",
             2,
             context_nif_wrapper<check_nif>,
             HARD_DEBUG ? 0 : ERL_NIF_DIRTY_JOB_CPU_BOUND},
            {"push",
             1,
             context_nif_wrapper<push_nif>,
             HARD_DEBUG ? 0 : ERL_NIF_DIRTY_JOB_CPU_BOUND},
            {"pop",
             3,
             context_nif_wrapper<pop_nif>,
             HARD_DEBUG ? 0 : ERL_NIF_DIRTY_JOB_CPU_BOUND},
    };

    static int load(ErlNifEnv *env, void **priv_data, ERL_NIF_TERM load_info) {
        ErlNifResourceTypeInit callbacks = {};

        callbacks.down = NULL;
        callbacks.dtor = [](ErlNifEnv *env, void *resource) {
            reinterpret_cast<Z3Nif *>(resource)->~Z3Nif();
        };
        callbacks.stop = NULL;
        callbacks.members = 3;

        resource_type = enif_init_resource_type(env,
                                                "Z3Nif",
                                                &callbacks,
                                                ERL_NIF_RT_CREATE,
                                                NULL);

        am_ok = enif_make_atom(env, "ok");
        am_error = enif_make_atom(env, "error");
        am_badarg = enif_make_atom(env, "badarg");

        am_true = enif_make_atom(env, "true");
        am_false = enif_make_atom(env, "false");

        am_sat = enif_make_atom(env, "sat");
        am_unsat = enif_make_atom(env, "unsat");
        am_unknown = enif_make_atom(env, "unknown");

        am_conversion_needed = enif_make_atom(env, "conversion_needed");

        am_log_file = enif_make_atom(env, "log_file");
        am_recursion_limit = enif_make_atom(env, "recursion_limit");

        *priv_data = NULL;

        /* Make sure Z3 isn't too helpful. */
        Z3_toggle_warning_messages(0);

        return 0;
    }

    static int upgrade(ErlNifEnv *env,
                       void **priv_data,
                       void **old_priv_data,
                       ERL_NIF_TERM load_info) {
        if (*old_priv_data != NULL || *priv_data != NULL) {
            return -1; /* Upgrades aren't supported. */
        }

        if (load(env, priv_data, load_info)) {
            return -1;
        }

        return 0;
    }

    static void unload(ErlNifEnv *env, void *priv_data) {
        (void)env;
        (void)priv_data;
    }

    ERL_NIF_INIT(z3_nif, nif_funcs, load, NULL, upgrade, unload)
}
