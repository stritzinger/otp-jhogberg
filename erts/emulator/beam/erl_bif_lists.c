/*
 * %CopyrightBegin%
 *
 * Copyright Ericsson AB 1999-2018. All Rights Reserved.
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

/*
 * BIFs logically belonging to the lists module.
 */

#ifdef HAVE_CONFIG_H
#  include "config.h"
#endif

#include "sys.h"
#include "erl_vm.h"
#include "global.h"
#include "bif.h"
#include "erl_binary.h"

static Export subtract_trap_export;

#if defined(DEBUG)
    #define IF_DEBUG(VAL_DEBUG, IGNORE) (VAL_DEBUG)
#else
    #define IF_DEBUG(IGNORE, VAL_RELEASE) (VAL_RELEASE)
#endif


static Eterm keyfind(int Bif, Process* p, Eterm Key, Eterm Pos, Eterm List);

void erts_init_bif_lists() {
    erts_init_trap_export(&subtract_trap_export, am_lists, am_subtract, 2,
                          &subtract_2);
}

static BIF_RETTYPE append(Process* p, Eterm A, Eterm B)
{
    Eterm list;
    Eterm copy;
    Eterm last;
    Eterm* hp = NULL;
    Sint i;

    list = A;

    if (is_nil(list)) {
        BIF_RET(B);
    }

    if (is_not_list(list)) {
        BIF_ERROR(p, BADARG);
    }

    /* optimistic append on heap first */

    if ((i = HeapWordsLeft(p) / 2) < 4) {
        goto list_tail;
    }

    hp   = HEAP_TOP(p);
    copy = last = CONS(hp, CAR(list_val(list)), make_list(hp+2));
    list = CDR(list_val(list));
    hp  += 2;
    i   -= 2; /* don't use the last 2 words (extra i--;) */

    while(i-- && is_list(list)) {
        Eterm* listp = list_val(list);
        last = CONS(hp, CAR(listp), make_list(hp+2));
        list = CDR(listp);
        hp += 2;
    }

    /* A is proper and B is NIL return A as-is, don't update HTOP */

    if (is_nil(list) && is_nil(B)) {
        BIF_RET(A);
    }

    if (is_nil(list)) {
        HEAP_TOP(p) = hp;
        CDR(list_val(last)) = B;
        BIF_RET(copy);
    }

list_tail:

    if ((i = erts_list_length(list)) < 0) {
        BIF_ERROR(p, BADARG);
    }

    /* remaining list was proper and B is NIL */
    if (is_nil(B)) {
        BIF_RET(A);
    }

    if (hp) {
        /* Note: fall through case, already written
         * on the heap.
         * The last 2 words of the heap is not written yet
         */
        Eterm *hp_save = hp;
        ASSERT(i != 0);
        HEAP_TOP(p) = hp + 2;
        if (i == 1) {
            hp[0] = CAR(list_val(list));
            hp[1] = B;
            BIF_RET(copy);
        }
        hp   = HAlloc(p, 2*(i - 1));
        last = CONS(hp_save, CAR(list_val(list)), make_list(hp));
    } else {
        hp   = HAlloc(p, 2*i);
        copy = last = CONS(hp, CAR(list_val(list)), make_list(hp+2));
        hp  += 2;
    }

    list = CDR(list_val(list));
    i--;

    ASSERT(i > -1);
    while(i--) {
        Eterm* listp = list_val(list);
        last = CONS(hp, CAR(listp), make_list(hp+2));
        list = CDR(listp);
        hp  += 2;
    }

    CDR(list_val(last)) = B;
    BIF_RET(copy);
}

/*
 * erlang:'++'/2
 */

Eterm
ebif_plusplus_2(BIF_ALIST_2)
{
    return append(BIF_P, BIF_ARG_1, BIF_ARG_2);
}

BIF_RETTYPE append_2(BIF_ALIST_2)
{
    return append(BIF_P, BIF_ARG_1, BIF_ARG_2);
}

/* erlang:'--'/2
 *
 * Subtracts a list from another (A -- B), removing the first occurrence of
 * each element in B from A. There is no type coercion so the elements must
 * match exactly.
 *
 * The runtime complexity is len(A) * log(len(B)), and its memory complexity
 * is len(A) + len(B).
 *
 * The algoritm is broken into four stages that can trap individually. The
 * first two determines the length of both lists, the third creates a multiset
 * from B, and the fourth builds a new list minus the elements in B.
 *
 * The multiset is implemented as a red-black tree with counters that track
 * the number of times a given value is present in the set. */

typedef enum {
    SUBTRACT_STAGE_LEN_A,     /* Calculate length of A */
    SUBTRACT_STAGE_LEN_B,     /* Calculate length of B */
    SUBTRACT_STAGE_BUILD_SET, /* Insert B into removal multiset */
    SUBTRACT_STAGE_SWEEP,     /* Scan A and copy elements not in B to result */
} ErtsSubtractCtxStage;

typedef struct __subtr_node_t {
    struct __subtr_node_t *parent;
    struct __subtr_node_t *left;
    struct __subtr_node_t *right;

    int is_red;

    Eterm key;
    Uint count;
} subms_node_t;

typedef struct {
    ErtsSubtractCtxStage stage;

    Uint rem_a;
    Uint len_b;

    Eterm iterator;
    Eterm orig_a;
    Eterm orig_b;

    Eterm *result_cdr;
    Eterm result;

    subms_node_t *removal_set;

    subms_node_t *set_alloc_start;
    subms_node_t *set_alloc;
} ErtsSubtractContext;

#define ERTS_RBT_PREFIX subms
#define ERTS_RBT_T subms_node_t
#define ERTS_RBT_KEY_T Eterm
#define ERTS_RBT_FLAGS_T int
#define ERTS_RBT_INIT_EMPTY_TNODE(T) \
    do { \
        (T)->parent = NULL; \
        (T)->left = NULL; \
        (T)->right = NULL; \
        (T)->is_red = 0; \
        (T)->count = 0; \
    } while(0)
#define ERTS_RBT_IS_RED(T) ((T)->is_red)
#define ERTS_RBT_SET_RED(T) ((T)->is_red = 1)
#define ERTS_RBT_IS_BLACK(T) (!ERTS_RBT_IS_RED(T))
#define ERTS_RBT_SET_BLACK(T) ((T)->is_red = 0)
#define ERTS_RBT_GET_FLAGS(T) ((T)->is_red)
#define ERTS_RBT_SET_FLAGS(T, F) ((T)->is_red = F)
#define ERTS_RBT_GET_PARENT(T) ((T)->parent)
#define ERTS_RBT_SET_PARENT(T, P) ((T)->parent = P)
#define ERTS_RBT_GET_RIGHT(T) ((T)->right)
#define ERTS_RBT_SET_RIGHT(T, R) ((T)->right = (R))
#define ERTS_RBT_GET_LEFT(T) ((T)->left)
#define ERTS_RBT_SET_LEFT(T, L) ((T)->left = (L))
#define ERTS_RBT_GET_KEY(T) ((T)->key)
#define ERTS_RBT_IS_LT(KX, KY) (CMP_TERM(KX, KY) < 0)
#define ERTS_RBT_IS_EQ(KX, KY) (CMP_TERM(KX, KY) == 0)
#define ERTS_RBT_WANT_DELETE
#define ERTS_RBT_WANT_INSERT
#define ERTS_RBT_WANT_LOOKUP
#define ERTS_RBT_UNDEF

#include "erl_rbtree.h"

static void subtract_ctx_dtor(ErtsSubtractContext *context) {
    if (context->set_alloc_start != NULL) {
        erts_free(ERTS_ALC_T_HEAP_FRAG, context->set_alloc_start);
    }
}

static int subtract_ctx_bin_dtor(Binary *context_bin) {
    ErtsSubtractContext *context = ERTS_MAGIC_BIN_DATA(context_bin);
    subtract_ctx_dtor(context);
    return 1;
}

/* Copies the current context into a magic binary for trapping. */
static Eterm subtract_create_trap_state(Process *p,
                                        ErtsSubtractContext *stack_context) {
    ErtsSubtractContext *copied_context;
    Binary *state_bin;
    Eterm *hp;

    state_bin = erts_create_magic_binary(sizeof(ErtsSubtractContext),
                                         subtract_ctx_bin_dtor);

    copied_context = ERTS_MAGIC_BIN_DATA(state_bin);
    *copied_context = *stack_context;

    hp = HAlloc(p, ERTS_MAGIC_REF_THING_SIZE);

    return erts_mk_magic_ref(&hp, &MSO(p), state_bin);
}

static void subtract_setup_len_a(ErtsSubtractContext *context) {
    context->stage = SUBTRACT_STAGE_LEN_A;

    context->iterator = context->orig_a;
    context->rem_a = 0;
}

static void subtract_setup_len_b(ErtsSubtractContext *context) {
    context->stage = SUBTRACT_STAGE_LEN_B;

    context->iterator = context->orig_b;
    context->len_b = 0;
}

static void subtract_setup_build_set(ErtsSubtractContext *context) {
    context->stage = SUBTRACT_STAGE_BUILD_SET;

    context->set_alloc = erts_alloc(ERTS_ALC_T_HEAP_FRAG,
                                    context->len_b * sizeof(subms_node_t));
    context->set_alloc_start = context->set_alloc;
    context->removal_set = NULL;

    context->iterator = context->orig_b;
}

static void subtract_setup_sweep(ErtsSubtractContext *context) {
    context->stage = SUBTRACT_STAGE_SWEEP;

    context->result_cdr = &context->result;
    context->result = NIL;

    context->iterator = context->orig_a;
}

static int subtract_get_length(Process *p, Eterm *iterator_p, Uint *count_p) {
    static const Sint ELEMENTS_PER_RED = 30;

    Sint count, budget;
    Eterm iterator;

    budget = ELEMENTS_PER_RED * IF_DEBUG(p->fcalls / 10 + 1, p->fcalls);
    iterator = *iterator_p;

    for (count = 0; count < budget && is_list(iterator); count++) {
        iterator = CDR(list_val(iterator));
    }

    if (!is_list(iterator) && !is_nil(iterator)) {
        return -1;
    }

    BUMP_REDS(p, count / ELEMENTS_PER_RED);

    *iterator_p = iterator;
    *count_p += count;

    if (is_nil(iterator)) {
        return 1;
    }

    return 0;
}

/* Copies elements from B into the multiset used when sweeping. */
static int subtract_build_set(Process *p, ErtsSubtractContext *context) {
    const static Sint INSERTIONS_PER_RED = 30;

    Sint budget, insertions;

    budget = INSERTIONS_PER_RED * IF_DEBUG(p->fcalls / 10 + 1, p->fcalls);
    insertions = 0;

    while (insertions < budget && is_list(context->iterator)) {
        subms_node_t *node;
        const Eterm *cell;
        Eterm key;

        cell = list_val(context->iterator);
        context->iterator = CDR(cell);
        key = CAR(cell);

        node = subms_rbt_lookup(context->removal_set, key);

        if(node == NULL) {
            node = context->set_alloc++;
            node->key = key;
            node->count = 0;

            subms_rbt_insert(&context->removal_set, node);
        }

        node->count++;
        insertions++;
    }

    BUMP_REDS(p, insertions / INSERTIONS_PER_RED);

    return is_nil(context->iterator);
}

/* Iterate over A and for each element that is present in B, skip it in A and
 * remove it from B, otherwise copy the element into the result. */
static int subtract_sweep(Process *p, ErtsSubtractContext *context) {
    const Sint CHECKS_PER_RED = 32;
    Sint checks, budget;

    budget = CHECKS_PER_RED * IF_DEBUG(p->fcalls / 10 + 1, p->fcalls);
    checks = 0;

    while (checks < budget && is_list(context->iterator)) {
        subms_node_t *node;
        const Eterm *cell;
        Eterm value, next;

        cell = list_val(context->iterator);
        value = CAR(cell);
        next = CDR(cell);

        node = subms_rbt_lookup(context->removal_set, value);

        if (node == NULL) {
            /* Destructively cons the value to the result. This is safe since
             * the GC is disabled and the term is never leaked to the outside
             * world. List termination is deferred until we return. */
            Eterm *hp = HAllocX(p, 2, context->rem_a * 2);

            *context->result_cdr = make_list(hp);
            context->result_cdr = &CDR(hp);

            CAR(hp) = value;
        } else {
            /* Skip consing the value and remove it from B. */

            if (node->count-- == 1) {
                subms_rbt_delete(&context->removal_set, node);
            }

            if (context->removal_set == NULL) {
                /* There's no more work to be done, so we set the tail to the
                 * remainder of A and return. */
                *context->result_cdr = next;

                BUMP_REDS(p, checks / CHECKS_PER_RED);

                return 1;
            }
        }

        context->iterator = next;
        context->rem_a--;
        checks++;
    }

    /* Make sure the list is terminated when trapping out. This is only
     * strictly necessary when we actually return, but debugging isn't fun with
     * holes in the heap. */
    *context->result_cdr = NIL;

    BUMP_REDS(p, checks / CHECKS_PER_RED);

    if (is_list(context->iterator)) {
        ASSERT(context->rem_a > 0 && context->removal_set != NULL);
        return 0;
    }

    return 1;
}

static int subtract_continue(Process *p, ErtsSubtractContext *context) {
    switch (context->stage) {
        case SUBTRACT_STAGE_LEN_A: {
            int res = subtract_get_length(p, &context->iterator, &context->rem_a);

            if (res != 1) {
                return res;
            }

            ASSERT(context->rem_a >= 1);

            subtract_setup_len_b(context);
            /* FALL THROUGH */
        }

        case SUBTRACT_STAGE_LEN_B: {
            int res = subtract_get_length(p, &context->iterator, &context->len_b);

            if (res != 1) {
                return res;
            }

            ASSERT(context->len_b >= 1);

            subtract_setup_build_set(context);
            /* FALL THROUGH */
        }

        case SUBTRACT_STAGE_BUILD_SET: {
            if (!subtract_build_set(p, context)) {
                return 0;
            }

            subtract_setup_sweep(context);
            /* FALL THROUGH */
        }

        case SUBTRACT_STAGE_SWEEP: {
            if (!subtract_sweep(p, context)) {
                return 0;
            }

            return 1;
        }
        default:
            ERTS_ASSERT(!"unreachable");
    }
}

/* erlang:'--'/2
 *
 * Calculates A -- B for two lists. When trapping, A is a magic reference and B
 * is NIL. */
static Eterm subtract(Process *p, Eterm *bif_args_p, Eterm A, Eterm B) {
    if (is_list(A) && is_list(B)) {
        /* This is the first call from Erlang code. A context has yet to be set
         * up, so we'll start with one on the stack in the hopes that we won't
         * have to trap. */

        ErtsSubtractContext onstack_context = {0};
        int res;

        onstack_context.orig_a = A;
        onstack_context.orig_b = B;

        subtract_setup_len_a(&onstack_context);

        res = subtract_continue(p, &onstack_context);

        if (res == 0) {
            Eterm state_mref = subtract_create_trap_state(p, &onstack_context);

            p->flags |= F_DISABLE_GC;
            BIF_TRAP2(&subtract_trap_export, p, state_mref, NIL);
        }

        subtract_ctx_dtor(&onstack_context);

        if (res < 0) {
            BIF_ERROR(p, BADARG);
        }

        BIF_RET(onstack_context.result);
    } else if (is_internal_magic_ref(A)) {
        ErtsSubtractContext *context;
        int (*dtor)(Binary*);
        Binary *magic_bin;

        int res;

        magic_bin = erts_magic_ref2bin(A);
        dtor = ERTS_MAGIC_BIN_DESTRUCTOR(magic_bin);

        if (dtor != subtract_ctx_bin_dtor) {
            BIF_ERROR(p, BADARG);
        }

        ASSERT(p->flags & F_DISABLE_GC);
        ASSERT(B == NIL);

        context = ERTS_MAGIC_BIN_DATA(magic_bin);
        res = subtract_continue(p, context);

        if (res == 0) {
            BIF_TRAP2(&subtract_trap_export, p, A, NIL);
        }

        p->flags &= ~F_DISABLE_GC;

        if (res < 0) {
            bif_args_p[0] = context->orig_a;
            bif_args_p[1] = context->orig_b;

            BIF_ERROR(p, BADARG);
        }

        BIF_RET(context->result);
    }

    /* Handle trivial cases. */
    if (is_nil(A)) {
        BIF_RET(NIL);
    } else if (is_nil(B)) {
        BIF_RET(A);
    }

    BIF_ERROR(p, BADARG);
}

BIF_RETTYPE ebif_minusminus_2(BIF_ALIST_2) {
    /* Passing also &BIF_ARG_1 to modify BIF__ARGS for nice badarg reporting */
    return subtract(BIF_P, &BIF_ARG_1, BIF_ARG_1, BIF_ARG_2);
}

BIF_RETTYPE subtract_2(BIF_ALIST_2) {
    /* Passing also &BIF_ARG_1 to modify BIF__ARGS for nice badarg reporting */
    return subtract(BIF_P, &BIF_ARG_1, BIF_ARG_1, BIF_ARG_2);
}


BIF_RETTYPE lists_member_2(BIF_ALIST_2)
{
    Eterm term;
    Eterm list;
    Eterm item;
    int non_immed_key;
    int max_iter = 10 * CONTEXT_REDS;

    if (is_nil(BIF_ARG_2)) {
	BIF_RET(am_false);
    } else if (is_not_list(BIF_ARG_2)) {
	BIF_ERROR(BIF_P, BADARG);
    }
    
    term = BIF_ARG_1;
    non_immed_key = is_not_immed(term);
    list = BIF_ARG_2;
    while (is_list(list)) {
	if (--max_iter < 0) {
	    BUMP_ALL_REDS(BIF_P);
	    BIF_TRAP2(bif_export[BIF_lists_member_2], BIF_P, term, list);
	}
	item = CAR(list_val(list));
	if ((item == term) || (non_immed_key && eq(item, term))) {
	    BIF_RET2(am_true, CONTEXT_REDS - max_iter/10);
	}
	list = CDR(list_val(list));
    }
    if (is_not_nil(list))  {
	BIF_ERROR(BIF_P, BADARG);
    }
    BIF_RET2(am_false, CONTEXT_REDS - max_iter/10);
}

static BIF_RETTYPE lists_reverse_alloc(Process *c_p,
                                       Eterm list_in,
                                       Eterm tail_in)
{
    static const Uint CELLS_PER_RED = 40;

    Eterm *heap_top, *heap_end;
    Uint cells_left, max_cells;
    Eterm list, tail;
    Eterm lookahead;

    list = list_in;
    tail = tail_in;

    cells_left = max_cells = CELLS_PER_RED * (1 + ERTS_BIF_REDS_LEFT(c_p));
    lookahead = list;

    while (cells_left != 0 && is_list(lookahead)) {
        lookahead = CDR(list_val(lookahead));
        cells_left--;
    }

    BUMP_REDS(c_p, (max_cells - cells_left) / CELLS_PER_RED);

    if (is_not_list(lookahead) && is_not_nil(lookahead)) {
        BIF_ERROR(c_p, BADARG);
    }

    heap_top = HAlloc(c_p, 2 * (max_cells - cells_left));
    heap_end = heap_top + 2 * (max_cells - cells_left);

    while (heap_top < heap_end) {
        Eterm *pair = list_val(list);

        tail = CONS(heap_top, CAR(pair), tail);
        list = CDR(pair);

        ASSERT(is_list(list) || is_nil(list));

        heap_top += 2;
    }

    if (is_nil(list)) {
        BIF_RET(tail);
    }

    ASSERT(is_list(tail) && cells_left == 0);
    BIF_TRAP2(bif_export[BIF_lists_reverse_2], c_p, list, tail);
}

static BIF_RETTYPE lists_reverse_onheap(Process *c_p,
                                        Eterm list_in,
                                        Eterm tail_in)
{
    static const Uint CELLS_PER_RED = 60;

    Eterm *heap_top, *heap_end;
    Uint cells_left, max_cells;
    Eterm list, tail;

    list = list_in;
    tail = tail_in;

    cells_left = max_cells = CELLS_PER_RED * (1 + ERTS_BIF_REDS_LEFT(c_p));

    ASSERT(HEAP_LIMIT(c_p) >= HEAP_TOP(c_p) + 2);
    heap_end = HEAP_LIMIT(c_p) - 2;
    heap_top = HEAP_TOP(c_p);

    while (heap_top < heap_end && is_list(list)) {
        Eterm *pair = list_val(list);

        tail = CONS(heap_top, CAR(pair), tail);
        list = CDR(pair);

        heap_top += 2;
    }

    cells_left -= (heap_top - heap_end) / 2;
    BUMP_REDS(c_p, (max_cells - cells_left) / CELLS_PER_RED);
    HEAP_TOP(c_p) = heap_top;

    if (is_nil(list)) {
        BIF_RET(tail);
    } else if (is_list(list)) {
        ASSERT(is_list(tail));

        if (cells_left > CELLS_PER_RED) {
            return lists_reverse_alloc(c_p, list, tail);
        }

        BUMP_ALL_REDS(c_p);
        BIF_TRAP2(bif_export[BIF_lists_reverse_2], c_p, list, tail);
    }

    BIF_ERROR(c_p, BADARG);
}

BIF_RETTYPE lists_reverse_2(BIF_ALIST_2)
{
    /* Handle legal and illegal non-lists quickly. */
    if (is_nil(BIF_ARG_1)) {
        BIF_RET(BIF_ARG_2);
    } else if (is_not_list(BIF_ARG_1)) {
        BIF_ERROR(BIF_P, BADARG);
    }

    /* We build the reversal on the unused part of the heap if possible to save
     * us the trouble of having to figure out the list size. We fall back to
     * lists_reverse_alloc when we run out of space. */
    if (HeapWordsLeft(BIF_P) > 8) {
        return lists_reverse_onheap(BIF_P, BIF_ARG_1, BIF_ARG_2);
    }

    return lists_reverse_alloc(BIF_P, BIF_ARG_1, BIF_ARG_2);
}

BIF_RETTYPE
lists_keymember_3(BIF_ALIST_3)
{
    Eterm res;

    res = keyfind(BIF_lists_keymember_3, BIF_P,
		  BIF_ARG_1, BIF_ARG_2, BIF_ARG_3);
    if (is_value(res) && is_tuple(res)) {
	return am_true;
    } else {
	return res;
    }
}

BIF_RETTYPE
lists_keysearch_3(BIF_ALIST_3)
{
    Eterm res;
    
    res = keyfind(BIF_lists_keysearch_3, BIF_P,
		  BIF_ARG_1, BIF_ARG_2, BIF_ARG_3);
    if (is_non_value(res) || is_not_tuple(res)) {
	return res;
    } else {			/* Tuple */
	Eterm* hp = HAlloc(BIF_P, 3);
	return TUPLE2(hp, am_value, res);
    }
}

BIF_RETTYPE
lists_keyfind_3(BIF_ALIST_3)
{
    return keyfind(BIF_lists_keyfind_3, BIF_P,
		   BIF_ARG_1, BIF_ARG_2, BIF_ARG_3);
}

static Eterm
keyfind(int Bif, Process* p, Eterm Key, Eterm Pos, Eterm List)
{
    int max_iter = 10 * CONTEXT_REDS;
    Sint pos;
    Eterm term;

    if (!is_small(Pos) || (pos = signed_val(Pos)) < 1) {
	BIF_ERROR(p, BADARG);
    }

    if (is_small(Key)) {
	double float_key = (double) signed_val(Key);

	while (is_list(List)) {
	    if (--max_iter < 0) {
		BUMP_ALL_REDS(p);
		BIF_TRAP3(bif_export[Bif], p, Key, Pos, List);
	    }
	    term = CAR(list_val(List));
	    List = CDR(list_val(List));
	    if (is_tuple(term)) {
		Eterm *tuple_ptr = tuple_val(term);
		if (pos <= arityval(*tuple_ptr)) {
		    Eterm element = tuple_ptr[pos];
		    if (Key == element) {
			return term;
		    } else if (is_float(element)) {
			FloatDef f;

			GET_DOUBLE(element, f);
			if (f.fd == float_key) {
			    return term;
			}
		    }
		}
	    }
	}
    } else if (is_immed(Key)) {
	while (is_list(List)) {
	    if (--max_iter < 0) {
		BUMP_ALL_REDS(p);
		BIF_TRAP3(bif_export[Bif], p, Key, Pos, List);
	    }
	    term = CAR(list_val(List));
	    List = CDR(list_val(List));
	    if (is_tuple(term)) {
		Eterm *tuple_ptr = tuple_val(term);
		if (pos <= arityval(*tuple_ptr)) {
		    Eterm element = tuple_ptr[pos];
		    if (Key == element) {
			return term;
		    }
		}
	    }
	}
    } else {
	while (is_list(List)) {
	    if (--max_iter < 0) {
		BUMP_ALL_REDS(p);
		BIF_TRAP3(bif_export[Bif], p, Key, Pos, List);
	    }
	    term = CAR(list_val(List));
	    List = CDR(list_val(List));
	    if (is_tuple(term)) {
		Eterm *tuple_ptr = tuple_val(term);
		if (pos <= arityval(*tuple_ptr)) {
		    Eterm element = tuple_ptr[pos];
		    if (CMP_EQ(Key, element)) {
			return term;
		    }
		}
	    }
	}
    }

    if (is_not_nil(List))  {
	BIF_ERROR(p, BADARG);
    }
    return am_false;
}
