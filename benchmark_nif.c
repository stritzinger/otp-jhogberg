#include "./erts/emulator/beam/erl_nif.h"


typedef struct {
    ErlNifIOQueue *queue;
    ErlNifMutex *mutex;
} buffer_data_t;

static ErlNifResourceType *rtype_buffer;

static void gc_resource(ErlNifEnv *env, void* data) {
    buffer_data_t *buffer = (buffer_data_t*)data;
    enif_ioq_destroy(buffer->queue);
    enif_mutex_destroy(buffer->mutex);
}

static ERL_NIF_TERM am_ok;
static ERL_NIF_TERM am_error;

static int load(ErlNifEnv *env, void** priv_data, ERL_NIF_TERM load_info) {
    rtype_buffer = enif_open_resource_type(env, NULL, "benchmark_resource", gc_resource,
        ERL_NIF_RT_CREATE, NULL);

    am_ok = enif_make_atom(env, "ok");
    am_error = enif_make_atom(env, "error");

    *priv_data = NULL;

    return 0;
}

static void unload(ErlNifEnv *env, void* priv_data) {

}

static int upgrade(ErlNifEnv *env, void** priv_data, void** old_priv_data, ERL_NIF_TERM load_info) {
    if(*old_priv_data != NULL) {
        return -1; /* Don't know how to do that */
    }

    if(*priv_data != NULL) {
        return -1; /* Don't know how to do that */
    }

    if(load(env, priv_data, load_info)) {
        return -1;
    }

    return 0;
}

static int get_buffer_data(ErlNifEnv *env, ERL_NIF_TERM opaque, buffer_data_t **buffer) {
    return enif_get_resource(env, opaque, rtype_buffer, (void **)buffer);
}

static ERL_NIF_TERM new_nif(ErlNifEnv *env, int argc, const ERL_NIF_TERM argv[]) {
    buffer_data_t *buffer;
    ERL_NIF_TERM result;

    buffer = (buffer_data_t*)enif_alloc_resource(rtype_buffer, sizeof(buffer_data_t));
    buffer->queue = enif_ioq_create(ERL_NIF_IOQ_NORMAL);
    buffer->mutex = enif_mutex_create("benchmark_nif");

    result = enif_make_resource(env, buffer);
    enif_release_resource(buffer);

    return result;
}

static ERL_NIF_TERM write_nif(ErlNifEnv *env, int argc, const ERL_NIF_TERM argv[]) {
    buffer_data_t *buffer;

    ErlNifIOVec vec, *iovec = &vec;
    ERL_NIF_TERM tail;
    size_t total_size;

    if(!get_buffer_data(env, argv[0], &buffer)
       || !enif_inspect_iovec(env, 64, argv[1], &tail, &iovec)) {
        return enif_make_badarg(env);
    }

    enif_mutex_lock(buffer->mutex);
    enif_ioq_enqv(buffer->queue, iovec, 0);
    total_size = enif_ioq_size(buffer->queue);
    enif_mutex_unlock(buffer->mutex);

    return enif_make_uint64(env, total_size);
}

static ERL_NIF_TERM empty_nif(ErlNifEnv *env, int argc, const ERL_NIF_TERM argv[]) {
    buffer_data_t *buffer;
    size_t total_size;

    if(!get_buffer_data(env, argv[0], &buffer)) {
        return enif_make_badarg(env);
    }

    enif_mutex_lock(buffer->mutex);
    total_size = enif_ioq_size(buffer->queue);
    enif_ioq_deq(buffer->queue, total_size, NULL);
    enif_mutex_unlock(buffer->mutex);

    return enif_make_uint64(env, total_size);
}

static ErlNifFunc nif_funcs[] = {
    {"new_nif", 0, new_nif},
    {"write_nif", 2, write_nif},
    {"empty_nif", 1, empty_nif},
};

ERL_NIF_INIT(benchmark, nif_funcs, load, NULL, upgrade, unload)

