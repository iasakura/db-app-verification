#include <lean/lean.h>
#include <libpq-fe.h>

// Attribution:
// Adapted from https://github.com/aripiprazole/pgsql (pgsql/ffi.cpp),
// then modified for this project's API/runtime and dynamic libpq loading.

#include <dlfcn.h>
#include <cstdlib>
#include <cstring>

typedef struct {
  PGresult *res;
} result_t;

static lean_external_class *g_dbapp_pg_conn_class = nullptr;
static lean_external_class *g_dbapp_pg_result_class = nullptr;

static void *g_libpq = nullptr;
static const char *g_libpq_error = nullptr;

static PGconn *(*p_PQconnectdb)(const char *) = nullptr;
static ConnStatusType (*p_PQstatus)(const PGconn *) = nullptr;
static char *(*p_PQerrorMessage)(const PGconn *) = nullptr;
static void (*p_PQfinish)(PGconn *) = nullptr;
static PGresult *(*p_PQexecParams)(
    PGconn *, const char *, int, const Oid *, const char *const *, const int *, const int *, int) = nullptr;
static ExecStatusType (*p_PQresultStatus)(const PGresult *) = nullptr;
static void (*p_PQclear)(PGresult *) = nullptr;
static char *(*p_PQresultErrorMessage)(const PGresult *) = nullptr;
static int (*p_PQntuples)(const PGresult *) = nullptr;
static int (*p_PQnfields)(const PGresult *) = nullptr;
static char *(*p_PQfname)(const PGresult *, int) = nullptr;
static int (*p_PQgetisnull)(const PGresult *, int, int) = nullptr;
static char *(*p_PQgetvalue)(const PGresult *, int, int) = nullptr;

inline static void noop_foreach(void *mod, b_lean_obj_arg fn) {}

static bool load_symbol(void **out, const char *name) {
  *out = dlsym(g_libpq, name);
  if (*out == nullptr) {
    g_libpq_error = name;
    return false;
  }
  return true;
}

static bool ensure_libpq_loaded() {
  if (g_libpq != nullptr) {
    return true;
  }

  g_libpq = dlopen("libpq.so.5", RTLD_NOW | RTLD_LOCAL);
  if (g_libpq == nullptr) {
    g_libpq = dlopen("libpq.so", RTLD_NOW | RTLD_LOCAL);
  }
  if (g_libpq == nullptr) {
    g_libpq_error = "dlopen(libpq)";
    return false;
  }

  if (!load_symbol((void **)&p_PQconnectdb, "PQconnectdb")) return false;
  if (!load_symbol((void **)&p_PQstatus, "PQstatus")) return false;
  if (!load_symbol((void **)&p_PQerrorMessage, "PQerrorMessage")) return false;
  if (!load_symbol((void **)&p_PQfinish, "PQfinish")) return false;
  if (!load_symbol((void **)&p_PQexecParams, "PQexecParams")) return false;
  if (!load_symbol((void **)&p_PQresultStatus, "PQresultStatus")) return false;
  if (!load_symbol((void **)&p_PQclear, "PQclear")) return false;
  if (!load_symbol((void **)&p_PQresultErrorMessage, "PQresultErrorMessage")) return false;
  if (!load_symbol((void **)&p_PQntuples, "PQntuples")) return false;
  if (!load_symbol((void **)&p_PQnfields, "PQnfields")) return false;
  if (!load_symbol((void **)&p_PQfname, "PQfname")) return false;
  if (!load_symbol((void **)&p_PQgetisnull, "PQgetisnull")) return false;
  if (!load_symbol((void **)&p_PQgetvalue, "PQgetvalue")) return false;

  return true;
}

inline static void connection_finalize(void *conn_ptr) {
  if (conn_ptr != nullptr && p_PQfinish != nullptr) {
    p_PQfinish((PGconn *)conn_ptr);
  }
}

inline static void result_finalize(void *result_ptr) {
  if (result_ptr != nullptr) {
    auto obj = (result_t *)result_ptr;
    if (obj->res != nullptr && p_PQclear != nullptr) {
      p_PQclear(obj->res);
    }
    free(obj);
  }
}

static lean_obj_res mk_some(lean_obj_res v) {
  lean_object *option = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(option, 0, v);
  return option;
}

static lean_obj_res mk_none() {
  return lean_alloc_ctor(0, 0, 0);
}

static lean_obj_res mk_conn(PGconn *conn) {
  return lean_alloc_external(g_dbapp_pg_conn_class, conn);
}

static PGconn *unbox_conn(lean_obj_res conn) {
  return (PGconn *)lean_get_external_data(conn);
}

static lean_obj_res mk_result(result_t *result) {
  return lean_alloc_external(g_dbapp_pg_result_class, result);
}

static result_t *unbox_result(lean_obj_res result) {
  return (result_t *)lean_get_external_data(result);
}

extern "C" lean_obj_res lean_dbapp_pg_initialize() {
  g_dbapp_pg_conn_class = lean_register_external_class(connection_finalize, noop_foreach);
  g_dbapp_pg_result_class = lean_register_external_class(result_finalize, noop_foreach);
  ensure_libpq_loaded();
  return lean_io_result_mk_ok(lean_box(0));
}

extern "C" lean_obj_res lean_dbapp_pg_connect(b_lean_obj_arg conninfo) {
  if (!ensure_libpq_loaded()) {
    lean_object *errCtor = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(errCtor, 0, lean_mk_string(g_libpq_error != nullptr ? g_libpq_error : "libpq load failure"));
    return lean_io_result_mk_ok(errCtor);
  }

  const char *options = lean_string_cstr(conninfo);
  PGconn *conn = p_PQconnectdb(options);

  if (p_PQstatus(conn) != CONNECTION_OK) {
    auto err = p_PQerrorMessage(conn);
    auto str = lean_mk_string(err != nullptr ? err : "postgres connection failed");
    p_PQfinish(conn);
    lean_object *errCtor = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(errCtor, 0, str);
    return lean_io_result_mk_ok(errCtor);
  }

  lean_object *okCtor = lean_alloc_ctor(0, 1, 0);
  lean_ctor_set(okCtor, 0, mk_conn(conn));
  return lean_io_result_mk_ok(okCtor);
}

extern "C" lean_obj_res lean_dbapp_pg_exec(
    b_lean_obj_arg conn,
    b_lean_obj_arg sql,
    b_lean_obj_arg params) {
  if (!ensure_libpq_loaded()) {
    lean_object *errCtor = lean_alloc_ctor(2, 1, 0);
    lean_ctor_set(errCtor, 0, lean_mk_string(g_libpq_error != nullptr ? g_libpq_error : "libpq load failure"));
    return lean_io_result_mk_ok(errCtor);
  }

  PGconn *connection = unbox_conn(conn);
  const char *command = lean_string_cstr(sql);
  auto arr = lean_to_array(params);

  const char **values = (const char **)malloc(sizeof(const char *) * arr->m_size);
  int *lengths = (int *)malloc(sizeof(int) * arr->m_size);
  int *formats = (int *)malloc(sizeof(int) * arr->m_size);

  for (size_t i = 0; i < arr->m_size; i++) {
    auto p = arr->m_data[i];
    auto s = lean_string_cstr(p);
    values[i] = s;
    lengths[i] = (int)strlen(s);
    formats[i] = 0;
  }

  PGresult *res = p_PQexecParams(
      connection,
      command,
      (int)arr->m_size,
      NULL,
      values,
      lengths,
      formats,
      0);

  free(values);
  free(lengths);
  free(formats);

  auto status = p_PQresultStatus(res);

  if (status == PGRES_COMMAND_OK) {
    p_PQclear(res);
    lean_object *okCtor = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(okCtor);
  }

  if (status == PGRES_TUPLES_OK) {
    auto cursor = (result_t *)malloc(sizeof(result_t));
    cursor->res = res;

    lean_object *tuplesCtor = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(tuplesCtor, 0, mk_result(cursor));
    return lean_io_result_mk_ok(tuplesCtor);
  }

  auto err = p_PQresultErrorMessage(res);
  auto msg = lean_mk_string(err != nullptr ? err : "postgres query failed");
  p_PQclear(res);

  lean_object *errCtor = lean_alloc_ctor(2, 1, 0);
  lean_ctor_set(errCtor, 0, msg);
  return lean_io_result_mk_ok(errCtor);
}

extern "C" size_t lean_dbapp_pg_result_rows(b_lean_obj_arg result) {
  auto obj = unbox_result(result);
  return (size_t)p_PQntuples(obj->res);
}

extern "C" size_t lean_dbapp_pg_result_cols(b_lean_obj_arg result) {
  auto obj = unbox_result(result);
  return (size_t)p_PQnfields(obj->res);
}

extern "C" lean_obj_res lean_dbapp_pg_result_col_name(b_lean_obj_arg result, size_t col) {
  auto obj = unbox_result(result);
  return lean_mk_string(p_PQfname(obj->res, (int)col));
}

extern "C" lean_obj_res lean_dbapp_pg_result_value(b_lean_obj_arg result, size_t row, size_t col) {
  auto obj = unbox_result(result);

  if (p_PQgetisnull(obj->res, (int)row, (int)col)) {
    return mk_none();
  }

  const char *value = p_PQgetvalue(obj->res, (int)row, (int)col);
  return mk_some(lean_mk_string(value != nullptr ? value : ""));
}
