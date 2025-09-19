// Lean compiler output
// Module: UEM.Model
// Imports: Init UEM.Structure
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l_UEM_ProjectionModel_specReference___default___closed__1;
LEAN_EXPORT lean_object* l_UEM_ProjectionModel_specReference___default;
static lean_object* _init_l_UEM_ProjectionModel_specReference___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Spec Example 6.1", 16);
return x_1;
}
}
static lean_object* _init_l_UEM_ProjectionModel_specReference___default() {
_start:
{
lean_object* x_1; 
x_1 = l_UEM_ProjectionModel_specReference___default___closed__1;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_UEM_Structure(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_UEM_Model(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UEM_Structure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_UEM_ProjectionModel_specReference___default___closed__1 = _init_l_UEM_ProjectionModel_specReference___default___closed__1();
lean_mark_persistent(l_UEM_ProjectionModel_specReference___default___closed__1);
l_UEM_ProjectionModel_specReference___default = _init_l_UEM_ProjectionModel_specReference___default();
lean_mark_persistent(l_UEM_ProjectionModel_specReference___default);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
