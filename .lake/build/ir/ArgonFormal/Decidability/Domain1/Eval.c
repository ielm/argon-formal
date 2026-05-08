// Lean compiler output
// Module: ArgonFormal.Decidability.Domain1.Eval
// Imports: public import Init public import ArgonFormal.Decidability.Fragment public import Mathlib.Logic.Relation
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_argon_x2dformal_ArgonFormal_Decidability_Fragment(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Logic_Relation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_argon_x2dformal_ArgonFormal_Decidability_Domain1_Eval(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_argon_x2dformal_ArgonFormal_Decidability_Fragment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Logic_Relation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
