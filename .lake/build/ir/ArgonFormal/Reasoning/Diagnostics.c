// Lean compiler output
// Module: ArgonFormal.Reasoning.Diagnostics
// Imports: public import Init public import ArgonFormal.Reasoning.Fixpoint
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
lean_object* lp_argon_x2dformal_instDecidableEqDiagnostic___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_ndunion___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_evaluateConstraints___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_evaluateConstraints___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_evaluateConstraints(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_evaluateConstraints___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_evaluateConstraints___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(lp_argon_x2dformal_instDecidableEqDiagnostic___boxed), 2, 0);
x_5 = lean_apply_1(x_3, x_1);
x_6 = lp_mathlib_Multiset_ndunion___redArg(x_4, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_evaluateConstraints___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(lp_argon_x2dformal_evaluateConstraints___redArg___lam__0), 3, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_box(0);
x_5 = l_List_foldl___redArg(x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_evaluateConstraints(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lp_argon_x2dformal_evaluateConstraints___redArg(x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_evaluateConstraints___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lp_argon_x2dformal_evaluateConstraints(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_argon_x2dformal_ArgonFormal_Reasoning_Fixpoint(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_argon_x2dformal_ArgonFormal_Reasoning_Diagnostics(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_argon_x2dformal_ArgonFormal_Reasoning_Fixpoint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
