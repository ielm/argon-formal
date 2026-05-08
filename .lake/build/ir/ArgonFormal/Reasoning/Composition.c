// Lean compiler output
// Module: ArgonFormal.Reasoning.Composition
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
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_Package_combine___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_Package_combine___redArg___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_ndunion___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_Package_combine___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_Package_combine(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_Package_combine___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_Package_combine___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_3);
x_6 = l_List_appendTR___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_Package_combine___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_3);
x_6 = l_List_appendTR___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_Package_combine___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_6);
lean_dec_ref(x_2);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 2);
x_11 = lean_alloc_closure((void*)(lp_argon_x2dformal_Package_combine___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_5);
lean_closure_set(x_11, 1, x_9);
x_12 = lean_alloc_closure((void*)(lp_argon_x2dformal_Package_combine___redArg___lam__1), 3, 2);
lean_closure_set(x_12, 0, x_6);
lean_closure_set(x_12, 1, x_10);
x_13 = lp_mathlib_Multiset_ndunion___redArg(x_1, x_4, x_8);
lean_ctor_set(x_3, 2, x_12);
lean_ctor_set(x_3, 1, x_11);
lean_ctor_set(x_3, 0, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_17 = lean_alloc_closure((void*)(lp_argon_x2dformal_Package_combine___redArg___lam__0), 3, 2);
lean_closure_set(x_17, 0, x_5);
lean_closure_set(x_17, 1, x_15);
x_18 = lean_alloc_closure((void*)(lp_argon_x2dformal_Package_combine___redArg___lam__1), 3, 2);
lean_closure_set(x_18, 0, x_6);
lean_closure_set(x_18, 1, x_16);
x_19 = lp_mathlib_Multiset_ndunion___redArg(x_1, x_4, x_14);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_Package_combine(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lp_argon_x2dformal_Package_combine___redArg(x_4, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_Package_combine___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lp_argon_x2dformal_Package_combine(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
return x_9;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_argon_x2dformal_ArgonFormal_Reasoning_Fixpoint(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_argon_x2dformal_ArgonFormal_Reasoning_Composition(uint8_t builtin) {
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
