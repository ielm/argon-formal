// Lean compiler output
// Module: ArgonFormal.TypeSystem.Soundness.Defeasibility
// Imports: public import Init public import ArgonFormal.TypeSystem.NarrowEnv
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
LEAN_EXPORT uint8_t lp_argon_x2dformal_applyOverride___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_applyOverride___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_argon_x2dformal_applyOverride(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_applyOverride___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_TypeSystem_Soundness_Defeasibility_0__NarrowPred_holds_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_TypeSystem_Soundness_Defeasibility_0__NarrowPred_holds_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_TypeSystem_Soundness_Defeasibility_0__NarrowPred_holds_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_argon_x2dformal_applyOverride___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
lean_inc(x_7);
x_9 = lean_apply_2(x_1, x_7, x_4);
x_10 = lean_unbox(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_5);
lean_dec_ref(x_2);
x_11 = lean_apply_2(x_3, x_7, x_8);
x_12 = lean_unbox(x_11);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
lean_inc(x_8);
x_13 = lean_apply_2(x_2, x_8, x_5);
x_14 = lean_unbox(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_apply_2(x_3, x_7, x_8);
x_16 = lean_unbox(x_15);
return x_16;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_applyOverride___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_6);
x_10 = lp_argon_x2dformal_applyOverride___redArg(x_1, x_2, x_3, x_4, x_5, x_9, x_7, x_8);
x_11 = lean_box(x_10);
return x_11;
}
}
LEAN_EXPORT uint8_t lp_argon_x2dformal_applyOverride(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lp_argon_x2dformal_applyOverride___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_applyOverride___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_8);
x_12 = lp_argon_x2dformal_applyOverride(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_9, x_10);
x_13 = lean_box(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_TypeSystem_Soundness_Defeasibility_0__NarrowPred_holds_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_3(x_3, x_6, x_7, x_2);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_apply_3(x_4, x_9, x_10, x_2);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec_ref(x_1);
x_14 = lean_apply_3(x_5, x_12, x_13, x_2);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_TypeSystem_Soundness_Defeasibility_0__NarrowPred_holds_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec_ref(x_6);
x_13 = lean_apply_3(x_8, x_11, x_12, x_7);
return x_13;
}
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_8);
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_dec_ref(x_6);
x_16 = lean_apply_3(x_9, x_14, x_15, x_7);
return x_16;
}
default: 
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_8);
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_dec_ref(x_6);
x_19 = lean_apply_3(x_10, x_17, x_18, x_7);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_TypeSystem_Soundness_Defeasibility_0__NarrowPred_holds_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lp_argon_x2dformal___private_ArgonFormal_TypeSystem_Soundness_Defeasibility_0__NarrowPred_holds_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_argon_x2dformal_ArgonFormal_TypeSystem_NarrowEnv(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_argon_x2dformal_ArgonFormal_TypeSystem_Soundness_Defeasibility(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_argon_x2dformal_ArgonFormal_TypeSystem_NarrowEnv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
