// Lean compiler output
// Module: ArgonFormal.TypeSystem.NarrowPred
// Imports: public import Init public import ArgonFormal.Foundation.MetaValue public import ArgonFormal.Reasoning.State public import ArgonFormal.Reasoning.Stratification
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
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_isIs_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_isIs_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_isNot_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_isNot_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_isDetermined_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_isDetermined_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_ctorIdx___redArg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_ctorIdx___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_argon_x2dformal_NarrowPred_ctorIdx___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_argon_x2dformal_NarrowPred_ctorIdx___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_argon_x2dformal_NarrowPred_ctorIdx(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_argon_x2dformal_NarrowPred_ctorElim___redArg(x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_argon_x2dformal_NarrowPred_ctorElim(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_isIs_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_argon_x2dformal_NarrowPred_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_isIs_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_argon_x2dformal_NarrowPred_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_isNot_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_argon_x2dformal_NarrowPred_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_isNot_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_argon_x2dformal_NarrowPred_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_isDetermined_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_argon_x2dformal_NarrowPred_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_NarrowPred_isDetermined_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_argon_x2dformal_NarrowPred_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_argon_x2dformal_ArgonFormal_Foundation_MetaValue(uint8_t builtin);
lean_object* initialize_argon_x2dformal_ArgonFormal_Reasoning_State(uint8_t builtin);
lean_object* initialize_argon_x2dformal_ArgonFormal_Reasoning_Stratification(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_argon_x2dformal_ArgonFormal_TypeSystem_NarrowPred(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_argon_x2dformal_ArgonFormal_Foundation_MetaValue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_argon_x2dformal_ArgonFormal_Reasoning_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_argon_x2dformal_ArgonFormal_Reasoning_Stratification(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
