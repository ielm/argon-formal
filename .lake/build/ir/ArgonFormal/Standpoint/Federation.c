// Lean compiler output
// Module: ArgonFormal.Standpoint.Federation
// Imports: public import Init public import ArgonFormal.Foundation.Projection public import ArgonFormal.Standpoint.Stratification
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
uint8_t lp_argon_x2dformal_Truth4_infoJoin(uint8_t, uint8_t);
LEAN_EXPORT uint8_t lp_argon_x2dformal_List_foldl___at___00Truth4_federate_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_List_foldl___at___00Truth4_federate_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_argon_x2dformal_Truth4_federate(lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_Truth4_federate___boxed(lean_object*);
lean_object* lp_argon_x2dformal_instDecidableEqTruth4___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_argon_x2dformal_Truth4_instDecidablePredListHasIs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_argon_x2dformal_Truth4_instDecidablePredListHasIs___closed__0;
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_argon_x2dformal_Truth4_instDecidablePredListHasIs(lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_Truth4_instDecidablePredListHasIs___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_argon_x2dformal_Truth4_instDecidablePredListHasNot(lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_Truth4_instDecidablePredListHasNot___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_argon_x2dformal_Truth4_instDecidablePredListHasBoth(lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_Truth4_instDecidablePredListHasBoth___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_argon_x2dformal_Truth4_classify(lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_Truth4_classify___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Standpoint_Federation_0__Truth4_isConsistent_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Standpoint_Federation_0__Truth4_isConsistent_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Standpoint_Federation_0__Truth4_isConsistent_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Standpoint_Federation_0__Truth4_isConsistent_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_argon_x2dformal_List_foldl___at___00Truth4_federate_spec__0(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_unbox(x_3);
x_6 = lp_argon_x2dformal_Truth4_infoJoin(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_List_foldl___at___00Truth4_federate_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lp_argon_x2dformal_List_foldl___at___00Truth4_federate_spec__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_argon_x2dformal_Truth4_federate(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = 2;
x_3 = lp_argon_x2dformal_List_foldl___at___00Truth4_federate_spec__0(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_Truth4_federate___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_argon_x2dformal_Truth4_federate(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_lp_argon_x2dformal_Truth4_instDecidablePredListHasIs___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(lp_argon_x2dformal_instDecidableEqTruth4___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t lp_argon_x2dformal_Truth4_instDecidablePredListHasIs(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_obj_once(&lp_argon_x2dformal_Truth4_instDecidablePredListHasIs___closed__0, &lp_argon_x2dformal_Truth4_instDecidablePredListHasIs___closed__0_once, _init_lp_argon_x2dformal_Truth4_instDecidablePredListHasIs___closed__0);
x_3 = 0;
x_4 = lean_box(x_3);
x_5 = l_List_elem___redArg(x_2, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_Truth4_instDecidablePredListHasIs___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_argon_x2dformal_Truth4_instDecidablePredListHasIs(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_argon_x2dformal_Truth4_instDecidablePredListHasNot(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_obj_once(&lp_argon_x2dformal_Truth4_instDecidablePredListHasIs___closed__0, &lp_argon_x2dformal_Truth4_instDecidablePredListHasIs___closed__0_once, _init_lp_argon_x2dformal_Truth4_instDecidablePredListHasIs___closed__0);
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = l_List_elem___redArg(x_2, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_Truth4_instDecidablePredListHasNot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_argon_x2dformal_Truth4_instDecidablePredListHasNot(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_argon_x2dformal_Truth4_instDecidablePredListHasBoth(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_obj_once(&lp_argon_x2dformal_Truth4_instDecidablePredListHasIs___closed__0, &lp_argon_x2dformal_Truth4_instDecidablePredListHasIs___closed__0_once, _init_lp_argon_x2dformal_Truth4_instDecidablePredListHasIs___closed__0);
x_3 = 3;
x_4 = lean_box(x_3);
x_5 = l_List_elem___redArg(x_2, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_Truth4_instDecidablePredListHasBoth___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_argon_x2dformal_Truth4_instDecidablePredListHasBoth(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_argon_x2dformal_Truth4_classify(lean_object* x_1) {
_start:
{
uint8_t x_2; 
lean_inc(x_1);
x_2 = lp_argon_x2dformal_Truth4_instDecidablePredListHasBoth(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
lean_inc(x_1);
x_3 = lp_argon_x2dformal_Truth4_instDecidablePredListHasIs(x_1);
if (x_3 == 0)
{
goto block_8;
}
else
{
uint8_t x_9; 
lean_inc(x_1);
x_9 = lp_argon_x2dformal_Truth4_instDecidablePredListHasNot(x_1);
if (x_9 == 0)
{
goto block_8;
}
else
{
uint8_t x_10; 
lean_dec(x_1);
x_10 = 3;
return x_10;
}
}
block_8:
{
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lp_argon_x2dformal_Truth4_instDecidablePredListHasNot(x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
lean_dec(x_1);
x_7 = 0;
return x_7;
}
}
}
else
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = 3;
return x_11;
}
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_Truth4_classify___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_argon_x2dformal_Truth4_classify(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Standpoint_Federation_0__Truth4_isConsistent_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 3)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_box(x_1);
x_7 = lean_apply_2(x_3, x_6, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Standpoint_Federation_0__Truth4_isConsistent_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = lp_argon_x2dformal___private_ArgonFormal_Standpoint_Federation_0__Truth4_isConsistent_match__1_splitter___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Standpoint_Federation_0__Truth4_isConsistent_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_2 == 3)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_box(x_2);
x_8 = lean_apply_2(x_4, x_7, lean_box(0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Standpoint_Federation_0__Truth4_isConsistent_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = lp_argon_x2dformal___private_ArgonFormal_Standpoint_Federation_0__Truth4_isConsistent_match__1_splitter(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_argon_x2dformal_ArgonFormal_Foundation_Projection(uint8_t builtin);
lean_object* initialize_argon_x2dformal_ArgonFormal_Standpoint_Stratification(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_argon_x2dformal_ArgonFormal_Standpoint_Federation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_argon_x2dformal_ArgonFormal_Foundation_Projection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_argon_x2dformal_ArgonFormal_Standpoint_Stratification(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
