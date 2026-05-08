// Lean compiler output
// Module: ArgonFormal.Decidability.Domain1.TC
// Imports: public import Init public import Mathlib.Logic.Relation public import Mathlib.Data.Fintype.Basic public import Mathlib.Data.Fintype.Card public import Mathlib.Data.Finset.Basic public import Mathlib.Data.Finset.Card public import Mathlib.Data.Finset.Union
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
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_stepReachable___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_biUnion___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_ndunion___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_stepReachable___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_stepReachable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_iterReachable___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_iterReachable___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_iterReachable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_iterReachable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_reachableFrom___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_reachableFrom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_iterReachable_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_iterReachable_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_iterReachable_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_iterReachable_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Multiset_decidableMem___aux__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_argon_x2dformal_ArgonDecidability_transGenDecidable___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_ArgonDecidability_transGenDecidable___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_argon_x2dformal_ArgonDecidability_transGenDecidable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_ArgonDecidability_transGenDecidable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_stepReachable___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lp_mathlib_Multiset_filter___redArg(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_stepReachable___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_stepReachable___redArg___lam__0), 3, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_1);
lean_inc(x_4);
lean_inc_ref(x_2);
x_6 = lp_mathlib_Finset_biUnion___redArg(x_2, x_4, x_5);
x_7 = lp_mathlib_Multiset_ndunion___redArg(x_2, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_stepReachable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_stepReachable___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_iterReachable___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 1)
{
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_5, x_8);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_10 = lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_iterReachable___redArg(x_1, x_2, x_3, x_4, x_9);
lean_dec(x_9);
x_11 = lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_stepReachable___redArg(x_1, x_2, x_3, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_iterReachable___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_iterReachable___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_iterReachable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_iterReachable___redArg(x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_iterReachable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_iterReachable(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_reachableFrom___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_3);
x_5 = lean_apply_1(x_3, x_4);
lean_inc(x_1);
x_6 = lp_mathlib_Multiset_filter___redArg(x_5, x_1);
x_7 = l_List_lengthTR___redArg(x_1);
x_8 = lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_iterReachable___redArg(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_reachableFrom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_reachableFrom___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_iterReachable_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_iterReachable_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_iterReachable_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_iterReachable_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 1)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_2, x_9);
x_11 = lean_apply_1(x_4, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_iterReachable_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_iterReachable_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_argon_x2dformal_ArgonDecidability_transGenDecidable___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
lean_inc_ref(x_2);
x_6 = lp_argon_x2dformal___private_ArgonFormal_Decidability_Domain1_TC_0__ArgonDecidability_reachableFrom___redArg(x_1, x_2, x_3, x_4);
x_7 = lp_mathlib_Multiset_decidableMem___aux__1___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_ArgonDecidability_transGenDecidable___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lp_argon_x2dformal_ArgonDecidability_transGenDecidable___redArg(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t lp_argon_x2dformal_ArgonDecidability_transGenDecidable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lp_argon_x2dformal_ArgonDecidability_transGenDecidable___redArg(x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_ArgonDecidability_transGenDecidable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lp_argon_x2dformal_ArgonDecidability_transGenDecidable(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Logic_Relation(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Card(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Card(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Union(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_argon_x2dformal_ArgonFormal_Decidability_Domain1_TC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Logic_Relation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Card(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Card(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Union(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
