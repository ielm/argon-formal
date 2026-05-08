// Lean compiler output
// Module: ArgonFormal.Locality.Seminaive
// Imports: public import Init public import ArgonFormal.Schema.Signature public import ArgonFormal.Schema.Ontology public import ArgonFormal.Schema.WorldAssumption public import Mathlib.Data.Finset.Basic public import Mathlib.Data.Fintype.Prod
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
LEAN_EXPORT uint8_t lp_argon_x2dformal_instDecidableEqModAtom_decEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_instDecidableEqModAtom_decEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_argon_x2dformal_instDecidableEqModAtom_decEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_instDecidableEqModAtom_decEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_argon_x2dformal_instDecidableEqModAtom___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_instDecidableEqModAtom___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_argon_x2dformal_instDecidableEqModAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_instDecidableEqModAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_instFintypeModAtom___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_instFintypeModAtom___redArg___lam__1(lean_object*);
static const lean_closure_object lp_argon_x2dformal_instFintypeModAtom___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_argon_x2dformal_instFintypeModAtom___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_argon_x2dformal_instFintypeModAtom___redArg___closed__0 = (const lean_object*)&lp_argon_x2dformal_instFintypeModAtom___redArg___closed__0_value;
static const lean_closure_object lp_argon_x2dformal_instFintypeModAtom___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_argon_x2dformal_instFintypeModAtom___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_argon_x2dformal_instFintypeModAtom___redArg___closed__1 = (const lean_object*)&lp_argon_x2dformal_instFintypeModAtom___redArg___closed__1_value;
static const lean_ctor_object lp_argon_x2dformal_instFintypeModAtom___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_argon_x2dformal_instFintypeModAtom___redArg___closed__0_value),((lean_object*)&lp_argon_x2dformal_instFintypeModAtom___redArg___closed__1_value)}};
static const lean_object* lp_argon_x2dformal_instFintypeModAtom___redArg___closed__2 = (const lean_object*)&lp_argon_x2dformal_instFintypeModAtom___redArg___closed__2_value;
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Fintype_ofEquiv___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_instFintypeModAtom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_instFintypeModAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_instFintypeModAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_argon_x2dformal_instDecidableEqModAtom_decEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = lean_apply_2(x_1, x_5, x_7);
x_10 = lean_unbox(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_2);
x_11 = lean_unbox(x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_apply_2(x_2, x_6, x_8);
x_13 = lean_unbox(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_instDecidableEqModAtom_decEq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_argon_x2dformal_instDecidableEqModAtom_decEq___redArg(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lp_argon_x2dformal_instDecidableEqModAtom_decEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lp_argon_x2dformal_instDecidableEqModAtom_decEq___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_instDecidableEqModAtom_decEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lp_argon_x2dformal_instDecidableEqModAtom_decEq(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t lp_argon_x2dformal_instDecidableEqModAtom___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lp_argon_x2dformal_instDecidableEqModAtom_decEq___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_instDecidableEqModAtom___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_argon_x2dformal_instDecidableEqModAtom___redArg(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lp_argon_x2dformal_instDecidableEqModAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lp_argon_x2dformal_instDecidableEqModAtom_decEq___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_instDecidableEqModAtom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lp_argon_x2dformal_instDecidableEqModAtom(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_instFintypeModAtom___redArg___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_instFintypeModAtom___redArg___lam__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_instFintypeModAtom___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lp_mathlib_Multiset_product___redArg(x_1, x_2);
x_4 = ((lean_object*)(lp_argon_x2dformal_instFintypeModAtom___redArg___closed__2));
x_5 = lp_mathlib_Fintype_ofEquiv___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_instFintypeModAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_argon_x2dformal_instFintypeModAtom___redArg(x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_instFintypeModAtom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_argon_x2dformal_instFintypeModAtom(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_argon_x2dformal_ArgonFormal_Schema_Signature(uint8_t builtin);
lean_object* initialize_argon_x2dformal_ArgonFormal_Schema_Ontology(uint8_t builtin);
lean_object* initialize_argon_x2dformal_ArgonFormal_Schema_WorldAssumption(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Prod(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_argon_x2dformal_ArgonFormal_Locality_Seminaive(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_argon_x2dformal_ArgonFormal_Schema_Signature(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_argon_x2dformal_ArgonFormal_Schema_Ontology(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_argon_x2dformal_ArgonFormal_Schema_WorldAssumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
