// Lean compiler output
// Module: ArgonFormal.Locality.Cwa
// Imports: public import Init public import ArgonFormal.Schema.Signature public import ArgonFormal.Schema.Ontology public import ArgonFormal.Schema.WorldAssumption public import ArgonFormal.Locality.Locality
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
uint8_t lp_mathlib_Multiset_decidableMem___aux__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_sigmaDomain___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_biUnion___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_sigmaDomain___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_sigmaDomain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_sigmaDomain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_sigmaDomain___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_dec(x_8);
x_9 = lp_mathlib_Multiset_decidableMem___aux__1___redArg(x_2, x_4, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_free_object(x_1);
lean_dec(x_5);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_box(0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lp_mathlib_Multiset_decidableMem___aux__1___redArg(x_2, x_4, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_5);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
lean_object* x_17; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_17 = lean_box(0);
return x_17;
}
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_sigmaDomain___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_alloc_closure((void*)(lp_argon_x2dformal_sigmaDomain___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_1);
x_7 = lp_mathlib_Finset_biUnion___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_sigmaDomain(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lp_argon_x2dformal_sigmaDomain___redArg(x_4, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_sigmaDomain___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lp_argon_x2dformal_sigmaDomain(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_5);
return x_9;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_argon_x2dformal_ArgonFormal_Schema_Signature(uint8_t builtin);
lean_object* initialize_argon_x2dformal_ArgonFormal_Schema_Ontology(uint8_t builtin);
lean_object* initialize_argon_x2dformal_ArgonFormal_Schema_WorldAssumption(uint8_t builtin);
lean_object* initialize_argon_x2dformal_ArgonFormal_Locality_Locality(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_argon_x2dformal_ArgonFormal_Locality_Cwa(uint8_t builtin) {
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
res = initialize_argon_x2dformal_ArgonFormal_Locality_Locality(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
