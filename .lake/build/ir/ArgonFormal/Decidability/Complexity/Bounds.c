// Lean compiler output
// Module: ArgonFormal.Decidability.Complexity.Bounds
// Imports: public import Init public import ArgonFormal.Decidability.Domain1.Decidability public import ArgonFormal.Decidability.Domain2.Decidability public import ArgonFormal.Decidability.CrossDomain.Decidability
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
LEAN_EXPORT lean_object* lp_argon_x2dformal_d1QuantifierDepth___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_d1QuantifierDepth___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_d1QuantifierDepth(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_d1QuantifierDepth___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_ptime_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_ptime_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_ptime_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_ptime_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_np_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_np_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_np_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_np_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_exptime2_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_exptime2_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_exptime2_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_exptime2_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_argon_x2dformal_instReprComplexityClass_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "ComplexityClass.ptime"};
static const lean_object* lp_argon_x2dformal_instReprComplexityClass_repr___closed__0 = (const lean_object*)&lp_argon_x2dformal_instReprComplexityClass_repr___closed__0_value;
static const lean_ctor_object lp_argon_x2dformal_instReprComplexityClass_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_argon_x2dformal_instReprComplexityClass_repr___closed__0_value)}};
static const lean_object* lp_argon_x2dformal_instReprComplexityClass_repr___closed__1 = (const lean_object*)&lp_argon_x2dformal_instReprComplexityClass_repr___closed__1_value;
static const lean_string_object lp_argon_x2dformal_instReprComplexityClass_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ComplexityClass.np"};
static const lean_object* lp_argon_x2dformal_instReprComplexityClass_repr___closed__2 = (const lean_object*)&lp_argon_x2dformal_instReprComplexityClass_repr___closed__2_value;
static const lean_ctor_object lp_argon_x2dformal_instReprComplexityClass_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_argon_x2dformal_instReprComplexityClass_repr___closed__2_value)}};
static const lean_object* lp_argon_x2dformal_instReprComplexityClass_repr___closed__3 = (const lean_object*)&lp_argon_x2dformal_instReprComplexityClass_repr___closed__3_value;
static const lean_string_object lp_argon_x2dformal_instReprComplexityClass_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "ComplexityClass.exptime2"};
static const lean_object* lp_argon_x2dformal_instReprComplexityClass_repr___closed__4 = (const lean_object*)&lp_argon_x2dformal_instReprComplexityClass_repr___closed__4_value;
static const lean_ctor_object lp_argon_x2dformal_instReprComplexityClass_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_argon_x2dformal_instReprComplexityClass_repr___closed__4_value)}};
static const lean_object* lp_argon_x2dformal_instReprComplexityClass_repr___closed__5 = (const lean_object*)&lp_argon_x2dformal_instReprComplexityClass_repr___closed__5_value;
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t lp_argon_x2dformal_instReprComplexityClass_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_argon_x2dformal_instReprComplexityClass_repr___closed__6;
static lean_once_cell_t lp_argon_x2dformal_instReprComplexityClass_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_argon_x2dformal_instReprComplexityClass_repr___closed__7;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_instReprComplexityClass_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_instReprComplexityClass_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_argon_x2dformal_instReprComplexityClass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_argon_x2dformal_instReprComplexityClass_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_argon_x2dformal_instReprComplexityClass___closed__0 = (const lean_object*)&lp_argon_x2dformal_instReprComplexityClass___closed__0_value;
LEAN_EXPORT const lean_object* lp_argon_x2dformal_instReprComplexityClass = (const lean_object*)&lp_argon_x2dformal_instReprComplexityClass___closed__0_value;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_argon_x2dformal_ComplexityClass_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_ofNat___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_argon_x2dformal_instDecidableEqComplexityClass(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_argon_x2dformal_instDecidableEqComplexityClass___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_argon_x2dformal_d1QuantifierDepth___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_7; lean_object* x_12; lean_object* x_13; 
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_1, 1);
x_2 = x_18;
goto block_6;
}
case 3:
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_1, 1);
x_2 = x_19;
goto block_6;
}
case 4:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lp_argon_x2dformal_d1QuantifierDepth___redArg(x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_21, x_22);
lean_dec(x_21);
return x_23;
}
case 5:
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_1, 0);
x_7 = x_24;
goto block_11;
}
case 6:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_1, 0);
x_7 = x_25;
goto block_11;
}
case 7:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
x_12 = x_26;
x_13 = x_27;
goto block_17;
}
case 8:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
x_12 = x_28;
x_13 = x_29;
goto block_17;
}
case 9:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_1, 0);
x_1 = x_30;
goto _start;
}
case 10:
{
lean_object* x_32; 
x_32 = lean_unsigned_to_nat(0u);
return x_32;
}
case 11:
{
lean_object* x_33; 
x_33 = lean_unsigned_to_nat(0u);
return x_33;
}
default: 
{
lean_object* x_34; 
x_34 = lean_unsigned_to_nat(0u);
return x_34;
}
}
block_6:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lp_argon_x2dformal_d1QuantifierDepth___redArg(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
return x_5;
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lp_argon_x2dformal_d1QuantifierDepth___redArg(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_8);
return x_10;
}
block_17:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lp_argon_x2dformal_d1QuantifierDepth___redArg(x_12);
x_15 = lp_argon_x2dformal_d1QuantifierDepth___redArg(x_13);
x_16 = lean_nat_dec_le(x_14, x_15);
if (x_16 == 0)
{
lean_dec(x_15);
return x_14;
}
else
{
lean_dec(x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_d1QuantifierDepth___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_argon_x2dformal_d1QuantifierDepth___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_d1QuantifierDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_argon_x2dformal_d1QuantifierDepth___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_d1QuantifierDepth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_argon_x2dformal_d1QuantifierDepth(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
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
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = lp_argon_x2dformal_ComplexityClass_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_argon_x2dformal_ComplexityClass_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = lp_argon_x2dformal_ComplexityClass_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_argon_x2dformal_ComplexityClass_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = lp_argon_x2dformal_ComplexityClass_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_ptime_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_ptime_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_argon_x2dformal_ComplexityClass_ptime_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_ptime_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_ptime_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = lp_argon_x2dformal_ComplexityClass_ptime_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_np_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_np_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_argon_x2dformal_ComplexityClass_np_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_np_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_np_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = lp_argon_x2dformal_ComplexityClass_np_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_exptime2_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_exptime2_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_argon_x2dformal_ComplexityClass_exptime2_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_exptime2_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_exptime2_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = lp_argon_x2dformal_ComplexityClass_exptime2_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_lp_argon_x2dformal_instReprComplexityClass_repr___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_lp_argon_x2dformal_instReprComplexityClass_repr___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_instReprComplexityClass_repr(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_10; lean_object* x_17; 
switch (x_1) {
case 0:
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_unsigned_to_nat(1024u);
x_25 = lean_nat_dec_le(x_24, x_2);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_obj_once(&lp_argon_x2dformal_instReprComplexityClass_repr___closed__6, &lp_argon_x2dformal_instReprComplexityClass_repr___closed__6_once, _init_lp_argon_x2dformal_instReprComplexityClass_repr___closed__6);
x_3 = x_26;
goto block_9;
}
else
{
lean_object* x_27; 
x_27 = lean_obj_once(&lp_argon_x2dformal_instReprComplexityClass_repr___closed__7, &lp_argon_x2dformal_instReprComplexityClass_repr___closed__7_once, _init_lp_argon_x2dformal_instReprComplexityClass_repr___closed__7);
x_3 = x_27;
goto block_9;
}
}
case 1:
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_unsigned_to_nat(1024u);
x_29 = lean_nat_dec_le(x_28, x_2);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_obj_once(&lp_argon_x2dformal_instReprComplexityClass_repr___closed__6, &lp_argon_x2dformal_instReprComplexityClass_repr___closed__6_once, _init_lp_argon_x2dformal_instReprComplexityClass_repr___closed__6);
x_10 = x_30;
goto block_16;
}
else
{
lean_object* x_31; 
x_31 = lean_obj_once(&lp_argon_x2dformal_instReprComplexityClass_repr___closed__7, &lp_argon_x2dformal_instReprComplexityClass_repr___closed__7_once, _init_lp_argon_x2dformal_instReprComplexityClass_repr___closed__7);
x_10 = x_31;
goto block_16;
}
}
default: 
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_unsigned_to_nat(1024u);
x_33 = lean_nat_dec_le(x_32, x_2);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_obj_once(&lp_argon_x2dformal_instReprComplexityClass_repr___closed__6, &lp_argon_x2dformal_instReprComplexityClass_repr___closed__6_once, _init_lp_argon_x2dformal_instReprComplexityClass_repr___closed__6);
x_17 = x_34;
goto block_23;
}
else
{
lean_object* x_35; 
x_35 = lean_obj_once(&lp_argon_x2dformal_instReprComplexityClass_repr___closed__7, &lp_argon_x2dformal_instReprComplexityClass_repr___closed__7_once, _init_lp_argon_x2dformal_instReprComplexityClass_repr___closed__7);
x_17 = x_35;
goto block_23;
}
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = ((lean_object*)(lp_argon_x2dformal_instReprComplexityClass_repr___closed__1));
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = 0;
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
block_16:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = ((lean_object*)(lp_argon_x2dformal_instReprComplexityClass_repr___closed__3));
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 0;
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = l_Repr_addAppParen(x_14, x_2);
return x_15;
}
block_23:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = ((lean_object*)(lp_argon_x2dformal_instReprComplexityClass_repr___closed__5));
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = 0;
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = l_Repr_addAppParen(x_21, x_2);
return x_22;
}
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_instReprComplexityClass_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = lp_argon_x2dformal_instReprComplexityClass_repr(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t lp_argon_x2dformal_ComplexityClass_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_le(x_1, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 2;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_ComplexityClass_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_argon_x2dformal_ComplexityClass_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_argon_x2dformal_instDecidableEqComplexityClass(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lp_argon_x2dformal_ComplexityClass_ctorIdx(x_1);
x_4 = lp_argon_x2dformal_ComplexityClass_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_argon_x2dformal_instDecidableEqComplexityClass___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lp_argon_x2dformal_instDecidableEqComplexityClass(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_argon_x2dformal_ArgonFormal_Decidability_Domain1_Decidability(uint8_t builtin);
lean_object* initialize_argon_x2dformal_ArgonFormal_Decidability_Domain2_Decidability(uint8_t builtin);
lean_object* initialize_argon_x2dformal_ArgonFormal_Decidability_CrossDomain_Decidability(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_argon_x2dformal_ArgonFormal_Decidability_Complexity_Bounds(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_argon_x2dformal_ArgonFormal_Decidability_Domain1_Decidability(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_argon_x2dformal_ArgonFormal_Decidability_Domain2_Decidability(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_argon_x2dformal_ArgonFormal_Decidability_CrossDomain_Decidability(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
