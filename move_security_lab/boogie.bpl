
// ** Expanded prelude

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Basic theory for vectors using arrays. This version of vectors is not extensional.

datatype Vec<T> {
    Vec(v: [int]T, l: int)
}

function {:builtin "MapConst"} MapConstVec<T>(T): [int]T;
function DefaultVecElem<T>(): T;
function {:inline} DefaultVecMap<T>(): [int]T { MapConstVec(DefaultVecElem()) }

function {:inline} EmptyVec<T>(): Vec T {
    Vec(DefaultVecMap(), 0)
}

function {:inline} MakeVec1<T>(v: T): Vec T {
    Vec(DefaultVecMap()[0 := v], 1)
}

function {:inline} MakeVec2<T>(v1: T, v2: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2], 2)
}

function {:inline} MakeVec3<T>(v1: T, v2: T, v3: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3], 3)
}

function {:inline} MakeVec4<T>(v1: T, v2: T, v3: T, v4: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3][3 := v4], 4)
}

function {:inline} ExtendVec<T>(v: Vec T, elem: T): Vec T {
    (var l := v->l;
    Vec(v->v[l := elem], l + 1))
}

function {:inline} ReadVec<T>(v: Vec T, i: int): T {
    v->v[i]
}

function {:inline} LenVec<T>(v: Vec T): int {
    v->l
}

function {:inline} IsEmptyVec<T>(v: Vec T): bool {
    v->l == 0
}

function {:inline} RemoveVec<T>(v: Vec T): Vec T {
    (var l := v->l - 1;
    Vec(v->v[l := DefaultVecElem()], l))
}

function {:inline} RemoveAtVec<T>(v: Vec T, i: int): Vec T {
    (var l := v->l - 1;
    Vec(
        (lambda j: int ::
           if j >= 0 && j < l then
               if j < i then v->v[j] else v->v[j+1]
           else DefaultVecElem()),
        l))
}

function {:inline} ConcatVec<T>(v1: Vec T, v2: Vec T): Vec T {
    (var l1, m1, l2, m2 := v1->l, v1->v, v2->l, v2->v;
    Vec(
        (lambda i: int ::
          if i >= 0 && i < l1 + l2 then
            if i < l1 then m1[i] else m2[i - l1]
          else DefaultVecElem()),
        l1 + l2))
}

function {:inline} ReverseVec<T>(v: Vec T): Vec T {
    (var l := v->l;
    Vec(
        (lambda i: int :: if 0 <= i && i < l then v->v[l - i - 1] else DefaultVecElem()),
        l))
}

function {:inline} SliceVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v->v;
    Vec(
        (lambda k:int ::
          if 0 <= k && k < j - i then
            m[i + k]
          else
            DefaultVecElem()),
        (if j - i < 0 then 0 else j - i)))
}


function {:inline} UpdateVec<T>(v: Vec T, i: int, elem: T): Vec T {
    Vec(v->v[i := elem], v->l)
}

function {:inline} SwapVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v->v;
    Vec(m[i := m[j]][j := m[i]], v->l))
}

function {:inline} ContainsVec<T>(v: Vec T, e: T): bool {
    (var l := v->l;
    (exists i: int :: InRangeVec(v, i) && v->v[i] == e))
}

function IndexOfVec<T>(v: Vec T, e: T): int;
axiom {:ctor "Vec"} (forall<T> v: Vec T, e: T :: {IndexOfVec(v, e)}
    (var i := IndexOfVec(v,e);
     if (!ContainsVec(v, e)) then i == -1
     else InRangeVec(v, i) && ReadVec(v, i) == e &&
        (forall j: int :: j >= 0 && j < i ==> ReadVec(v, j) != e)));

// This function should stay non-inlined as it guards many quantifiers
// over vectors. It appears important to have this uninterpreted for
// quantifier triggering.
function InRangeVec<T>(v: Vec T, i: int): bool {
    i >= 0 && i < LenVec(v)
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Boogie model for multisets, based on Boogie arrays. This theory assumes extensional equality for element types.

datatype Multiset<T> {
    Multiset(v: [T]int, l: int)
}

function {:builtin "MapConst"} MapConstMultiset<T>(l: int): [T]int;

function {:inline} EmptyMultiset<T>(): Multiset T {
    Multiset(MapConstMultiset(0), 0)
}

function {:inline} LenMultiset<T>(s: Multiset T): int {
    s->l
}

function {:inline} ExtendMultiset<T>(s: Multiset T, v: T): Multiset T {
    (var len := s->l;
    (var cnt := s->v[v];
    Multiset(s->v[v := (cnt + 1)], len + 1)))
}

// This function returns (s1 - s2). This function assumes that s2 is a subset of s1.
function {:inline} SubtractMultiset<T>(s1: Multiset T, s2: Multiset T): Multiset T {
    (var len1 := s1->l;
    (var len2 := s2->l;
    Multiset((lambda v:T :: s1->v[v]-s2->v[v]), len1-len2)))
}

function {:inline} IsEmptyMultiset<T>(s: Multiset T): bool {
    (s->l == 0) &&
    (forall v: T :: s->v[v] == 0)
}

function {:inline} IsSubsetMultiset<T>(s1: Multiset T, s2: Multiset T): bool {
    (s1->l <= s2->l) &&
    (forall v: T :: s1->v[v] <= s2->v[v])
}

function {:inline} ContainsMultiset<T>(s: Multiset T, v: T): bool {
    s->v[v] > 0
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Theory for tables.

// v is the SMT array holding the key-value assignment. e is an array which
// independently determines whether a key is valid or not. l is the length.
//
// Note that even though the program cannot reflect over existence of a key,
// we want the specification to be able to do this, so it can express
// verification conditions like "key has been inserted".
datatype Table <K, V> {
    Table(v: [K]V, e: [K]bool, l: int)
}

// Functions for default SMT arrays. For the table values, we don't care and
// use an uninterpreted function.
function DefaultTableArray<K, V>(): [K]V;
function DefaultTableKeyExistsArray<K>(): [K]bool;
axiom DefaultTableKeyExistsArray() == (lambda i: int :: false);

function {:inline} EmptyTable<K, V>(): Table K V {
    Table(DefaultTableArray(), DefaultTableKeyExistsArray(), 0)
}

function {:inline} GetTable<K,V>(t: Table K V, k: K): V {
    // Notice we do not check whether key is in the table. The result is undetermined if it is not.
    t->v[k]
}

function {:inline} LenTable<K,V>(t: Table K V): int {
    t->l
}


function {:inline} ContainsTable<K,V>(t: Table K V, k: K): bool {
    t->e[k]
}

function {:inline} UpdateTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    Table(t->v[k := v], t->e, t->l)
}

function {:inline} AddTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    // This function has an undetermined result if the key is already in the table
    // (all specification functions have this "partial definiteness" behavior). Thus we can
    // just increment the length.
    Table(t->v[k := v], t->e[k := true], t->l + 1)
}

function {:inline} RemoveTable<K,V>(t: Table K V, k: K): Table K V {
    // Similar as above, we only need to consider the case where the key is in the table.
    Table(t->v, t->e[k := false], t->l - 1)
}

axiom {:ctor "Table"} (forall<K,V> t: Table K V :: {LenTable(t)}
    (exists k: K :: {ContainsTable(t, k)} ContainsTable(t, k)) ==> LenTable(t) >= 1
);
// TODO: we might want to encoder a stronger property that the length of table
// must be more than N given a set of N items. Currently we don't see a need here
// and the above axiom seems to be sufficient.
// Copyright © Aptos Foundation
// SPDX-License-Identifier: Apache-2.0

// ==================================================================================
// Native object::exists_at

// ==================================================================================
// Intrinsic implementation of aggregator and aggregator factory

datatype $1_aggregator_Aggregator {
    $1_aggregator_Aggregator($handle: int, $key: int, $limit: int, $val: int)
}
function {:inline} $Update'$1_aggregator_Aggregator'_handle(s: $1_aggregator_Aggregator, x: int): $1_aggregator_Aggregator {
    $1_aggregator_Aggregator(x, s->$key, s->$limit, s->$val)
}
function {:inline} $Update'$1_aggregator_Aggregator'_key(s: $1_aggregator_Aggregator, x: int): $1_aggregator_Aggregator {
    $1_aggregator_Aggregator(s->$handle, x, s->$limit, s->$val)
}
function {:inline} $Update'$1_aggregator_Aggregator'_limit(s: $1_aggregator_Aggregator, x: int): $1_aggregator_Aggregator {
    $1_aggregator_Aggregator(s->$handle, s->$key, x, s->$val)
}
function {:inline} $Update'$1_aggregator_Aggregator'_val(s: $1_aggregator_Aggregator, x: int): $1_aggregator_Aggregator {
    $1_aggregator_Aggregator(s->$handle, s->$key, s->$limit, x)
}
function $IsValid'$1_aggregator_Aggregator'(s: $1_aggregator_Aggregator): bool {
    $IsValid'address'(s->$handle)
      && $IsValid'address'(s->$key)
      && $IsValid'u128'(s->$limit)
      && $IsValid'u128'(s->$val)
}
function {:inline} $IsEqual'$1_aggregator_Aggregator'(s1: $1_aggregator_Aggregator, s2: $1_aggregator_Aggregator): bool {
    s1 == s2
}
function {:inline} $1_aggregator_spec_get_limit(s: $1_aggregator_Aggregator): int {
    s->$limit
}
function {:inline} $1_aggregator_limit(s: $1_aggregator_Aggregator): int {
    s->$limit
}
procedure {:inline 1} $1_aggregator_limit(s: $1_aggregator_Aggregator) returns (res: int) {
    res := s->$limit;
    return;
}
function {:inline} $1_aggregator_spec_get_handle(s: $1_aggregator_Aggregator): int {
    s->$handle
}
function {:inline} $1_aggregator_spec_get_key(s: $1_aggregator_Aggregator): int {
    s->$key
}
function {:inline} $1_aggregator_spec_get_val(s: $1_aggregator_Aggregator): int {
    s->$val
}

function $1_aggregator_spec_read(agg: $1_aggregator_Aggregator): int {
    $1_aggregator_spec_get_val(agg)
}

function $1_aggregator_spec_aggregator_set_val(agg: $1_aggregator_Aggregator, val: int): $1_aggregator_Aggregator {
    $Update'$1_aggregator_Aggregator'_val(agg, val)
}

function $1_aggregator_spec_aggregator_get_val(agg: $1_aggregator_Aggregator): int {
    $1_aggregator_spec_get_val(agg)
}

function $1_aggregator_factory_spec_new_aggregator(limit: int) : $1_aggregator_Aggregator;

axiom (forall limit: int :: {$1_aggregator_factory_spec_new_aggregator(limit)}
    (var agg := $1_aggregator_factory_spec_new_aggregator(limit);
     $1_aggregator_spec_get_limit(agg) == limit));

axiom (forall limit: int :: {$1_aggregator_factory_spec_new_aggregator(limit)}
     (var agg := $1_aggregator_factory_spec_new_aggregator(limit);
     $1_aggregator_spec_aggregator_get_val(agg) == 0));

// ==================================================================================
// Native for function_info

procedure $1_function_info_is_identifier(s: Vec int) returns (res: bool);



// Uninterpreted function for all types

function $Arbitrary_value_of'$42_prover_basics_Coin'(): $42_prover_basics_Coin;

function $Arbitrary_value_of'$42_prover_basics_Wallet'(): $42_prover_basics_Wallet;

function $Arbitrary_value_of'bool'(): bool;

function $Arbitrary_value_of'u256'(): int;

function $Arbitrary_value_of'u64'(): int;

function $Arbitrary_value_of'bv256'(): bv256;

function $Arbitrary_value_of'bv64'(): bv64;



// ============================================================================================
// Primitive Types

const $MAX_U8: int;
axiom $MAX_U8 == 255;
const $MAX_U16: int;
axiom $MAX_U16 == 65535;
const $MAX_U32: int;
axiom $MAX_U32 == 4294967295;
const $MAX_U64: int;
axiom $MAX_U64 == 18446744073709551615;
const $MAX_U128: int;
axiom $MAX_U128 == 340282366920938463463374607431768211455;
const $MAX_U256: int;
axiom $MAX_U256 == 115792089237316195423570985008687907853269984665640564039457584007913129639935;

// Templates for bitvector operations

function {:bvbuiltin "bvand"} $And'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvor"} $Or'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvxor"} $Xor'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvadd"} $Add'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvsub"} $Sub'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvmul"} $Mul'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvudiv"} $Div'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvurem"} $Mod'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvshl"} $Shl'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvlshr"} $Shr'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvult"} $Lt'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv8'(bv8,bv8) returns(bool);

procedure {:inline 1} $AddBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'($Add'Bv8'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv8'(src1, src2);
}

procedure {:inline 1} $AddBv8_unchecked(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Add'Bv8'(src1, src2);
}

procedure {:inline 1} $SubBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv8'(src1, src2);
}

procedure {:inline 1} $MulBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'($Mul'Bv8'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv8'(src1, src2);
}

procedure {:inline 1} $DivBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if (src2 == 0bv8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv8'(src1, src2);
}

procedure {:inline 1} $ModBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if (src2 == 0bv8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv8'(src1, src2);
}

procedure {:inline 1} $AndBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $And'Bv8'(src1,src2);
}

procedure {:inline 1} $OrBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Or'Bv8'(src1,src2);
}

procedure {:inline 1} $XorBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Xor'Bv8'(src1,src2);
}

procedure {:inline 1} $LtBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Lt'Bv8'(src1,src2);
}

procedure {:inline 1} $LeBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Le'Bv8'(src1,src2);
}

procedure {:inline 1} $GtBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Gt'Bv8'(src1,src2);
}

procedure {:inline 1} $GeBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Ge'Bv8'(src1,src2);
}

function $IsValid'bv8'(v: bv8): bool {
  $Ge'Bv8'(v,0bv8) && $Le'Bv8'(v,255bv8)
}

function {:inline} $IsEqual'bv8'(x: bv8, y: bv8): bool {
    x == y
}

procedure {:inline 1} $int2bv8(src: int) returns (dst: bv8)
{
    if (src > 255) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.8(src);
}

procedure {:inline 1} $bv2int8(src: bv8) returns (dst: int)
{
    dst := $bv2int.8(src);
}

function {:builtin "(_ int2bv 8)"} $int2bv.8(i: int) returns (bv8);
function {:builtin "bv2nat"} $bv2int.8(i: bv8) returns (int);

function {:bvbuiltin "bvand"} $And'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvor"} $Or'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvxor"} $Xor'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvadd"} $Add'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvsub"} $Sub'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvmul"} $Mul'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvudiv"} $Div'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvurem"} $Mod'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvshl"} $Shl'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvlshr"} $Shr'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvult"} $Lt'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv16'(bv16,bv16) returns(bool);

procedure {:inline 1} $AddBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'($Add'Bv16'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv16'(src1, src2);
}

procedure {:inline 1} $AddBv16_unchecked(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Add'Bv16'(src1, src2);
}

procedure {:inline 1} $SubBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv16'(src1, src2);
}

procedure {:inline 1} $MulBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'($Mul'Bv16'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv16'(src1, src2);
}

procedure {:inline 1} $DivBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if (src2 == 0bv16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv16'(src1, src2);
}

procedure {:inline 1} $ModBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if (src2 == 0bv16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv16'(src1, src2);
}

procedure {:inline 1} $AndBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $And'Bv16'(src1,src2);
}

procedure {:inline 1} $OrBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Or'Bv16'(src1,src2);
}

procedure {:inline 1} $XorBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Xor'Bv16'(src1,src2);
}

procedure {:inline 1} $LtBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Lt'Bv16'(src1,src2);
}

procedure {:inline 1} $LeBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Le'Bv16'(src1,src2);
}

procedure {:inline 1} $GtBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Gt'Bv16'(src1,src2);
}

procedure {:inline 1} $GeBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Ge'Bv16'(src1,src2);
}

function $IsValid'bv16'(v: bv16): bool {
  $Ge'Bv16'(v,0bv16) && $Le'Bv16'(v,65535bv16)
}

function {:inline} $IsEqual'bv16'(x: bv16, y: bv16): bool {
    x == y
}

procedure {:inline 1} $int2bv16(src: int) returns (dst: bv16)
{
    if (src > 65535) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.16(src);
}

procedure {:inline 1} $bv2int16(src: bv16) returns (dst: int)
{
    dst := $bv2int.16(src);
}

function {:builtin "(_ int2bv 16)"} $int2bv.16(i: int) returns (bv16);
function {:builtin "bv2nat"} $bv2int.16(i: bv16) returns (int);

function {:bvbuiltin "bvand"} $And'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvor"} $Or'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvxor"} $Xor'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvadd"} $Add'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvsub"} $Sub'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvmul"} $Mul'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvudiv"} $Div'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvurem"} $Mod'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvshl"} $Shl'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvlshr"} $Shr'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvult"} $Lt'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv32'(bv32,bv32) returns(bool);

procedure {:inline 1} $AddBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'($Add'Bv32'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv32'(src1, src2);
}

procedure {:inline 1} $AddBv32_unchecked(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Add'Bv32'(src1, src2);
}

procedure {:inline 1} $SubBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv32'(src1, src2);
}

procedure {:inline 1} $MulBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'($Mul'Bv32'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv32'(src1, src2);
}

procedure {:inline 1} $DivBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if (src2 == 0bv32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv32'(src1, src2);
}

procedure {:inline 1} $ModBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if (src2 == 0bv32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv32'(src1, src2);
}

procedure {:inline 1} $AndBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $And'Bv32'(src1,src2);
}

procedure {:inline 1} $OrBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Or'Bv32'(src1,src2);
}

procedure {:inline 1} $XorBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Xor'Bv32'(src1,src2);
}

procedure {:inline 1} $LtBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Lt'Bv32'(src1,src2);
}

procedure {:inline 1} $LeBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Le'Bv32'(src1,src2);
}

procedure {:inline 1} $GtBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Gt'Bv32'(src1,src2);
}

procedure {:inline 1} $GeBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Ge'Bv32'(src1,src2);
}

function $IsValid'bv32'(v: bv32): bool {
  $Ge'Bv32'(v,0bv32) && $Le'Bv32'(v,2147483647bv32)
}

function {:inline} $IsEqual'bv32'(x: bv32, y: bv32): bool {
    x == y
}

procedure {:inline 1} $int2bv32(src: int) returns (dst: bv32)
{
    if (src > 2147483647) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.32(src);
}

procedure {:inline 1} $bv2int32(src: bv32) returns (dst: int)
{
    dst := $bv2int.32(src);
}

function {:builtin "(_ int2bv 32)"} $int2bv.32(i: int) returns (bv32);
function {:builtin "bv2nat"} $bv2int.32(i: bv32) returns (int);

function {:bvbuiltin "bvand"} $And'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvor"} $Or'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvxor"} $Xor'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvadd"} $Add'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvsub"} $Sub'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvmul"} $Mul'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvudiv"} $Div'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvurem"} $Mod'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvshl"} $Shl'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvlshr"} $Shr'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvult"} $Lt'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv64'(bv64,bv64) returns(bool);

procedure {:inline 1} $AddBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'($Add'Bv64'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv64'(src1, src2);
}

procedure {:inline 1} $AddBv64_unchecked(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Add'Bv64'(src1, src2);
}

procedure {:inline 1} $SubBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv64'(src1, src2);
}

procedure {:inline 1} $MulBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'($Mul'Bv64'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv64'(src1, src2);
}

procedure {:inline 1} $DivBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if (src2 == 0bv64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv64'(src1, src2);
}

procedure {:inline 1} $ModBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if (src2 == 0bv64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv64'(src1, src2);
}

procedure {:inline 1} $AndBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $And'Bv64'(src1,src2);
}

procedure {:inline 1} $OrBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Or'Bv64'(src1,src2);
}

procedure {:inline 1} $XorBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Xor'Bv64'(src1,src2);
}

procedure {:inline 1} $LtBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Lt'Bv64'(src1,src2);
}

procedure {:inline 1} $LeBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Le'Bv64'(src1,src2);
}

procedure {:inline 1} $GtBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Gt'Bv64'(src1,src2);
}

procedure {:inline 1} $GeBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Ge'Bv64'(src1,src2);
}

function $IsValid'bv64'(v: bv64): bool {
  $Ge'Bv64'(v,0bv64) && $Le'Bv64'(v,18446744073709551615bv64)
}

function {:inline} $IsEqual'bv64'(x: bv64, y: bv64): bool {
    x == y
}

procedure {:inline 1} $int2bv64(src: int) returns (dst: bv64)
{
    if (src > 18446744073709551615) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.64(src);
}

procedure {:inline 1} $bv2int64(src: bv64) returns (dst: int)
{
    dst := $bv2int.64(src);
}

function {:builtin "(_ int2bv 64)"} $int2bv.64(i: int) returns (bv64);
function {:builtin "bv2nat"} $bv2int.64(i: bv64) returns (int);

function {:bvbuiltin "bvand"} $And'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvor"} $Or'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvxor"} $Xor'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvadd"} $Add'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvsub"} $Sub'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvmul"} $Mul'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvudiv"} $Div'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvurem"} $Mod'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvshl"} $Shl'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvlshr"} $Shr'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvult"} $Lt'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv128'(bv128,bv128) returns(bool);

procedure {:inline 1} $AddBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'($Add'Bv128'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv128'(src1, src2);
}

procedure {:inline 1} $AddBv128_unchecked(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Add'Bv128'(src1, src2);
}

procedure {:inline 1} $SubBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv128'(src1, src2);
}

procedure {:inline 1} $MulBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'($Mul'Bv128'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv128'(src1, src2);
}

procedure {:inline 1} $DivBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if (src2 == 0bv128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv128'(src1, src2);
}

procedure {:inline 1} $ModBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if (src2 == 0bv128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv128'(src1, src2);
}

procedure {:inline 1} $AndBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $And'Bv128'(src1,src2);
}

procedure {:inline 1} $OrBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Or'Bv128'(src1,src2);
}

procedure {:inline 1} $XorBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Xor'Bv128'(src1,src2);
}

procedure {:inline 1} $LtBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Lt'Bv128'(src1,src2);
}

procedure {:inline 1} $LeBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Le'Bv128'(src1,src2);
}

procedure {:inline 1} $GtBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Gt'Bv128'(src1,src2);
}

procedure {:inline 1} $GeBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Ge'Bv128'(src1,src2);
}

function $IsValid'bv128'(v: bv128): bool {
  $Ge'Bv128'(v,0bv128) && $Le'Bv128'(v,340282366920938463463374607431768211455bv128)
}

function {:inline} $IsEqual'bv128'(x: bv128, y: bv128): bool {
    x == y
}

procedure {:inline 1} $int2bv128(src: int) returns (dst: bv128)
{
    if (src > 340282366920938463463374607431768211455) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.128(src);
}

procedure {:inline 1} $bv2int128(src: bv128) returns (dst: int)
{
    dst := $bv2int.128(src);
}

function {:builtin "(_ int2bv 128)"} $int2bv.128(i: int) returns (bv128);
function {:builtin "bv2nat"} $bv2int.128(i: bv128) returns (int);

function {:bvbuiltin "bvand"} $And'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvor"} $Or'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvxor"} $Xor'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvadd"} $Add'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvsub"} $Sub'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvmul"} $Mul'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvudiv"} $Div'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvurem"} $Mod'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvshl"} $Shl'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvlshr"} $Shr'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvult"} $Lt'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv256'(bv256,bv256) returns(bool);

procedure {:inline 1} $AddBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'($Add'Bv256'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv256'(src1, src2);
}

procedure {:inline 1} $AddBv256_unchecked(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Add'Bv256'(src1, src2);
}

procedure {:inline 1} $SubBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv256'(src1, src2);
}

procedure {:inline 1} $MulBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'($Mul'Bv256'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv256'(src1, src2);
}

procedure {:inline 1} $DivBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if (src2 == 0bv256) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv256'(src1, src2);
}

procedure {:inline 1} $ModBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if (src2 == 0bv256) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv256'(src1, src2);
}

procedure {:inline 1} $AndBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $And'Bv256'(src1,src2);
}

procedure {:inline 1} $OrBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Or'Bv256'(src1,src2);
}

procedure {:inline 1} $XorBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Xor'Bv256'(src1,src2);
}

procedure {:inline 1} $LtBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Lt'Bv256'(src1,src2);
}

procedure {:inline 1} $LeBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Le'Bv256'(src1,src2);
}

procedure {:inline 1} $GtBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Gt'Bv256'(src1,src2);
}

procedure {:inline 1} $GeBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Ge'Bv256'(src1,src2);
}

function $IsValid'bv256'(v: bv256): bool {
  $Ge'Bv256'(v,0bv256) && $Le'Bv256'(v,115792089237316195423570985008687907853269984665640564039457584007913129639935bv256)
}

function {:inline} $IsEqual'bv256'(x: bv256, y: bv256): bool {
    x == y
}

procedure {:inline 1} $int2bv256(src: int) returns (dst: bv256)
{
    if (src > 115792089237316195423570985008687907853269984665640564039457584007913129639935) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.256(src);
}

procedure {:inline 1} $bv2int256(src: bv256) returns (dst: int)
{
    dst := $bv2int.256(src);
}

function {:builtin "(_ int2bv 256)"} $int2bv.256(i: int) returns (bv256);
function {:builtin "bv2nat"} $bv2int.256(i: bv256) returns (int);

datatype $Range {
    $Range(lb: int, ub: int)
}

function {:inline} $IsValid'bool'(v: bool): bool {
  true
}

function $IsValid'u8'(v: int): bool {
  v >= 0 && v <= $MAX_U8
}

function $IsValid'u16'(v: int): bool {
  v >= 0 && v <= $MAX_U16
}

function $IsValid'u32'(v: int): bool {
  v >= 0 && v <= $MAX_U32
}

function $IsValid'u64'(v: int): bool {
  v >= 0 && v <= $MAX_U64
}

function $IsValid'u128'(v: int): bool {
  v >= 0 && v <= $MAX_U128
}

function $IsValid'u256'(v: int): bool {
  v >= 0 && v <= $MAX_U256
}

function $IsValid'num'(v: int): bool {
  true
}

function $IsValid'address'(v: int): bool {
  // TODO: restrict max to representable addresses?
  v >= 0
}

function {:inline} $IsValidRange(r: $Range): bool {
   $IsValid'u64'(r->lb) &&  $IsValid'u64'(r->ub)
}

// Intentionally not inlined so it serves as a trigger in quantifiers.
function $InRange(r: $Range, i: int): bool {
   r->lb <= i && i < r->ub
}


function {:inline} $IsEqual'u8'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u16'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u32'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u64'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u128'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u256'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'num'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'address'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'bool'(x: bool, y: bool): bool {
    x == y
}

// ============================================================================================
// Memory

datatype $Location {
    // A global resource location within the statically known resource type's memory,
    // where `a` is an address.
    $Global(a: int),
    // A local location. `i` is the unique index of the local.
    $Local(i: int),
    // The location of a reference outside of the verification scope, for example, a `&mut` parameter
    // of the function being verified. References with these locations don't need to be written back
    // when mutation ends.
    $Param(i: int),
    // The location of an uninitialized mutation. Using this to make sure that the location
    // will not be equal to any valid mutation locations, i.e., $Local, $Global, or $Param.
    $Uninitialized()
}

// A mutable reference which also carries its current value. Since mutable references
// are single threaded in Move, we can keep them together and treat them as a value
// during mutation until the point they are stored back to their original location.
datatype $Mutation<T> {
    $Mutation(l: $Location, p: Vec int, v: T)
}

// Representation of memory for a given type.
datatype $Memory<T> {
    $Memory(domain: [int]bool, contents: [int]T)
}

function {:builtin "MapConst"} $ConstMemoryDomain(v: bool): [int]bool;
function {:builtin "MapConst"} $ConstMemoryContent<T>(v: T): [int]T;
axiom $ConstMemoryDomain(false) == (lambda i: int :: false);
axiom $ConstMemoryDomain(true) == (lambda i: int :: true);


// Dereferences a mutation.
function {:inline} $Dereference<T>(ref: $Mutation T): T {
    ref->v
}

// Update the value of a mutation.
function {:inline} $UpdateMutation<T>(m: $Mutation T, v: T): $Mutation T {
    $Mutation(m->l, m->p, v)
}

function {:inline} $ChildMutation<T1, T2>(m: $Mutation T1, offset: int, v: T2): $Mutation T2 {
    $Mutation(m->l, ExtendVec(m->p, offset), v)
}

// Return true if two mutations share the location and path
function {:inline} $IsSameMutation<T1, T2>(parent: $Mutation T1, child: $Mutation T2 ): bool {
    parent->l == child->l && parent->p == child->p
}

// Return true if the mutation is a parent of a child which was derived with the given edge offset. This
// is used to implement write-back choices.
function {:inline} $IsParentMutation<T1, T2>(parent: $Mutation T1, edge: int, child: $Mutation T2 ): bool {
    parent->l == child->l &&
    (var pp := parent->p;
    (var cp := child->p;
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
     cl == pl + 1 &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) ==  ReadVec(cp, i)) &&
     $EdgeMatches(ReadVec(cp, pl), edge)
    ))))
}

// Return true if the mutation is a parent of a child, for hyper edge.
function {:inline} $IsParentMutationHyper<T1, T2>(parent: $Mutation T1, hyper_edge: Vec int, child: $Mutation T2 ): bool {
    parent->l == child->l &&
    (var pp := parent->p;
    (var cp := child->p;
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
    (var el := LenVec(hyper_edge);
     cl == pl + el &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) == ReadVec(cp, i)) &&
     (forall i: int:: i >= 0 && i < el ==> $EdgeMatches(ReadVec(cp, pl + i), ReadVec(hyper_edge, i)))
    )))))
}

function {:inline} $EdgeMatches(edge: int, edge_pattern: int): bool {
    edge_pattern == -1 // wildcard
    || edge_pattern == edge
}



function {:inline} $SameLocation<T1, T2>(m1: $Mutation T1, m2: $Mutation T2): bool {
    m1->l == m2->l
}

function {:inline} $HasGlobalLocation<T>(m: $Mutation T): bool {
    (m->l) is $Global
}

function {:inline} $HasLocalLocation<T>(m: $Mutation T, idx: int): bool {
    m->l == $Local(idx)
}

function {:inline} $GlobalLocationAddress<T>(m: $Mutation T): int {
    (m->l)->a
}



// Tests whether resource exists.
function {:inline} $ResourceExists<T>(m: $Memory T, addr: int): bool {
    m->domain[addr]
}

// Obtains Value of given resource.
function {:inline} $ResourceValue<T>(m: $Memory T, addr: int): T {
    m->contents[addr]
}

// Update resource.
function {:inline} $ResourceUpdate<T>(m: $Memory T, a: int, v: T): $Memory T {
    $Memory(m->domain[a := true], m->contents[a := v])
}

// Remove resource.
function {:inline} $ResourceRemove<T>(m: $Memory T, a: int): $Memory T {
    $Memory(m->domain[a := false], m->contents)
}

// Copies resource from memory s to m.
function {:inline} $ResourceCopy<T>(m: $Memory T, s: $Memory T, a: int): $Memory T {
    $Memory(m->domain[a := s->domain[a]],
            m->contents[a := s->contents[a]])
}



// ============================================================================================
// Abort Handling

var $abort_flag: bool;
var $abort_code: int;

function {:inline} $process_abort_code(code: int): int {
    code
}

const $EXEC_FAILURE_CODE: int;
axiom $EXEC_FAILURE_CODE == -1;

// TODO(wrwg): currently we map aborts of native functions like those for vectors also to
//   execution failure. This may need to be aligned with what the runtime actually does.

procedure {:inline 1} $ExecFailureAbort() {
    $abort_flag := true;
    $abort_code := $EXEC_FAILURE_CODE;
}

procedure {:inline 1} $Abort(code: int) {
    $abort_flag := true;
    $abort_code := code;
}

function {:inline} $StdError(cat: int, reason: int): int {
    reason * 256 + cat
}

procedure {:inline 1} $InitVerification() {
    // Set abort_flag to false, and havoc abort_code
    $abort_flag := false;
    havoc $abort_code;
    // Initialize event store
    call $InitEventStore();
}

// ============================================================================================
// Instructions


procedure {:inline 1} $CastU8(src: int) returns (dst: int)
{
    if (src > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU16(src: int) returns (dst: int)
{
    if (src > $MAX_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU32(src: int) returns (dst: int)
{
    if (src > $MAX_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU64(src: int) returns (dst: int)
{
    if (src > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU128(src: int) returns (dst: int)
{
    if (src > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU256(src: int) returns (dst: int)
{
    if (src > $MAX_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU16(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU16_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU32(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU32_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU256(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU256_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $Sub(src1: int, src2: int) returns (dst: int)
{
    if (src1 < src2) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

// uninterpreted function to return an undefined value.
function $undefined_int(): int;

// Recursive exponentiation function
// Undefined unless e >=0.  $pow(0,0) is also undefined.
function $pow(n: int, e: int): int {
    if n != 0 && e == 0 then 1
    else if e > 0 then n * $pow(n, e - 1)
    else $undefined_int()
}

function $shl(src1: int, p: int): int {
    src1 * $pow(2, p)
}

function $shlU8(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 256
}

function $shlU16(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 65536
}

function $shlU32(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 4294967296
}

function $shlU64(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 18446744073709551616
}

function $shlU128(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 340282366920938463463374607431768211456
}

function $shlU256(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 115792089237316195423570985008687907853269984665640564039457584007913129639936
}

function $shr(src1: int, p: int): int {
    src1 div $pow(2, p)
}

// We need to know the size of the destination in order to drop bits
// that have been shifted left more than that, so we have $ShlU8/16/32/64/128/256
procedure {:inline 1} $ShlU8(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU8(src1, src2);
}

// Template for cast and shift operations of bitvector types

procedure {:inline 1} $CastBv8to8(src: bv8) returns (dst: bv8)
{
    dst := src;
}


function $shlBv8From8(src1: bv8, src2: bv8) returns (bv8)
{
    $Shl'Bv8'(src1, src2)
}

procedure {:inline 1} $ShlBv8From8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Ge'Bv8'(src2, 8bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2);
}

function $shrBv8From8(src1: bv8, src2: bv8) returns (bv8)
{
    $Shr'Bv8'(src1, src2)
}

procedure {:inline 1} $ShrBv8From8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Ge'Bv8'(src2, 8bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2);
}

procedure {:inline 1} $CastBv16to8(src: bv16) returns (dst: bv8)
{
    if ($Gt'Bv16'(src, 255bv16)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From16(src1: bv8, src2: bv16) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From16(src1: bv8, src2: bv16) returns (dst: bv8)
{
    if ($Ge'Bv16'(src2, 8bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From16(src1: bv8, src2: bv16) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From16(src1: bv8, src2: bv16) returns (dst: bv8)
{
    if ($Ge'Bv16'(src2, 8bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv32to8(src: bv32) returns (dst: bv8)
{
    if ($Gt'Bv32'(src, 255bv32)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From32(src1: bv8, src2: bv32) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From32(src1: bv8, src2: bv32) returns (dst: bv8)
{
    if ($Ge'Bv32'(src2, 8bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From32(src1: bv8, src2: bv32) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From32(src1: bv8, src2: bv32) returns (dst: bv8)
{
    if ($Ge'Bv32'(src2, 8bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv64to8(src: bv64) returns (dst: bv8)
{
    if ($Gt'Bv64'(src, 255bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From64(src1: bv8, src2: bv64) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From64(src1: bv8, src2: bv64) returns (dst: bv8)
{
    if ($Ge'Bv64'(src2, 8bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From64(src1: bv8, src2: bv64) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From64(src1: bv8, src2: bv64) returns (dst: bv8)
{
    if ($Ge'Bv64'(src2, 8bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv128to8(src: bv128) returns (dst: bv8)
{
    if ($Gt'Bv128'(src, 255bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From128(src1: bv8, src2: bv128) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From128(src1: bv8, src2: bv128) returns (dst: bv8)
{
    if ($Ge'Bv128'(src2, 8bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From128(src1: bv8, src2: bv128) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From128(src1: bv8, src2: bv128) returns (dst: bv8)
{
    if ($Ge'Bv128'(src2, 8bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv256to8(src: bv256) returns (dst: bv8)
{
    if ($Gt'Bv256'(src, 255bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From256(src1: bv8, src2: bv256) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From256(src1: bv8, src2: bv256) returns (dst: bv8)
{
    if ($Ge'Bv256'(src2, 8bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From256(src1: bv8, src2: bv256) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From256(src1: bv8, src2: bv256) returns (dst: bv8)
{
    if ($Ge'Bv256'(src2, 8bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv8to16(src: bv8) returns (dst: bv16)
{
    dst := 0bv8 ++ src;
}


function $shlBv16From8(src1: bv16, src2: bv8) returns (bv16)
{
    $Shl'Bv16'(src1, 0bv8 ++ src2)
}

procedure {:inline 1} $ShlBv16From8(src1: bv16, src2: bv8) returns (dst: bv16)
{
    if ($Ge'Bv8'(src2, 16bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, 0bv8 ++ src2);
}

function $shrBv16From8(src1: bv16, src2: bv8) returns (bv16)
{
    $Shr'Bv16'(src1, 0bv8 ++ src2)
}

procedure {:inline 1} $ShrBv16From8(src1: bv16, src2: bv8) returns (dst: bv16)
{
    if ($Ge'Bv8'(src2, 16bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, 0bv8 ++ src2);
}

procedure {:inline 1} $CastBv16to16(src: bv16) returns (dst: bv16)
{
    dst := src;
}


function $shlBv16From16(src1: bv16, src2: bv16) returns (bv16)
{
    $Shl'Bv16'(src1, src2)
}

procedure {:inline 1} $ShlBv16From16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Ge'Bv16'(src2, 16bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2);
}

function $shrBv16From16(src1: bv16, src2: bv16) returns (bv16)
{
    $Shr'Bv16'(src1, src2)
}

procedure {:inline 1} $ShrBv16From16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Ge'Bv16'(src2, 16bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2);
}

procedure {:inline 1} $CastBv32to16(src: bv32) returns (dst: bv16)
{
    if ($Gt'Bv32'(src, 65535bv32)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From32(src1: bv16, src2: bv32) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From32(src1: bv16, src2: bv32) returns (dst: bv16)
{
    if ($Ge'Bv32'(src2, 16bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From32(src1: bv16, src2: bv32) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From32(src1: bv16, src2: bv32) returns (dst: bv16)
{
    if ($Ge'Bv32'(src2, 16bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv64to16(src: bv64) returns (dst: bv16)
{
    if ($Gt'Bv64'(src, 65535bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From64(src1: bv16, src2: bv64) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From64(src1: bv16, src2: bv64) returns (dst: bv16)
{
    if ($Ge'Bv64'(src2, 16bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From64(src1: bv16, src2: bv64) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From64(src1: bv16, src2: bv64) returns (dst: bv16)
{
    if ($Ge'Bv64'(src2, 16bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv128to16(src: bv128) returns (dst: bv16)
{
    if ($Gt'Bv128'(src, 65535bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From128(src1: bv16, src2: bv128) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From128(src1: bv16, src2: bv128) returns (dst: bv16)
{
    if ($Ge'Bv128'(src2, 16bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From128(src1: bv16, src2: bv128) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From128(src1: bv16, src2: bv128) returns (dst: bv16)
{
    if ($Ge'Bv128'(src2, 16bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv256to16(src: bv256) returns (dst: bv16)
{
    if ($Gt'Bv256'(src, 65535bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From256(src1: bv16, src2: bv256) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From256(src1: bv16, src2: bv256) returns (dst: bv16)
{
    if ($Ge'Bv256'(src2, 16bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From256(src1: bv16, src2: bv256) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From256(src1: bv16, src2: bv256) returns (dst: bv16)
{
    if ($Ge'Bv256'(src2, 16bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv8to32(src: bv8) returns (dst: bv32)
{
    dst := 0bv24 ++ src;
}


function $shlBv32From8(src1: bv32, src2: bv8) returns (bv32)
{
    $Shl'Bv32'(src1, 0bv24 ++ src2)
}

procedure {:inline 1} $ShlBv32From8(src1: bv32, src2: bv8) returns (dst: bv32)
{
    if ($Ge'Bv8'(src2, 32bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, 0bv24 ++ src2);
}

function $shrBv32From8(src1: bv32, src2: bv8) returns (bv32)
{
    $Shr'Bv32'(src1, 0bv24 ++ src2)
}

procedure {:inline 1} $ShrBv32From8(src1: bv32, src2: bv8) returns (dst: bv32)
{
    if ($Ge'Bv8'(src2, 32bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, 0bv24 ++ src2);
}

procedure {:inline 1} $CastBv16to32(src: bv16) returns (dst: bv32)
{
    dst := 0bv16 ++ src;
}


function $shlBv32From16(src1: bv32, src2: bv16) returns (bv32)
{
    $Shl'Bv32'(src1, 0bv16 ++ src2)
}

procedure {:inline 1} $ShlBv32From16(src1: bv32, src2: bv16) returns (dst: bv32)
{
    if ($Ge'Bv16'(src2, 32bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, 0bv16 ++ src2);
}

function $shrBv32From16(src1: bv32, src2: bv16) returns (bv32)
{
    $Shr'Bv32'(src1, 0bv16 ++ src2)
}

procedure {:inline 1} $ShrBv32From16(src1: bv32, src2: bv16) returns (dst: bv32)
{
    if ($Ge'Bv16'(src2, 32bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, 0bv16 ++ src2);
}

procedure {:inline 1} $CastBv32to32(src: bv32) returns (dst: bv32)
{
    dst := src;
}


function $shlBv32From32(src1: bv32, src2: bv32) returns (bv32)
{
    $Shl'Bv32'(src1, src2)
}

procedure {:inline 1} $ShlBv32From32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Ge'Bv32'(src2, 32bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2);
}

function $shrBv32From32(src1: bv32, src2: bv32) returns (bv32)
{
    $Shr'Bv32'(src1, src2)
}

procedure {:inline 1} $ShrBv32From32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Ge'Bv32'(src2, 32bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2);
}

procedure {:inline 1} $CastBv64to32(src: bv64) returns (dst: bv32)
{
    if ($Gt'Bv64'(src, 2147483647bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From64(src1: bv32, src2: bv64) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From64(src1: bv32, src2: bv64) returns (dst: bv32)
{
    if ($Ge'Bv64'(src2, 32bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From64(src1: bv32, src2: bv64) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From64(src1: bv32, src2: bv64) returns (dst: bv32)
{
    if ($Ge'Bv64'(src2, 32bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv128to32(src: bv128) returns (dst: bv32)
{
    if ($Gt'Bv128'(src, 2147483647bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From128(src1: bv32, src2: bv128) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From128(src1: bv32, src2: bv128) returns (dst: bv32)
{
    if ($Ge'Bv128'(src2, 32bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From128(src1: bv32, src2: bv128) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From128(src1: bv32, src2: bv128) returns (dst: bv32)
{
    if ($Ge'Bv128'(src2, 32bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv256to32(src: bv256) returns (dst: bv32)
{
    if ($Gt'Bv256'(src, 2147483647bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From256(src1: bv32, src2: bv256) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From256(src1: bv32, src2: bv256) returns (dst: bv32)
{
    if ($Ge'Bv256'(src2, 32bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From256(src1: bv32, src2: bv256) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From256(src1: bv32, src2: bv256) returns (dst: bv32)
{
    if ($Ge'Bv256'(src2, 32bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv8to64(src: bv8) returns (dst: bv64)
{
    dst := 0bv56 ++ src;
}


function $shlBv64From8(src1: bv64, src2: bv8) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv56 ++ src2)
}

procedure {:inline 1} $ShlBv64From8(src1: bv64, src2: bv8) returns (dst: bv64)
{
    if ($Ge'Bv8'(src2, 64bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv56 ++ src2);
}

function $shrBv64From8(src1: bv64, src2: bv8) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv56 ++ src2)
}

procedure {:inline 1} $ShrBv64From8(src1: bv64, src2: bv8) returns (dst: bv64)
{
    if ($Ge'Bv8'(src2, 64bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv56 ++ src2);
}

procedure {:inline 1} $CastBv16to64(src: bv16) returns (dst: bv64)
{
    dst := 0bv48 ++ src;
}


function $shlBv64From16(src1: bv64, src2: bv16) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv48 ++ src2)
}

procedure {:inline 1} $ShlBv64From16(src1: bv64, src2: bv16) returns (dst: bv64)
{
    if ($Ge'Bv16'(src2, 64bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv48 ++ src2);
}

function $shrBv64From16(src1: bv64, src2: bv16) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv48 ++ src2)
}

procedure {:inline 1} $ShrBv64From16(src1: bv64, src2: bv16) returns (dst: bv64)
{
    if ($Ge'Bv16'(src2, 64bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv48 ++ src2);
}

procedure {:inline 1} $CastBv32to64(src: bv32) returns (dst: bv64)
{
    dst := 0bv32 ++ src;
}


function $shlBv64From32(src1: bv64, src2: bv32) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv32 ++ src2)
}

procedure {:inline 1} $ShlBv64From32(src1: bv64, src2: bv32) returns (dst: bv64)
{
    if ($Ge'Bv32'(src2, 64bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv32 ++ src2);
}

function $shrBv64From32(src1: bv64, src2: bv32) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv32 ++ src2)
}

procedure {:inline 1} $ShrBv64From32(src1: bv64, src2: bv32) returns (dst: bv64)
{
    if ($Ge'Bv32'(src2, 64bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv32 ++ src2);
}

procedure {:inline 1} $CastBv64to64(src: bv64) returns (dst: bv64)
{
    dst := src;
}


function $shlBv64From64(src1: bv64, src2: bv64) returns (bv64)
{
    $Shl'Bv64'(src1, src2)
}

procedure {:inline 1} $ShlBv64From64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Ge'Bv64'(src2, 64bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2);
}

function $shrBv64From64(src1: bv64, src2: bv64) returns (bv64)
{
    $Shr'Bv64'(src1, src2)
}

procedure {:inline 1} $ShrBv64From64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Ge'Bv64'(src2, 64bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2);
}

procedure {:inline 1} $CastBv128to64(src: bv128) returns (dst: bv64)
{
    if ($Gt'Bv128'(src, 18446744073709551615bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[64:0];
}


function $shlBv64From128(src1: bv64, src2: bv128) returns (bv64)
{
    $Shl'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShlBv64From128(src1: bv64, src2: bv128) returns (dst: bv64)
{
    if ($Ge'Bv128'(src2, 64bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2[64:0]);
}

function $shrBv64From128(src1: bv64, src2: bv128) returns (bv64)
{
    $Shr'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShrBv64From128(src1: bv64, src2: bv128) returns (dst: bv64)
{
    if ($Ge'Bv128'(src2, 64bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2[64:0]);
}

procedure {:inline 1} $CastBv256to64(src: bv256) returns (dst: bv64)
{
    if ($Gt'Bv256'(src, 18446744073709551615bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[64:0];
}


function $shlBv64From256(src1: bv64, src2: bv256) returns (bv64)
{
    $Shl'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShlBv64From256(src1: bv64, src2: bv256) returns (dst: bv64)
{
    if ($Ge'Bv256'(src2, 64bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2[64:0]);
}

function $shrBv64From256(src1: bv64, src2: bv256) returns (bv64)
{
    $Shr'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShrBv64From256(src1: bv64, src2: bv256) returns (dst: bv64)
{
    if ($Ge'Bv256'(src2, 64bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2[64:0]);
}

procedure {:inline 1} $CastBv8to128(src: bv8) returns (dst: bv128)
{
    dst := 0bv120 ++ src;
}


function $shlBv128From8(src1: bv128, src2: bv8) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv120 ++ src2)
}

procedure {:inline 1} $ShlBv128From8(src1: bv128, src2: bv8) returns (dst: bv128)
{
    if ($Ge'Bv8'(src2, 128bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv120 ++ src2);
}

function $shrBv128From8(src1: bv128, src2: bv8) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv120 ++ src2)
}

procedure {:inline 1} $ShrBv128From8(src1: bv128, src2: bv8) returns (dst: bv128)
{
    if ($Ge'Bv8'(src2, 128bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv120 ++ src2);
}

procedure {:inline 1} $CastBv16to128(src: bv16) returns (dst: bv128)
{
    dst := 0bv112 ++ src;
}


function $shlBv128From16(src1: bv128, src2: bv16) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv112 ++ src2)
}

procedure {:inline 1} $ShlBv128From16(src1: bv128, src2: bv16) returns (dst: bv128)
{
    if ($Ge'Bv16'(src2, 128bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv112 ++ src2);
}

function $shrBv128From16(src1: bv128, src2: bv16) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv112 ++ src2)
}

procedure {:inline 1} $ShrBv128From16(src1: bv128, src2: bv16) returns (dst: bv128)
{
    if ($Ge'Bv16'(src2, 128bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv112 ++ src2);
}

procedure {:inline 1} $CastBv32to128(src: bv32) returns (dst: bv128)
{
    dst := 0bv96 ++ src;
}


function $shlBv128From32(src1: bv128, src2: bv32) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv96 ++ src2)
}

procedure {:inline 1} $ShlBv128From32(src1: bv128, src2: bv32) returns (dst: bv128)
{
    if ($Ge'Bv32'(src2, 128bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv96 ++ src2);
}

function $shrBv128From32(src1: bv128, src2: bv32) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv96 ++ src2)
}

procedure {:inline 1} $ShrBv128From32(src1: bv128, src2: bv32) returns (dst: bv128)
{
    if ($Ge'Bv32'(src2, 128bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv96 ++ src2);
}

procedure {:inline 1} $CastBv64to128(src: bv64) returns (dst: bv128)
{
    dst := 0bv64 ++ src;
}


function $shlBv128From64(src1: bv128, src2: bv64) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv64 ++ src2)
}

procedure {:inline 1} $ShlBv128From64(src1: bv128, src2: bv64) returns (dst: bv128)
{
    if ($Ge'Bv64'(src2, 128bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv64 ++ src2);
}

function $shrBv128From64(src1: bv128, src2: bv64) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv64 ++ src2)
}

procedure {:inline 1} $ShrBv128From64(src1: bv128, src2: bv64) returns (dst: bv128)
{
    if ($Ge'Bv64'(src2, 128bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv64 ++ src2);
}

procedure {:inline 1} $CastBv128to128(src: bv128) returns (dst: bv128)
{
    dst := src;
}


function $shlBv128From128(src1: bv128, src2: bv128) returns (bv128)
{
    $Shl'Bv128'(src1, src2)
}

procedure {:inline 1} $ShlBv128From128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Ge'Bv128'(src2, 128bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, src2);
}

function $shrBv128From128(src1: bv128, src2: bv128) returns (bv128)
{
    $Shr'Bv128'(src1, src2)
}

procedure {:inline 1} $ShrBv128From128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Ge'Bv128'(src2, 128bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, src2);
}

procedure {:inline 1} $CastBv256to128(src: bv256) returns (dst: bv128)
{
    if ($Gt'Bv256'(src, 340282366920938463463374607431768211455bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[128:0];
}


function $shlBv128From256(src1: bv128, src2: bv256) returns (bv128)
{
    $Shl'Bv128'(src1, src2[128:0])
}

procedure {:inline 1} $ShlBv128From256(src1: bv128, src2: bv256) returns (dst: bv128)
{
    if ($Ge'Bv256'(src2, 128bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, src2[128:0]);
}

function $shrBv128From256(src1: bv128, src2: bv256) returns (bv128)
{
    $Shr'Bv128'(src1, src2[128:0])
}

procedure {:inline 1} $ShrBv128From256(src1: bv128, src2: bv256) returns (dst: bv128)
{
    if ($Ge'Bv256'(src2, 128bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, src2[128:0]);
}

procedure {:inline 1} $CastBv8to256(src: bv8) returns (dst: bv256)
{
    dst := 0bv248 ++ src;
}


function $shlBv256From8(src1: bv256, src2: bv8) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv248 ++ src2)
}

procedure {:inline 1} $ShlBv256From8(src1: bv256, src2: bv8) returns (dst: bv256)
{
    if ($Ge'Bv8'(src2, 256bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv248 ++ src2);
}

function $shrBv256From8(src1: bv256, src2: bv8) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv248 ++ src2)
}

procedure {:inline 1} $ShrBv256From8(src1: bv256, src2: bv8) returns (dst: bv256)
{
    if ($Ge'Bv8'(src2, 256bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv248 ++ src2);
}

procedure {:inline 1} $CastBv16to256(src: bv16) returns (dst: bv256)
{
    dst := 0bv240 ++ src;
}


function $shlBv256From16(src1: bv256, src2: bv16) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv240 ++ src2)
}

procedure {:inline 1} $ShlBv256From16(src1: bv256, src2: bv16) returns (dst: bv256)
{
    if ($Ge'Bv16'(src2, 256bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv240 ++ src2);
}

function $shrBv256From16(src1: bv256, src2: bv16) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv240 ++ src2)
}

procedure {:inline 1} $ShrBv256From16(src1: bv256, src2: bv16) returns (dst: bv256)
{
    if ($Ge'Bv16'(src2, 256bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv240 ++ src2);
}

procedure {:inline 1} $CastBv32to256(src: bv32) returns (dst: bv256)
{
    dst := 0bv224 ++ src;
}


function $shlBv256From32(src1: bv256, src2: bv32) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv224 ++ src2)
}

procedure {:inline 1} $ShlBv256From32(src1: bv256, src2: bv32) returns (dst: bv256)
{
    if ($Ge'Bv32'(src2, 256bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv224 ++ src2);
}

function $shrBv256From32(src1: bv256, src2: bv32) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv224 ++ src2)
}

procedure {:inline 1} $ShrBv256From32(src1: bv256, src2: bv32) returns (dst: bv256)
{
    if ($Ge'Bv32'(src2, 256bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv224 ++ src2);
}

procedure {:inline 1} $CastBv64to256(src: bv64) returns (dst: bv256)
{
    dst := 0bv192 ++ src;
}


function $shlBv256From64(src1: bv256, src2: bv64) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv192 ++ src2)
}

procedure {:inline 1} $ShlBv256From64(src1: bv256, src2: bv64) returns (dst: bv256)
{
    if ($Ge'Bv64'(src2, 256bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv192 ++ src2);
}

function $shrBv256From64(src1: bv256, src2: bv64) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv192 ++ src2)
}

procedure {:inline 1} $ShrBv256From64(src1: bv256, src2: bv64) returns (dst: bv256)
{
    if ($Ge'Bv64'(src2, 256bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv192 ++ src2);
}

procedure {:inline 1} $CastBv128to256(src: bv128) returns (dst: bv256)
{
    dst := 0bv128 ++ src;
}


function $shlBv256From128(src1: bv256, src2: bv128) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv128 ++ src2)
}

procedure {:inline 1} $ShlBv256From128(src1: bv256, src2: bv128) returns (dst: bv256)
{
    if ($Ge'Bv128'(src2, 256bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv128 ++ src2);
}

function $shrBv256From128(src1: bv256, src2: bv128) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv128 ++ src2)
}

procedure {:inline 1} $ShrBv256From128(src1: bv256, src2: bv128) returns (dst: bv256)
{
    if ($Ge'Bv128'(src2, 256bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv128 ++ src2);
}

procedure {:inline 1} $CastBv256to256(src: bv256) returns (dst: bv256)
{
    dst := src;
}


function $shlBv256From256(src1: bv256, src2: bv256) returns (bv256)
{
    $Shl'Bv256'(src1, src2)
}

procedure {:inline 1} $ShlBv256From256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Ge'Bv256'(src2, 256bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, src2);
}

function $shrBv256From256(src1: bv256, src2: bv256) returns (bv256)
{
    $Shr'Bv256'(src1, src2)
}

procedure {:inline 1} $ShrBv256From256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Ge'Bv256'(src2, 256bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, src2);
}

procedure {:inline 1} $ShlU16(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU16(src1, src2);
}

procedure {:inline 1} $ShlU32(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU32(src1, src2);
}

procedure {:inline 1} $ShlU64(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 64) {
       call $ExecFailureAbort();
       return;
    }
    dst := $shlU64(src1, src2);
}

procedure {:inline 1} $ShlU128(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU128(src1, src2);
}

procedure {:inline 1} $ShlU256(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shlU256(src1, src2);
}

procedure {:inline 1} $Shr(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU8(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU16(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU32(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU64(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU128(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU256(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shr(src1, src2);
}

procedure {:inline 1} $MulU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU16(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU32(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU256(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $Div(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 div src2;
}

procedure {:inline 1} $Mod(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 mod src2;
}

procedure {:inline 1} $ArithBinaryUnimplemented(src1: int, src2: int) returns (dst: int);

procedure {:inline 1} $Lt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 < src2;
}

procedure {:inline 1} $Gt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 > src2;
}

procedure {:inline 1} $Le(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 <= src2;
}

procedure {:inline 1} $Ge(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 >= src2;
}

procedure {:inline 1} $And(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 && src2;
}

procedure {:inline 1} $Or(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 || src2;
}

procedure {:inline 1} $Not(src: bool) returns (dst: bool)
{
    dst := !src;
}

// Pack and Unpack are auto-generated for each type T


// ==================================================================================
// Native Vector

function {:inline} $SliceVecByRange<T>(v: Vec T, r: $Range): Vec T {
    SliceVec(v, r->lb, r->ub)
}

// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `u8`

// Not inlined. It appears faster this way.
function $IsEqual'vec'u8''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'u8'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'u8''(v: Vec (int), prefix: Vec (int)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'u8'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'u8''(v: Vec (int), suffix: Vec (int)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'u8'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'u8''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'u8'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'u8'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e))
}

function $IndexOfVec'u8'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'u8'(v, e)}
    (var i := $IndexOfVec'u8'(v, e);
     if (!$ContainsVec'u8'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'u8'(ReadVec(v, j), e))));


function {:inline} $RangeVec'u8'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'u8'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'u8'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'u8'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'u8'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'u8'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'u8'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'u8'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'u8'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'u8'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'u8'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'u8'(m: $Mutation (Vec (int)), left: int, right: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'u8'(m: $Mutation (Vec (int)), rot: int) returns (n: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'u8'(m: $Mutation (Vec (int)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var mid_left_vec: Vec (int);
    var mid_right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'u8'(m: $Mutation (Vec (int)), i: int, e: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'u8'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'u8'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'u8'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'u8'(m: $Mutation (Vec (int)), index: int)
returns (dst: $Mutation (int), m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'u8'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'u8'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'u8'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var v: Vec (int);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var len: int;
    var v: Vec (int);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'u8'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'u8'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'u8'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'u8'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ==================================================================================
// Native Table

// ==================================================================================
// Native Hash

// Hash is modeled as an otherwise uninterpreted injection.
// In truth, it is not an injection since the domain has greater cardinality
// (arbitrary length vectors) than the co-domain (vectors of length 32).  But it is
// common to assume in code there are no hash collisions in practice.  Fortunately,
// Boogie is not smart enough to recognized that there is an inconsistency.
// FIXME: If we were using a reliable extensional theory of arrays, and if we could use ==
// instead of $IsEqual, we might be able to avoid so many quantified formulas by
// using a sha2_inverse function in the ensures conditions of Hash_sha2_256 to
// assert that sha2/3 are injections without using global quantified axioms.


function $1_hash_sha2(val: Vec int): Vec int;

// This says that Hash_sha2 is bijective.
axiom (forall v1,v2: Vec int :: {$1_hash_sha2(v1), $1_hash_sha2(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha2(v1), $1_hash_sha2(v2)));

procedure $1_hash_sha2_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha2(val);     // returns Hash_sha2 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha2_256(val: Vec int): Vec int {
    $1_hash_sha2(val)
}

// similarly for Hash_sha3
function $1_hash_sha3(val: Vec int): Vec int;

axiom (forall v1,v2: Vec int :: {$1_hash_sha3(v1), $1_hash_sha3(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha3(v1), $1_hash_sha3(v2)));

procedure $1_hash_sha3_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha3(val);     // returns Hash_sha3 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha3_256(val: Vec int): Vec int {
    $1_hash_sha3(val)
}

// ==================================================================================
// Native string

// TODO: correct implementation of strings

procedure {:inline 1} $1_string_internal_check_utf8(x: Vec int) returns (r: bool) {
}

procedure {:inline 1} $1_string_internal_sub_string(x: Vec int, i: int, j: int) returns (r: Vec int) {
}

procedure {:inline 1} $1_string_internal_index_of(x: Vec int, y: Vec int) returns (r: int) {
}

procedure {:inline 1} $1_string_internal_is_char_boundary(x: Vec int, i: int) returns (r: bool) {
}




// ==================================================================================
// Native diem_account

procedure {:inline 1} $1_DiemAccount_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

procedure {:inline 1} $1_DiemAccount_destroy_signer(
  signer: $signer
) {
  return;
}

// ==================================================================================
// Native account

procedure {:inline 1} $1_Account_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

// ==================================================================================
// Native Signer

datatype $signer {
    $signer($addr: int),
    $permissioned_signer($addr: int, $permission_addr: int)
}

function {:inline} $IsValid'signer'(s: $signer): bool {
    if s is $signer then
        $IsValid'address'(s->$addr)
    else
        $IsValid'address'(s->$addr) &&
        $IsValid'address'(s->$permission_addr)
}

function {:inline} $IsEqual'signer'(s1: $signer, s2: $signer): bool {
    if s1 is $signer && s2 is $signer then
        s1 == s2
    else if s1 is $permissioned_signer && s2 is $permissioned_signer then
        s1 == s2
    else
        false
}

procedure {:inline 1} $1_signer_borrow_address(signer: $signer) returns (res: int) {
    res := signer->$addr;
}

function {:inline} $1_signer_$borrow_address(signer: $signer): int
{
    signer->$addr
}

function $1_signer_is_txn_signer(s: $signer): bool;

function $1_signer_is_txn_signer_addr(a: int): bool;


// ==================================================================================
// Native signature

// Signature related functionality is handled via uninterpreted functions. This is sound
// currently because we verify every code path based on signature verification with
// an arbitrary interpretation.

function $1_Signature_$ed25519_validate_pubkey(public_key: Vec int): bool;
function $1_Signature_$ed25519_verify(signature: Vec int, public_key: Vec int, message: Vec int): bool;

// Needed because we do not have extensional equality:
axiom (forall k1, k2: Vec int ::
    {$1_Signature_$ed25519_validate_pubkey(k1), $1_Signature_$ed25519_validate_pubkey(k2)}
    $IsEqual'vec'u8''(k1, k2) ==> $1_Signature_$ed25519_validate_pubkey(k1) == $1_Signature_$ed25519_validate_pubkey(k2));
axiom (forall s1, s2, k1, k2, m1, m2: Vec int ::
    {$1_Signature_$ed25519_verify(s1, k1, m1), $1_Signature_$ed25519_verify(s2, k2, m2)}
    $IsEqual'vec'u8''(s1, s2) && $IsEqual'vec'u8''(k1, k2) && $IsEqual'vec'u8''(m1, m2)
    ==> $1_Signature_$ed25519_verify(s1, k1, m1) == $1_Signature_$ed25519_verify(s2, k2, m2));


procedure {:inline 1} $1_Signature_ed25519_validate_pubkey(public_key: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_validate_pubkey(public_key);
}

procedure {:inline 1} $1_Signature_ed25519_verify(
        signature: Vec int, public_key: Vec int, message: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_verify(signature, public_key, message);
}


// ==================================================================================
// Native bcs::serialize


// ==================================================================================
// Native Event module



procedure {:inline 1} $InitEventStore() {
}

// ============================================================================================
// Type Reflection on Type Parameters

datatype $TypeParamInfo {
    $TypeParamBool(),
    $TypeParamU8(),
    $TypeParamU16(),
    $TypeParamU32(),
    $TypeParamU64(),
    $TypeParamU128(),
    $TypeParamU256(),
    $TypeParamAddress(),
    $TypeParamSigner(),
    $TypeParamVector(e: $TypeParamInfo),
    $TypeParamStruct(a: int, m: Vec int, s: Vec int)
}



//==================================
// Begin Translation



// Given Types for Type Parameters


// struct prover_basics::Coin at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:71:5+57
datatype $42_prover_basics_Coin {
    $42_prover_basics_Coin($value: int)
}
function {:inline} $Update'$42_prover_basics_Coin'_value(s: $42_prover_basics_Coin, x: int): $42_prover_basics_Coin {
    $42_prover_basics_Coin(x)
}
function $IsValid'$42_prover_basics_Coin'(s: $42_prover_basics_Coin): bool {
    $IsValid'u64'(s->$value)
}
function {:inline} $IsEqual'$42_prover_basics_Coin'(s1: $42_prover_basics_Coin, s2: $42_prover_basics_Coin): bool {
    s1 == s2
}

// struct prover_basics::Wallet at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:133:5+77
datatype $42_prover_basics_Wallet {
    $42_prover_basics_Wallet($balance: int, $frozen: bool)
}
function {:inline} $Update'$42_prover_basics_Wallet'_balance(s: $42_prover_basics_Wallet, x: int): $42_prover_basics_Wallet {
    $42_prover_basics_Wallet(x, s->$frozen)
}
function {:inline} $Update'$42_prover_basics_Wallet'_frozen(s: $42_prover_basics_Wallet, x: bool): $42_prover_basics_Wallet {
    $42_prover_basics_Wallet(s->$balance, x)
}
function $IsValid'$42_prover_basics_Wallet'(s: $42_prover_basics_Wallet): bool {
    $IsValid'u64'(s->$balance)
      && $IsValid'bool'(s->$frozen)
}
function {:inline} $IsEqual'$42_prover_basics_Wallet'(s1: $42_prover_basics_Wallet, s2: $42_prover_basics_Wallet): bool {
    s1 == s2
}

// fun prover_basics::add [verification] at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:15:5+59
procedure {:timeLimit 40} $42_prover_basics_add$verify(_$t0: int, _$t1: int) returns ($ret0: int)
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t0: int;
    var $t1: int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:15:5+1
    assume {:print "$at(2,404,405)"} true;
    assume $IsValid'u64'($t0);

    // assume WellFormed($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:15:5+1
    assume $IsValid'u64'($t1);

    // trace_local[a]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:15:5+1
    assume {:print "$track_local(1,0,0):", $t0} $t0 == $t0;

    // trace_local[b]($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:15:5+1
    assume {:print "$track_local(1,0,1):", $t1} $t1 == $t1;

    // $t2 := +($t0, $t1) on_abort goto L2 with $t3 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:16:9+5
    assume {:print "$at(2,451,456)"} true;
    call $t2 := $AddU64($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,451,456)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(1,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t2) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:16:9+5
    assume {:print "$track_return(1,0,0):", $t2} $t2 == $t2;

    // label L1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:17:5+1
    assume {:print "$at(2,462,463)"} true;
L1:

    // assert Not(Gt(Add($t0, $t1), 18446744073709551615)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:21:9+26
    assume {:print "$at(2,525,551)"} true;
    assert {:msg "assert_failed(2,525,551): function does not abort under this condition"}
      !(($t0 + $t1) > 18446744073709551615);

    // assert Eq<u64>($t2, Add($t0, $t1)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:20:9+24
    assume {:print "$at(2,491,515)"} true;
    assert {:msg "assert_failed(2,491,515): post-condition does not hold"}
      $IsEqual'u64'($t2, ($t0 + $t1));

    // return $t2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:20:9+24
    $ret0 := $t2;
    return;

    // label L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:17:5+1
    assume {:print "$at(2,462,463)"} true;
L2:

    // assert Gt(Add($t0, $t1), 18446744073709551615) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:19:5+87
    assume {:print "$at(2,471,558)"} true;
    assert {:msg "assert_failed(2,471,558): abort not covered by any of the `aborts_if` clauses"}
      (($t0 + $t1) > 18446744073709551615);

    // abort($t3) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:19:5+87
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun prover_basics::coin_value [verification] at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:119:5+68
procedure {:timeLimit 40} $42_prover_basics_coin_value$verify(_$t0: $42_prover_basics_Coin) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t0: $42_prover_basics_Coin;
    var $temp_0'$42_prover_basics_Coin': $42_prover_basics_Coin;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:119:5+1
    assume {:print "$at(2,3057,3058)"} true;
    assume $IsValid'$42_prover_basics_Coin'($t0);

    // trace_local[coin]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:119:5+1
    assume {:print "$track_local(1,1,0):", $t0} $t0 == $t0;

    // $t1 := get_field<0x42::prover_basics::Coin>.value($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:120:9+10
    assume {:print "$at(2,3108,3118)"} true;
    $t1 := $t0->$value;

    // trace_return[0]($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:120:9+10
    assume {:print "$track_return(1,1,0):", $t1} $t1 == $t1;

    // label L1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:121:5+1
    assume {:print "$at(2,3124,3125)"} true;
L1:

    // assert Not(false) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:125:9+16
    assume {:print "$at(2,3199,3215)"} true;
    assert {:msg "assert_failed(2,3199,3215): function does not abort under this condition"}
      !false;

    // assert Eq<u64>($t1, select prover_basics::Coin.value<0x42::prover_basics::Coin>($t0)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:124:9+29
    assume {:print "$at(2,3160,3189)"} true;
    assert {:msg "assert_failed(2,3160,3189): post-condition does not hold"}
      $IsEqual'u64'($t1, $t0->$value);

    // return $t1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:124:9+29
    $ret0 := $t1;
    return;

}

// fun prover_basics::conditional_update [verification] at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:246:5+199
procedure {:timeLimit 40} $42_prover_basics_conditional_update$verify(_$t0: $Mutation ($42_prover_basics_Wallet), _$t1: int, _$t2: bool) returns ($ret0: $Mutation ($42_prover_basics_Wallet))
{
    // declare local variables
    var $t3: $Mutation (int);
    var $t4: $42_prover_basics_Wallet;
    var $t5: bool;
    var $t6: bool;
    var $t7: $Mutation (int);
    var $t8: int;
    var $t9: bool;
    var $t0: $Mutation ($42_prover_basics_Wallet);
    var $t1: int;
    var $t2: bool;
    var $temp_0'$42_prover_basics_Wallet': $42_prover_basics_Wallet;
    var $temp_0'bool': bool;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();
    assume $t0->l == $Param(0);

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:246:5+1
    assume {:print "$at(2,7014,7015)"} true;
    assume $IsValid'$42_prover_basics_Wallet'($Dereference($t0));

    // assume WellFormed($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:246:5+1
    assume $IsValid'u64'($t1);

    // assume WellFormed($t2) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:246:5+1
    assume $IsValid'bool'($t2);

    // $t4 := read_ref($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:246:5+1
    $t4 := $Dereference($t0);

    // $t5 := copy($t2) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:246:5+1
    $t5 := $t2;

    // trace_local[wallet]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:246:5+1
    $temp_0'$42_prover_basics_Wallet' := $Dereference($t0);
    assume {:print "$track_local(1,2,0):", $temp_0'$42_prover_basics_Wallet'} $temp_0'$42_prover_basics_Wallet' == $temp_0'$42_prover_basics_Wallet';

    // trace_local[new_balance]($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:246:5+1
    assume {:print "$track_local(1,2,1):", $t1} $t1 == $t1;

    // trace_local[force]($t2) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:246:5+1
    assume {:print "$track_local(1,2,2):", $t2} $t2 == $t2;

    // if ($t2) goto L1 else goto L0 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:247:13+38
    assume {:print "$at(2,7111,7149)"} true;
    if ($t2) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:247:13+38
L1:

    // $t6 := true at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:247:13+38
    assume {:print "$at(2,7111,7149)"} true;
    $t6 := true;
    assume $IsValid'bool'($t6);

    // $t2 := $t6 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:247:13+38
    $t2 := $t6;

    // trace_local[force]($t6) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:247:13+38
    assume {:print "$track_local(1,2,2):", $t6} $t6 == $t6;

    // label L5 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:247:9+99
L5:

    // if ($t2) goto L3 else goto L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:247:9+99
    assume {:print "$at(2,7107,7206)"} true;
    if ($t2) { goto L3; } else { goto L2; }

    // label L3 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:248:13+14
    assume {:print "$at(2,7166,7180)"} true;
L3:

    // $t7 := borrow_field<0x42::prover_basics::Wallet>.balance($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:248:13+14
    assume {:print "$at(2,7166,7180)"} true;
    $t7 := $ChildMutation($t0, 0, $Dereference($t0)->$balance);

    // trace_local[$t6]($t7) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:248:13+28
    $temp_0'u64' := $Dereference($t7);
    assume {:print "$track_local(1,2,3):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // write_ref($t7, $t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:248:13+28
    $t7 := $UpdateMutation($t7, $t1);

    // write_back[Reference($t0).balance (u64)]($t7) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:248:13+28
    $t0 := $UpdateMutation($t0, $Update'$42_prover_basics_Wallet'_balance($Dereference($t0), $Dereference($t7)));

    // trace_local[wallet]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:248:13+28
    $temp_0'$42_prover_basics_Wallet' := $Dereference($t0);
    assume {:print "$track_local(1,2,0):", $temp_0'$42_prover_basics_Wallet'} $temp_0'$42_prover_basics_Wallet' == $temp_0'$42_prover_basics_Wallet';

    // label L4 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:247:9+99
    assume {:print "$at(2,7107,7206)"} true;
L4:

    // trace_local[wallet]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:247:9+99
    assume {:print "$at(2,7107,7206)"} true;
    $temp_0'$42_prover_basics_Wallet' := $Dereference($t0);
    assume {:print "$track_local(1,2,0):", $temp_0'$42_prover_basics_Wallet'} $temp_0'$42_prover_basics_Wallet' == $temp_0'$42_prover_basics_Wallet';

    // goto L6 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:247:9+99
    goto L6;

    // label L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:247:9+99
L2:

    // drop($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:247:9+99
    assume {:print "$at(2,7107,7206)"} true;

    // goto L4 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:247:9+99
    goto L4;

    // label L0 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:247:22+14
L0:

    // $t8 := get_field<0x42::prover_basics::Wallet>.balance($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:247:22+14
    assume {:print "$at(2,7120,7134)"} true;
    $t8 := $Dereference($t0)->$balance;

    // $t9 := <=($t8, $t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:247:22+29
    call $t9 := $Le($t8, $t1);

    // $t2 := $t9 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:247:22+29
    $t2 := $t9;

    // trace_local[force]($t9) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:247:22+29
    assume {:print "$track_local(1,2,2):", $t9} $t9 == $t9;

    // goto L5 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:247:22+29
    goto L5;

    // label L6 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:250:5+1
    assume {:print "$at(2,7212,7213)"} true;
L6:

    // assert Not(false) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:267:9+16
    assume {:print "$at(2,7856,7872)"} true;
    assert {:msg "assert_failed(2,7856,7872): function does not abort under this condition"}
      !false;

    // assert Implies($t5, Eq<u64>(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t0), $t1)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:254:9+48
    assume {:print "$at(2,7309,7357)"} true;
    assert {:msg "assert_failed(2,7309,7357): post-condition does not hold"}
      ($t5 ==> $IsEqual'u64'($Dereference($t0)->$balance, $t1));

    // assert Implies(And(Not($t5), Gt(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t4), $t1)), Eq<u64>(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t0), select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t4))) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:257:9+114
    assume {:print "$at(2,7427,7541)"} true;
    assert {:msg "assert_failed(2,7427,7541): post-condition does not hold"}
      ((!$t5 && ($t4->$balance > $t1)) ==> $IsEqual'u64'($Dereference($t0)->$balance, $t4->$balance));

    // assert Implies(And(Not($t5), Le(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t4), $t1)), Eq<u64>(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t0), $t1)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:261:9+107
    assume {:print "$at(2,7625,7732)"} true;
    assert {:msg "assert_failed(2,7625,7732): post-condition does not hold"}
      ((!$t5 && ($t4->$balance <= $t1)) ==> $IsEqual'u64'($Dereference($t0)->$balance, $t1));

    // assert Eq<bool>(select prover_basics::Wallet.frozen<0x42::prover_basics::Wallet>($t0), select prover_basics::Wallet.frozen<0x42::prover_basics::Wallet>($t4)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:265:9+44
    assume {:print "$at(2,7792,7836)"} true;
    assert {:msg "assert_failed(2,7792,7836): post-condition does not hold"}
      $IsEqual'bool'($Dereference($t0)->$frozen, $t4->$frozen);

    // return () at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:265:9+44
    $ret0 := $t0;
    return;

}

// fun prover_basics::create_wallet [verification] at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:139:5+161
procedure {:timeLimit 40} $42_prover_basics_create_wallet$verify(_$t0: int) returns ($ret0: $42_prover_basics_Wallet)
{
    // declare local variables
    var $t1: bool;
    var $t2: $42_prover_basics_Wallet;
    var $t0: int;
    var $temp_0'$42_prover_basics_Wallet': $42_prover_basics_Wallet;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:139:5+1
    assume {:print "$at(2,3475,3476)"} true;
    assume $IsValid'u64'($t0);

    // trace_local[initial_balance]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:139:5+1
    assume {:print "$track_local(1,3,0):", $t0} $t0 == $t0;

    // $t1 := false at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:142:21+5
    assume {:print "$at(2,3612,3617)"} true;
    $t1 := false;
    assume $IsValid'bool'($t1);

    // $t2 := pack 0x42::prover_basics::Wallet($t0, $t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:140:9+88
    assume {:print "$at(2,3541,3629)"} true;
    $t2 := $42_prover_basics_Wallet($t0, $t1);

    // trace_return[0]($t2) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:140:9+88
    assume {:print "$track_return(1,3,0):", $t2} $t2 == $t2;

    // label L1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:144:5+1
    assume {:print "$at(2,3635,3636)"} true;
L1:

    // assert Not(false) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:149:9+16
    assume {:print "$at(2,3767,3783)"} true;
    assert {:msg "assert_failed(2,3767,3783): function does not abort under this condition"}
      !false;

    // assert Eq<u64>(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t2), $t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:147:9+42
    assume {:print "$at(2,3674,3716)"} true;
    assert {:msg "assert_failed(2,3674,3716): post-condition does not hold"}
      $IsEqual'u64'($t2->$balance, $t0);

    // assert Eq<bool>(select prover_basics::Wallet.frozen<0x42::prover_basics::Wallet>($t2), false) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:148:9+31
    assume {:print "$at(2,3726,3757)"} true;
    assert {:msg "assert_failed(2,3726,3757): post-condition does not hold"}
      $IsEqual'bool'($t2->$frozen, false);

    // return $t2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:148:9+31
    $ret0 := $t2;
    return;

}

// fun prover_basics::deposit [baseline] at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:153:5+149
procedure {:inline 1} $42_prover_basics_deposit(_$t0: $Mutation ($42_prover_basics_Wallet), _$t1: int) returns ($ret0: $Mutation ($42_prover_basics_Wallet))
{
    // declare local variables
    var $t2: bool;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: $Mutation (int);
    var $t7: int;
    var $t0: $Mutation ($42_prover_basics_Wallet);
    var $t1: int;
    var $temp_0'$42_prover_basics_Wallet': $42_prover_basics_Wallet;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // assume Not(select prover_basics::Wallet.frozen<0x42::prover_basics::Wallet>($t0)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:159:9+24
    assume {:print "$at(2,4006,4030)"} true;
    assume !$Dereference($t0)->$frozen;

    // assume Le(Add(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t0), $t1), 18446744073709551615) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:160:9+44
    assume {:print "$at(2,4040,4084)"} true;
    assume (($Dereference($t0)->$balance + $t1) <= 18446744073709551615);

    // trace_local[wallet]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:153:5+1
    assume {:print "$at(2,3825,3826)"} true;
    $temp_0'$42_prover_basics_Wallet' := $Dereference($t0);
    assume {:print "$track_local(1,4,0):", $temp_0'$42_prover_basics_Wallet'} $temp_0'$42_prover_basics_Wallet' == $temp_0'$42_prover_basics_Wallet';

    // trace_local[amount]($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:153:5+1
    assume {:print "$track_local(1,4,1):", $t1} $t1 == $t1;

    // $t2 := get_field<0x42::prover_basics::Wallet>.frozen($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:154:18+13
    assume {:print "$at(2,3898,3911)"} true;
    $t2 := $Dereference($t0)->$frozen;

    // if ($t2) goto L0 else goto L1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:154:17+14
    if ($t2) { goto L0; } else { goto L1; }

    // label L1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:155:26+14
    assume {:print "$at(2,3943,3957)"} true;
L1:

    // $t3 := get_field<0x42::prover_basics::Wallet>.balance($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:155:26+14
    assume {:print "$at(2,3943,3957)"} true;
    $t3 := $Dereference($t0)->$balance;

    // $t4 := +($t3, $t1) on_abort goto L3 with $t5 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:155:26+23
    call $t4 := $AddU64($t3, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,3943,3966)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(1,4):", $t5} $t5 == $t5;
        goto L3;
    }

    // $t6 := borrow_field<0x42::prover_basics::Wallet>.balance($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:155:9+14
    $t6 := $ChildMutation($t0, 0, $Dereference($t0)->$balance);

    // write_ref($t6, $t4) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:155:9+40
    $t6 := $UpdateMutation($t6, $t4);

    // write_back[Reference($t0).balance (u64)]($t6) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:155:9+40
    $t0 := $UpdateMutation($t0, $Update'$42_prover_basics_Wallet'_balance($Dereference($t0), $Dereference($t6)));

    // trace_local[wallet]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:155:9+40
    $temp_0'$42_prover_basics_Wallet' := $Dereference($t0);
    assume {:print "$track_local(1,4,0):", $temp_0'$42_prover_basics_Wallet'} $temp_0'$42_prover_basics_Wallet' == $temp_0'$42_prover_basics_Wallet';

    // trace_local[wallet]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:153:58+96
    assume {:print "$at(2,3878,3974)"} true;
    $temp_0'$42_prover_basics_Wallet' := $Dereference($t0);
    assume {:print "$track_local(1,4,0):", $temp_0'$42_prover_basics_Wallet'} $temp_0'$42_prover_basics_Wallet' == $temp_0'$42_prover_basics_Wallet';

    // goto L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:153:58+96
    goto L2;

    // label L0 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:154:9+6
    assume {:print "$at(2,3889,3895)"} true;
L0:

    // drop($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:154:9+6
    assume {:print "$at(2,3889,3895)"} true;

    // $t7 := 4 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:154:33+1
    $t7 := 4;
    assume $IsValid'u64'($t7);

    // trace_abort($t7) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:154:9+6
    assume {:print "$at(2,3889,3895)"} true;
    assume {:print "$track_abort(1,4):", $t7} $t7 == $t7;

    // $t5 := move($t7) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:154:9+6
    $t5 := $t7;

    // goto L3 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:154:9+6
    goto L3;

    // label L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:156:5+1
    assume {:print "$at(2,3973,3974)"} true;
L2:

    // return () at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:156:5+1
    assume {:print "$at(2,3973,3974)"} true;
    $ret0 := $t0;
    return;

    // label L3 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:156:5+1
L3:

    // abort($t5) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:156:5+1
    assume {:print "$at(2,3973,3974)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun prover_basics::deposit [verification] at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:153:5+149
procedure {:timeLimit 40} $42_prover_basics_deposit$verify(_$t0: $Mutation ($42_prover_basics_Wallet), _$t1: int) returns ($ret0: $Mutation ($42_prover_basics_Wallet))
{
    // declare local variables
    var $t2: $42_prover_basics_Wallet;
    var $t3: bool;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: $Mutation (int);
    var $t8: int;
    var $t0: $Mutation ($42_prover_basics_Wallet);
    var $t1: int;
    var $temp_0'$42_prover_basics_Wallet': $42_prover_basics_Wallet;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();
    assume $t0->l == $Param(0);

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:153:5+1
    assume {:print "$at(2,3825,3826)"} true;
    assume $IsValid'$42_prover_basics_Wallet'($Dereference($t0));

    // assume WellFormed($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:153:5+1
    assume $IsValid'u64'($t1);

    // assume Not(select prover_basics::Wallet.frozen<0x42::prover_basics::Wallet>($t0)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:159:9+24
    assume {:print "$at(2,4006,4030)"} true;
    assume !$Dereference($t0)->$frozen;

    // assume Le(Add(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t0), $t1), 18446744073709551615) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:160:9+44
    assume {:print "$at(2,4040,4084)"} true;
    assume (($Dereference($t0)->$balance + $t1) <= 18446744073709551615);

    // $t2 := read_ref($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:160:9+44
    $t2 := $Dereference($t0);

    // trace_local[wallet]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:153:5+1
    assume {:print "$at(2,3825,3826)"} true;
    $temp_0'$42_prover_basics_Wallet' := $Dereference($t0);
    assume {:print "$track_local(1,4,0):", $temp_0'$42_prover_basics_Wallet'} $temp_0'$42_prover_basics_Wallet' == $temp_0'$42_prover_basics_Wallet';

    // trace_local[amount]($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:153:5+1
    assume {:print "$track_local(1,4,1):", $t1} $t1 == $t1;

    // $t3 := get_field<0x42::prover_basics::Wallet>.frozen($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:154:18+13
    assume {:print "$at(2,3898,3911)"} true;
    $t3 := $Dereference($t0)->$frozen;

    // if ($t3) goto L0 else goto L1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:154:17+14
    if ($t3) { goto L0; } else { goto L1; }

    // label L1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:155:26+14
    assume {:print "$at(2,3943,3957)"} true;
L1:

    // $t4 := get_field<0x42::prover_basics::Wallet>.balance($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:155:26+14
    assume {:print "$at(2,3943,3957)"} true;
    $t4 := $Dereference($t0)->$balance;

    // $t5 := +($t4, $t1) on_abort goto L3 with $t6 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:155:26+23
    call $t5 := $AddU64($t4, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,3943,3966)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,4):", $t6} $t6 == $t6;
        goto L3;
    }

    // $t7 := borrow_field<0x42::prover_basics::Wallet>.balance($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:155:9+14
    $t7 := $ChildMutation($t0, 0, $Dereference($t0)->$balance);

    // write_ref($t7, $t5) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:155:9+40
    $t7 := $UpdateMutation($t7, $t5);

    // write_back[Reference($t0).balance (u64)]($t7) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:155:9+40
    $t0 := $UpdateMutation($t0, $Update'$42_prover_basics_Wallet'_balance($Dereference($t0), $Dereference($t7)));

    // trace_local[wallet]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:155:9+40
    $temp_0'$42_prover_basics_Wallet' := $Dereference($t0);
    assume {:print "$track_local(1,4,0):", $temp_0'$42_prover_basics_Wallet'} $temp_0'$42_prover_basics_Wallet' == $temp_0'$42_prover_basics_Wallet';

    // trace_local[wallet]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:153:58+96
    assume {:print "$at(2,3878,3974)"} true;
    $temp_0'$42_prover_basics_Wallet' := $Dereference($t0);
    assume {:print "$track_local(1,4,0):", $temp_0'$42_prover_basics_Wallet'} $temp_0'$42_prover_basics_Wallet' == $temp_0'$42_prover_basics_Wallet';

    // goto L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:153:58+96
    goto L2;

    // label L0 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:154:9+6
    assume {:print "$at(2,3889,3895)"} true;
L0:

    // drop($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:154:9+6
    assume {:print "$at(2,3889,3895)"} true;

    // $t8 := 4 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:154:33+1
    $t8 := 4;
    assume $IsValid'u64'($t8);

    // trace_abort($t8) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:154:9+6
    assume {:print "$at(2,3889,3895)"} true;
    assume {:print "$track_abort(1,4):", $t8} $t8 == $t8;

    // $t6 := move($t8) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:154:9+6
    $t6 := $t8;

    // goto L3 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:154:9+6
    goto L3;

    // label L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:156:5+1
    assume {:print "$at(2,3973,3974)"} true;
L2:

    // assert Not(false) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:163:9+16
    assume {:print "$at(2,4213,4229)"} true;
    assert {:msg "assert_failed(2,4213,4229): function does not abort under this condition"}
      !false;

    // assert Eq<u64>(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t0), Add(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t2), $t1)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:161:9+55
    assume {:print "$at(2,4094,4149)"} true;
    assert {:msg "assert_failed(2,4094,4149): post-condition does not hold"}
      $IsEqual'u64'($Dereference($t0)->$balance, ($t2->$balance + $t1));

    // assert Eq<bool>(select prover_basics::Wallet.frozen<0x42::prover_basics::Wallet>($t0), select prover_basics::Wallet.frozen<0x42::prover_basics::Wallet>($t2)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:162:9+44
    assume {:print "$at(2,4159,4203)"} true;
    assert {:msg "assert_failed(2,4159,4203): post-condition does not hold"}
      $IsEqual'bool'($Dereference($t0)->$frozen, $t2->$frozen);

    // return () at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:162:9+44
    $ret0 := $t0;
    return;

    // label L3 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:156:5+1
    assume {:print "$at(2,3973,3974)"} true;
L3:

    // assert false at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:158:5+254
    assume {:print "$at(2,3982,4236)"} true;
    assert {:msg "assert_failed(2,3982,4236): abort not covered by any of the `aborts_if` clauses"}
      false;

    // abort($t6) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:158:5+254
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun prover_basics::max [verification] at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:54:5+73
procedure {:timeLimit 40} $42_prover_basics_max$verify(_$t0: int, _$t1: int) returns ($ret0: int)
{
    // declare local variables
    var $t2: int;
    var $t3: bool;
    var $t0: int;
    var $t1: int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:54:5+1
    assume {:print "$at(2,1306,1307)"} true;
    assume $IsValid'u64'($t0);

    // assume WellFormed($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:54:5+1
    assume $IsValid'u64'($t1);

    // trace_local[a]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:54:5+1
    assume {:print "$track_local(1,5,0):", $t0} $t0 == $t0;

    // trace_local[b]($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:54:5+1
    assume {:print "$track_local(1,5,1):", $t1} $t1 == $t1;

    // $t3 := >($t0, $t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:55:13+5
    assume {:print "$at(2,1357,1362)"} true;
    call $t3 := $Gt($t0, $t1);

    // if ($t3) goto L1 else goto L0 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:55:9+19
    if ($t3) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:55:20+1
L1:

    // $t2 := $t0 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:55:20+1
    assume {:print "$at(2,1364,1365)"} true;
    $t2 := $t0;

    // trace_local[$t4]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:55:20+1
    assume {:print "$track_local(1,5,2):", $t0} $t0 == $t0;

    // label L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:55:9+19
L2:

    // trace_return[0]($t2) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:55:9+19
    assume {:print "$at(2,1353,1372)"} true;
    assume {:print "$track_return(1,5,0):", $t2} $t2 == $t2;

    // goto L3 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:55:9+19
    goto L3;

    // label L0 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:55:27+1
L0:

    // $t2 := $t1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:55:27+1
    assume {:print "$at(2,1371,1372)"} true;
    $t2 := $t1;

    // trace_local[$t4]($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:55:27+1
    assume {:print "$track_local(1,5,2):", $t1} $t1 == $t1;

    // goto L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:55:27+1
    goto L2;

    // label L3 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:56:5+1
    assume {:print "$at(2,1378,1379)"} true;
L3:

    // assert Not(false) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:63:9+16
    assume {:print "$at(2,1582,1598)"} true;
    assert {:msg "assert_failed(2,1582,1598): function does not abort under this condition"}
      !false;

    // assert And(Ge($t2, $t0), Ge($t2, $t1)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:59:9+35
    assume {:print "$at(2,1407,1442)"} true;
    assert {:msg "assert_failed(2,1407,1442): post-condition does not hold"}
      (($t2 >= $t0) && ($t2 >= $t1));

    // assert Or(Eq<u64>($t2, $t0), Eq<u64>($t2, $t1)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:60:9+35
    assume {:print "$at(2,1452,1487)"} true;
    assert {:msg "assert_failed(2,1452,1487): post-condition does not hold"}
      ($IsEqual'u64'($t2, $t0) || $IsEqual'u64'($t2, $t1));

    // assert Implies(Gt($t0, $t1), Eq<u64>($t2, $t0)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:61:9+32
    assume {:print "$at(2,1497,1529)"} true;
    assert {:msg "assert_failed(2,1497,1529): post-condition does not hold"}
      (($t0 > $t1) ==> $IsEqual'u64'($t2, $t0));

    // assert Implies(Le($t0, $t1), Eq<u64>($t2, $t1)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:62:9+33
    assume {:print "$at(2,1539,1572)"} true;
    assert {:msg "assert_failed(2,1539,1572): post-condition does not hold"}
      (($t0 <= $t1) ==> $IsEqual'u64'($t2, $t1));

    // return $t2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:62:9+33
    $ret0 := $t2;
    return;

}

// fun prover_basics::merge_coins [verification] at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:107:5+157
procedure {:timeLimit 40} $42_prover_basics_merge_coins$verify(_$t0: $Mutation ($42_prover_basics_Coin), _$t1: $42_prover_basics_Coin) returns ($ret0: $Mutation ($42_prover_basics_Coin))
{
    // declare local variables
    var $t2: $42_prover_basics_Coin;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: $Mutation (int);
    var $t0: $Mutation ($42_prover_basics_Coin);
    var $t1: $42_prover_basics_Coin;
    var $temp_0'$42_prover_basics_Coin': $42_prover_basics_Coin;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();
    assume $t0->l == $Param(0);

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:107:5+1
    assume {:print "$at(2,2689,2690)"} true;
    assume $IsValid'$42_prover_basics_Coin'($Dereference($t0));

    // assume WellFormed($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:107:5+1
    assume $IsValid'$42_prover_basics_Coin'($t1);

    // assume Le(Add(select prover_basics::Coin.value<0x42::prover_basics::Coin>($t0), select prover_basics::Coin.value<0x42::prover_basics::Coin>($t1)), 18446744073709551615) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:114:9+46
    assume {:print "$at(2,2946,2992)"} true;
    assume (($Dereference($t0)->$value + $t1->$value) <= 18446744073709551615);

    // $t2 := read_ref($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:114:9+46
    $t2 := $Dereference($t0);

    // trace_local[coin1]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:107:5+1
    assume {:print "$at(2,2689,2690)"} true;
    $temp_0'$42_prover_basics_Coin' := $Dereference($t0);
    assume {:print "$track_local(1,6,0):", $temp_0'$42_prover_basics_Coin'} $temp_0'$42_prover_basics_Coin' == $temp_0'$42_prover_basics_Coin';

    // trace_local[coin2]($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:107:5+1
    assume {:print "$track_local(1,6,1):", $t1} $t1 == $t1;

    // $t3 := get_field<0x42::prover_basics::Coin>.value($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:108:23+11
    assume {:print "$at(2,2768,2779)"} true;
    $t3 := $Dereference($t0)->$value;

    // $t4 := get_field<0x42::prover_basics::Coin>.value($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:108:37+11
    $t4 := $t1->$value;

    // $t5 := +($t3, $t4) on_abort goto L2 with $t6 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:108:23+25
    call $t5 := $AddU64($t3, $t4);
    if ($abort_flag) {
        assume {:print "$at(2,2768,2793)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,6):", $t6} $t6 == $t6;
        goto L2;
    }

    // $t7 := borrow_field<0x42::prover_basics::Coin>.value($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:108:9+11
    $t7 := $ChildMutation($t0, 0, $Dereference($t0)->$value);

    // write_ref($t7, $t5) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:108:9+39
    $t7 := $UpdateMutation($t7, $t5);

    // write_back[Reference($t0).value (u64)]($t7) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:108:9+39
    $t0 := $UpdateMutation($t0, $Update'$42_prover_basics_Coin'_value($Dereference($t0), $Dereference($t7)));

    // trace_local[coin1]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:108:9+39
    $temp_0'$42_prover_basics_Coin' := $Dereference($t0);
    assume {:print "$track_local(1,6,0):", $temp_0'$42_prover_basics_Coin'} $temp_0'$42_prover_basics_Coin' == $temp_0'$42_prover_basics_Coin';

    // trace_local[coin1]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:107:59+103
    assume {:print "$at(2,2743,2846)"} true;
    $temp_0'$42_prover_basics_Coin' := $Dereference($t0);
    assume {:print "$track_local(1,6,0):", $temp_0'$42_prover_basics_Coin'} $temp_0'$42_prover_basics_Coin' == $temp_0'$42_prover_basics_Coin';

    // label L1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:110:5+1
    assume {:print "$at(2,2845,2846)"} true;
L1:

    // assert Not(false) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:115:9+16
    assume {:print "$at(2,3002,3018)"} true;
    assert {:msg "assert_failed(2,3002,3018): function does not abort under this condition"}
      !false;

    // assert Eq<u64>(select prover_basics::Coin.value<0x42::prover_basics::Coin>($t0), Add(select prover_basics::Coin.value<0x42::prover_basics::Coin>($t2), select prover_basics::Coin.value<0x42::prover_basics::Coin>($t1))) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:113:9+54
    assume {:print "$at(2,2882,2936)"} true;
    assert {:msg "assert_failed(2,2882,2936): post-condition does not hold"}
      $IsEqual'u64'($Dereference($t0)->$value, ($t2->$value + $t1->$value));

    // return () at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:113:9+54
    $ret0 := $t0;
    return;

    // label L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:110:5+1
    assume {:print "$at(2,2845,2846)"} true;
L2:

    // assert false at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:112:5+171
    assume {:print "$at(2,2854,3025)"} true;
    assert {:msg "assert_failed(2,2854,3025): abort not covered by any of the `aborts_if` clauses"}
      false;

    // abort($t6) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:112:5+171
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun prover_basics::mint_coin [verification] at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:76:5+71
procedure {:timeLimit 40} $42_prover_basics_mint_coin$verify(_$t0: int) returns ($ret0: $42_prover_basics_Coin)
{
    // declare local variables
    var $t1: $42_prover_basics_Coin;
    var $t0: int;
    var $temp_0'$42_prover_basics_Coin': $42_prover_basics_Coin;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:76:5+1
    assume {:print "$at(2,1864,1865)"} true;
    assume $IsValid'u64'($t0);

    // trace_local[value]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:76:5+1
    assume {:print "$track_local(1,7,0):", $t0} $t0 == $t0;

    // $t1 := pack 0x42::prover_basics::Coin($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:77:9+14
    assume {:print "$at(2,1914,1928)"} true;
    $t1 := $42_prover_basics_Coin($t0);

    // trace_return[0]($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:77:9+14
    assume {:print "$track_return(1,7,0):", $t1} $t1 == $t1;

    // label L1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:78:5+1
    assume {:print "$at(2,1934,1935)"} true;
L1:

    // assert Not(false) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:82:9+16
    assume {:print "$at(2,2009,2025)"} true;
    assert {:msg "assert_failed(2,2009,2025): function does not abort under this condition"}
      !false;

    // assert Eq<u64>(select prover_basics::Coin.value<0x42::prover_basics::Coin>($t1), $t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:81:9+30
    assume {:print "$at(2,1969,1999)"} true;
    assert {:msg "assert_failed(2,1969,1999): post-condition does not hold"}
      $IsEqual'u64'($t1->$value, $t0);

    // return $t1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:81:9+30
    $ret0 := $t1;
    return;

}

// fun prover_basics::percentage [baseline] at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:211:5+154
procedure {:inline 1} $42_prover_basics_percentage(_$t0: int, _$t1: int) returns ($ret0: int)
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t0: int;
    var $t1: int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // assume Le($t0, Div(18446744073709551615, Add($t1, 1))) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:221:9+42
    assume {:print "$at(2,6137,6179)"} true;
    assume ($t0 <= (18446744073709551615 div ($t1 + 1)));

    // trace_local[value]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:211:5+1
    assume {:print "$at(2,5710,5711)"} true;
    assume {:print "$track_local(1,8,0):", $t0} $t0 == $t0;

    // trace_local[percent]($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:211:5+1
    assume {:print "$track_local(1,8,1):", $t1} $t1 == $t1;

    // $t2 := *($t0, $t1) on_abort goto L2 with $t3 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:213:9+17
    assume {:print "$at(2,5832,5849)"} true;
    call $t2 := $MulU64($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,5832,5849)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(1,8):", $t3} $t3 == $t3;
        goto L2;
    }

    // $t4 := 10000 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:213:29+5
    $t4 := 10000;
    assume $IsValid'u64'($t4);

    // $t5 := /($t2, $t4) on_abort goto L2 with $t3 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:213:9+25
    call $t5 := $Div($t2, $t4);
    if ($abort_flag) {
        assume {:print "$at(2,5832,5857)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(1,8):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t5) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:213:9+25
    assume {:print "$track_return(1,8,0):", $t5} $t5 == $t5;

    // label L1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:214:5+1
    assume {:print "$at(2,5863,5864)"} true;
L1:

    // return $t5 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:214:5+1
    assume {:print "$at(2,5863,5864)"} true;
    $ret0 := $t5;
    return;

    // label L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:214:5+1
L2:

    // abort($t3) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:214:5+1
    assume {:print "$at(2,5863,5864)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun prover_basics::percentage [verification] at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:211:5+154
procedure {:timeLimit 40} $42_prover_basics_percentage$verify(_$t0: int, _$t1: int) returns ($ret0: int)
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t0: int;
    var $t1: int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:211:5+1
    assume {:print "$at(2,5710,5711)"} true;
    assume $IsValid'u64'($t0);

    // assume WellFormed($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:211:5+1
    assume $IsValid'u64'($t1);

    // assume Le($t0, Div(18446744073709551615, Add($t1, 1))) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:221:9+42
    assume {:print "$at(2,6137,6179)"} true;
    assume ($t0 <= (18446744073709551615 div ($t1 + 1)));

    // trace_local[value]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:211:5+1
    assume {:print "$at(2,5710,5711)"} true;
    assume {:print "$track_local(1,8,0):", $t0} $t0 == $t0;

    // trace_local[percent]($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:211:5+1
    assume {:print "$track_local(1,8,1):", $t1} $t1 == $t1;

    // $t2 := *($t0, $t1) on_abort goto L2 with $t3 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:213:9+17
    assume {:print "$at(2,5832,5849)"} true;
    call $t2 := $MulU64($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,5832,5849)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(1,8):", $t3} $t3 == $t3;
        goto L2;
    }

    // $t4 := 10000 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:213:29+5
    $t4 := 10000;
    assume $IsValid'u64'($t4);

    // $t5 := /($t2, $t4) on_abort goto L2 with $t3 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:213:9+25
    call $t5 := $Div($t2, $t4);
    if ($abort_flag) {
        assume {:print "$at(2,5832,5857)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(1,8):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t5) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:213:9+25
    assume {:print "$track_return(1,8,0):", $t5} $t5 == $t5;

    // label L1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:214:5+1
    assume {:print "$at(2,5863,5864)"} true;
L1:

    // assert Not(false) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:222:9+16
    assume {:print "$at(2,6189,6205)"} true;
    assert {:msg "assert_failed(2,6189,6205): function does not abort under this condition"}
      !false;

    // assert Implies(Eq<u64>($t1, 0), Eq<u64>($t5, 0)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:218:9+37
    assume {:print "$at(2,5980,6017)"} true;
    assert {:msg "assert_failed(2,5980,6017): post-condition does not hold"}
      ($IsEqual'u64'($t1, 0) ==> $IsEqual'u64'($t5, 0));

    // assert Implies(Ge($t1, 10000), Ge($t5, $t0)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:219:9+45
    assume {:print "$at(2,6027,6072)"} true;
    assert {:msg "assert_failed(2,6027,6072): post-condition does not hold"}
      (($t1 >= 10000) ==> ($t5 >= $t0));

    // assert Implies(Le($t1, 10000), Le($t5, $t0)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:220:9+45
    assume {:print "$at(2,6082,6127)"} true;
    assert {:msg "assert_failed(2,6082,6127): post-condition does not hold"}
      (($t1 <= 10000) ==> ($t5 <= $t0));

    // return $t5 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:220:9+45
    $ret0 := $t5;
    return;

    // label L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:214:5+1
    assume {:print "$at(2,5863,5864)"} true;
L2:

    // assert false at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:216:5+340
    assume {:print "$at(2,5872,6212)"} true;
    assert {:msg "assert_failed(2,5872,6212): abort not covered by any of the `aborts_if` clauses"}
      false;

    // abort($t3) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:216:5+340
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun prover_basics::safe_mul [verification] at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:37:5+188
procedure {:timeLimit 40} $42_prover_basics_safe_mul$verify(_$t0: int, _$t1: int) returns ($ret0: int)
{
    // declare local variables
    var $t2: bool;
    var $t3: int;
    var $t4: int;
    var $t5: bool;
    var $t6: bool;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: int;
    var $t11: bool;
    var $t12: int;
    var $t13: int;
    var $t14: int;
    var $t15: bool;
    var $t0: int;
    var $t1: int;
    var $temp_0'bool': bool;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:37:5+1
    assume {:print "$at(2,879,880)"} true;
    assume $IsValid'u64'($t0);

    // assume WellFormed($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:37:5+1
    assume $IsValid'u64'($t1);

    // assume Or(Or(Eq<u64>($t0, 0), Eq<u64>($t1, 0)), Le($t0, Div(18446744073709551615, $t1))) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:49:9+46
    assume {:print "$at(2,1187,1233)"} true;
    assume (($IsEqual'u64'($t0, 0) || $IsEqual'u64'($t1, 0)) || ($t0 <= (18446744073709551615 div $t1)));

    // trace_local[a]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:37:5+1
    assume {:print "$at(2,879,880)"} true;
    assume {:print "$track_local(1,9,0):", $t0} $t0 == $t0;

    // trace_local[b]($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:37:5+1
    assume {:print "$track_local(1,9,1):", $t1} $t1 == $t1;

    // $t4 := 0 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:38:18+1
    assume {:print "$at(2,940,941)"} true;
    $t4 := 0;
    assume $IsValid'u64'($t4);

    // $t5 := ==($t0, $t4) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:38:13+6
    $t5 := $IsEqual'u64'($t0, $t4);

    // if ($t5) goto L1 else goto L0 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:38:13+16
    if ($t5) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:38:13+16
L1:

    // $t6 := true at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:38:13+16
    assume {:print "$at(2,935,951)"} true;
    $t6 := true;
    assume $IsValid'bool'($t6);

    // $t2 := $t6 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:38:13+16
    $t2 := $t6;

    // trace_local[$t4]($t6) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:38:13+16
    assume {:print "$track_local(1,9,2):", $t6} $t6 == $t6;

    // label L7 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:38:9+129
L7:

    // if ($t2) goto L3 else goto L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:38:9+129
    assume {:print "$at(2,931,1060)"} true;
    if ($t2) { goto L3; } else { goto L2; }

    // label L3 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:39:13+1
    assume {:print "$at(2,968,969)"} true;
L3:

    // $t7 := 0 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:39:13+1
    assume {:print "$at(2,968,969)"} true;
    $t7 := 0;
    assume $IsValid'u64'($t7);

    // $t3 := $t7 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:39:13+1
    $t3 := $t7;

    // trace_local[$t5]($t7) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:39:13+1
    assume {:print "$track_local(1,9,3):", $t7} $t7 == $t7;

    // label L6 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:38:9+129
    assume {:print "$at(2,931,1060)"} true;
L6:

    // trace_return[0]($t3) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:38:9+129
    assume {:print "$at(2,931,1060)"} true;
    assume {:print "$track_return(1,9,0):", $t3} $t3 == $t3;

    // goto L8 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:38:9+129
    goto L8;

    // label L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:41:21+1
    assume {:print "$at(2,1009,1010)"} true;
L2:

    // $t8 := 18446744073709551615 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:41:26+7
    assume {:print "$at(2,1014,1021)"} true;
    $t8 := 18446744073709551615;
    assume $IsValid'u64'($t8);

    // $t9 := /($t8, $t1) on_abort goto L9 with $t10 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:41:26+11
    call $t9 := $Div($t8, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,1014,1025)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(1,9):", $t10} $t10 == $t10;
        goto L9;
    }

    // $t11 := <=($t0, $t9) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:41:21+16
    call $t11 := $Le($t0, $t9);

    // if ($t11) goto L5 else goto L4 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:41:13+6
    if ($t11) { goto L5; } else { goto L4; }

    // label L5 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:42:13+1
    assume {:print "$at(2,1044,1045)"} true;
L5:

    // $t12 := *($t0, $t1) on_abort goto L9 with $t10 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:42:13+5
    assume {:print "$at(2,1044,1049)"} true;
    call $t12 := $MulU64($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,1044,1049)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(1,9):", $t10} $t10 == $t10;
        goto L9;
    }

    // $t3 := $t12 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:42:13+5
    $t3 := $t12;

    // trace_local[$t5]($t12) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:42:13+5
    assume {:print "$track_local(1,9,3):", $t12} $t12 == $t12;

    // goto L6 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:42:13+5
    goto L6;

    // label L4 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:41:39+1
    assume {:print "$at(2,1027,1028)"} true;
L4:

    // $t13 := 2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:41:39+1
    assume {:print "$at(2,1027,1028)"} true;
    $t13 := 2;
    assume $IsValid'u64'($t13);

    // trace_abort($t13) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:41:13+6
    assume {:print "$at(2,1001,1007)"} true;
    assume {:print "$track_abort(1,9):", $t13} $t13 == $t13;

    // $t10 := move($t13) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:41:13+6
    $t10 := $t13;

    // goto L9 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:41:13+6
    goto L9;

    // label L0 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:38:23+1
    assume {:print "$at(2,945,946)"} true;
L0:

    // $t14 := 0 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:38:28+1
    assume {:print "$at(2,950,951)"} true;
    $t14 := 0;
    assume $IsValid'u64'($t14);

    // $t15 := ==($t1, $t14) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:38:23+6
    $t15 := $IsEqual'u64'($t1, $t14);

    // $t2 := $t15 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:38:23+6
    $t2 := $t15;

    // trace_local[$t4]($t15) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:38:23+6
    assume {:print "$track_local(1,9,2):", $t15} $t15 == $t15;

    // goto L7 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:38:23+6
    goto L7;

    // label L8 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:44:5+1
    assume {:print "$at(2,1066,1067)"} true;
L8:

    // assert Not(false) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:50:9+16
    assume {:print "$at(2,1243,1259)"} true;
    assert {:msg "assert_failed(2,1243,1259): function does not abort under this condition"}
      !false;

    // assert Eq<u64>($t3, Mul($t0, $t1)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:47:9+24
    assume {:print "$at(2,1100,1124)"} true;
    assert {:msg "assert_failed(2,1100,1124): post-condition does not hold"}
      $IsEqual'u64'($t3, ($t0 * $t1));

    // assert Implies(Or(Eq<u64>($t0, 0), Eq<u64>($t1, 0)), Eq<u64>($t3, 0)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:48:9+43
    assume {:print "$at(2,1134,1177)"} true;
    assert {:msg "assert_failed(2,1134,1177): post-condition does not hold"}
      (($IsEqual'u64'($t0, 0) || $IsEqual'u64'($t1, 0)) ==> $IsEqual'u64'($t3, 0));

    // return $t3 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:48:9+43
    $ret0 := $t3;
    return;

    // label L9 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:44:5+1
    assume {:print "$at(2,1066,1067)"} true;
L9:

    // assert false at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:46:5+191
    assume {:print "$at(2,1075,1266)"} true;
    assert {:msg "assert_failed(2,1075,1266): abort not covered by any of the `aborts_if` clauses"}
      false;

    // abort($t10) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:46:5+191
    $abort_code := $t10;
    $abort_flag := true;
    return;

}

// fun prover_basics::safe_sub [verification] at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:25:5+93
procedure {:timeLimit 40} $42_prover_basics_safe_sub$verify(_$t0: int, _$t1: int) returns ($ret0: int)
{
    // declare local variables
    var $t2: bool;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t0: int;
    var $t1: int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:25:5+1
    assume {:print "$at(2,613,614)"} true;
    assume $IsValid'u64'($t0);

    // assume WellFormed($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:25:5+1
    assume $IsValid'u64'($t1);

    // assume Ge($t0, $t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:31:9+16
    assume {:print "$at(2,739,755)"} true;
    assume ($t0 >= $t1);

    // trace_local[a]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:25:5+1
    assume {:print "$at(2,613,614)"} true;
    assume {:print "$track_local(1,10,0):", $t0} $t0 == $t0;

    // trace_local[b]($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:25:5+1
    assume {:print "$track_local(1,10,1):", $t1} $t1 == $t1;

    // $t2 := >=($t0, $t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:26:17+6
    assume {:print "$at(2,673,679)"} true;
    call $t2 := $Ge($t0, $t1);

    // if ($t2) goto L1 else goto L0 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:26:9+6
    if ($t2) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:27:9+1
    assume {:print "$at(2,694,695)"} true;
L1:

    // $t3 := -($t0, $t1) on_abort goto L3 with $t4 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:27:9+5
    assume {:print "$at(2,694,699)"} true;
    call $t3 := $Sub($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,694,699)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(1,10):", $t4} $t4 == $t4;
        goto L3;
    }

    // trace_return[0]($t3) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:25:46+52
    assume {:print "$at(2,654,706)"} true;
    assume {:print "$track_return(1,10,0):", $t3} $t3 == $t3;

    // goto L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:25:46+52
    goto L2;

    // label L0 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:26:25+1
    assume {:print "$at(2,681,682)"} true;
L0:

    // $t5 := 1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:26:25+1
    assume {:print "$at(2,681,682)"} true;
    $t5 := 1;
    assume $IsValid'u64'($t5);

    // trace_abort($t5) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:26:9+6
    assume {:print "$at(2,665,671)"} true;
    assume {:print "$track_abort(1,10):", $t5} $t5 == $t5;

    // $t4 := move($t5) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:26:9+6
    $t4 := $t5;

    // goto L3 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:26:9+6
    goto L3;

    // label L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:28:5+1
    assume {:print "$at(2,705,706)"} true;
L2:

    // assert Not(false) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:33:9+16
    assume {:print "$at(2,799,815)"} true;
    assert {:msg "assert_failed(2,799,815): function does not abort under this condition"}
      !false;

    // assert Eq<u64>($t3, Sub($t0, $t1)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:32:9+24
    assume {:print "$at(2,765,789)"} true;
    assert {:msg "assert_failed(2,765,789): post-condition does not hold"}
      $IsEqual'u64'($t3, ($t0 - $t1));

    // return $t3 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:32:9+24
    $ret0 := $t3;
    return;

    // label L3 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:28:5+1
    assume {:print "$at(2,705,706)"} true;
L3:

    // assert false at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:30:5+108
    assume {:print "$at(2,714,822)"} true;
    assert {:msg "assert_failed(2,714,822): abort not covered by any of the `aborts_if` clauses"}
      false;

    // abort($t4) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:30:5+108
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun prover_basics::simple_interest [verification] at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:226:5+205
procedure {:timeLimit 40} $42_prover_basics_simple_interest$verify(_$t0: int, _$t1: int, _$t2: int) returns ($ret0: int)
{
    // declare local variables
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:226:5+1
    assume {:print "$at(2,6257,6258)"} true;
    assume $IsValid'u64'($t0);

    // assume WellFormed($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:226:5+1
    assume $IsValid'u64'($t1);

    // assume WellFormed($t2) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:226:5+1
    assume $IsValid'u64'($t2);

    // assume Le($t0, Div(18446744073709551615, Add($t2, 1))) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:236:9+43
    assume {:print "$at(2,6722,6765)"} true;
    assume ($t0 <= (18446744073709551615 div ($t2 + 1)));

    // assume Le(Mul($t0, $t2), Div(18446744073709551615, Add($t1, 1))) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:237:9+52
    assume {:print "$at(2,6775,6827)"} true;
    assume (($t0 * $t2) <= (18446744073709551615 div ($t1 + 1)));

    // trace_local[principal]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:226:5+1
    assume {:print "$at(2,6257,6258)"} true;
    assume {:print "$track_local(1,11,0):", $t0} $t0 == $t0;

    // trace_local[rate]($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:226:5+1
    assume {:print "$track_local(1,11,1):", $t1} $t1 == $t1;

    // trace_local[time]($t2) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:226:5+1
    assume {:print "$track_local(1,11,2):", $t2} $t2 == $t2;

    // $t3 := *($t0, $t2) on_abort goto L2 with $t4 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:229:20+16
    assume {:print "$at(2,6432,6448)"} true;
    call $t3 := $MulU64($t0, $t2);
    if ($abort_flag) {
        assume {:print "$at(2,6432,6448)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(1,11):", $t4} $t4 == $t4;
        goto L2;
    }

    // assert Le($t3, Div(18446744073709551615, Add($t1, 1))) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:221:9+42
    assume {:print "$at(2,6137,6179)"} true;
    assert {:msg "assert_failed(2,6137,6179): precondition does not hold at this call"}
      ($t3 <= (18446744073709551615 div ($t1 + 1)));

    // $t5 := prover_basics::percentage($t3, $t1) on_abort goto L2 with $t4 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:229:9+34
    assume {:print "$at(2,6421,6455)"} true;
    call $t5 := $42_prover_basics_percentage($t3, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,6421,6455)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(1,11):", $t4} $t4 == $t4;
        goto L2;
    }

    // trace_return[0]($t5) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:229:9+34
    assume {:print "$track_return(1,11,0):", $t5} $t5 == $t5;

    // label L1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:230:5+1
    assume {:print "$at(2,6461,6462)"} true;
L1:

    // assert Not(false) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:238:9+16
    assume {:print "$at(2,6837,6853)"} true;
    assert {:msg "assert_failed(2,6837,6853): function does not abort under this condition"}
      !false;

    // assert Implies(Or(Or(Eq<u64>($t0, 0), Eq<u64>($t1, 0)), Eq<u64>($t2, 0)), Eq<u64>($t5, 0)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:233:9+67
    assume {:print "$at(2,6502,6569)"} true;
    assert {:msg "assert_failed(2,6502,6569): post-condition does not hold"}
      ((($IsEqual'u64'($t0, 0) || $IsEqual'u64'($t1, 0)) || $IsEqual'u64'($t2, 0)) ==> $IsEqual'u64'($t5, 0));

    // assert Implies(Le($t1, 10000), Le($t5, Mul($t0, $t2))) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:235:9+53
    assume {:print "$at(2,6659,6712)"} true;
    assert {:msg "assert_failed(2,6659,6712): post-condition does not hold"}
      (($t1 <= 10000) ==> ($t5 <= ($t0 * $t2)));

    // return $t5 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:235:9+53
    $ret0 := $t5;
    return;

    // label L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:230:5+1
    assume {:print "$at(2,6461,6462)"} true;
L2:

    // assert false at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:232:5+390
    assume {:print "$at(2,6470,6860)"} true;
    assert {:msg "assert_failed(2,6470,6860): abort not covered by any of the `aborts_if` clauses"}
      false;

    // abort($t4) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:232:5+390
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun prover_basics::split_coin [verification] at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:86:5+184
procedure {:timeLimit 40} $42_prover_basics_split_coin$verify(_$t0: $Mutation ($42_prover_basics_Coin), _$t1: int) returns ($ret0: $42_prover_basics_Coin, $ret1: $Mutation ($42_prover_basics_Coin))
{
    // declare local variables
    var $t2: $42_prover_basics_Coin;
    var $t3: int;
    var $t4: bool;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: $Mutation (int);
    var $t9: $42_prover_basics_Coin;
    var $t10: int;
    var $t0: $Mutation ($42_prover_basics_Coin);
    var $t1: int;
    var $temp_0'$42_prover_basics_Coin': $42_prover_basics_Coin;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();
    assume $t0->l == $Param(0);

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:86:5+1
    assume {:print "$at(2,2075,2076)"} true;
    assume $IsValid'$42_prover_basics_Coin'($Dereference($t0));

    // assume WellFormed($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:86:5+1
    assume $IsValid'u64'($t1);

    // assume Ge(select prover_basics::Coin.value<0x42::prover_basics::Coin>($t0), $t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:101:9+30
    assume {:print "$at(2,2583,2613)"} true;
    assume ($Dereference($t0)->$value >= $t1);

    // $t2 := read_ref($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:101:9+30
    $t2 := $Dereference($t0);

    // trace_local[coin]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:86:5+1
    assume {:print "$at(2,2075,2076)"} true;
    $temp_0'$42_prover_basics_Coin' := $Dereference($t0);
    assume {:print "$track_local(1,12,0):", $temp_0'$42_prover_basics_Coin'} $temp_0'$42_prover_basics_Coin' == $temp_0'$42_prover_basics_Coin';

    // trace_local[amount]($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:86:5+1
    assume {:print "$track_local(1,12,1):", $t1} $t1 == $t1;

    // $t3 := get_field<0x42::prover_basics::Coin>.value($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:87:17+10
    assume {:print "$at(2,2152,2162)"} true;
    $t3 := $Dereference($t0)->$value;

    // $t4 := >=($t3, $t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:87:17+20
    call $t4 := $Ge($t3, $t1);

    // if ($t4) goto L1 else goto L0 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:87:9+6
    if ($t4) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:88:22+10
    assume {:print "$at(2,2200,2210)"} true;
L1:

    // $t5 := get_field<0x42::prover_basics::Coin>.value($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:88:22+10
    assume {:print "$at(2,2200,2210)"} true;
    $t5 := $Dereference($t0)->$value;

    // $t6 := -($t5, $t1) on_abort goto L3 with $t7 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:88:22+19
    call $t6 := $Sub($t5, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,2200,2219)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(1,12):", $t7} $t7 == $t7;
        goto L3;
    }

    // $t8 := borrow_field<0x42::prover_basics::Coin>.value($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:88:9+10
    $t8 := $ChildMutation($t0, 0, $Dereference($t0)->$value);

    // write_ref($t8, $t6) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:88:9+32
    $t8 := $UpdateMutation($t8, $t6);

    // write_back[Reference($t0).value (u64)]($t8) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:88:9+32
    $t0 := $UpdateMutation($t0, $Update'$42_prover_basics_Coin'_value($Dereference($t0), $Dereference($t8)));

    // trace_local[coin]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:88:9+32
    $temp_0'$42_prover_basics_Coin' := $Dereference($t0);
    assume {:print "$track_local(1,12,0):", $temp_0'$42_prover_basics_Coin'} $temp_0'$42_prover_basics_Coin' == $temp_0'$42_prover_basics_Coin';

    // $t9 := pack 0x42::prover_basics::Coin($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:89:9+22
    assume {:print "$at(2,2230,2252)"} true;
    $t9 := $42_prover_basics_Coin($t1);

    // trace_return[0]($t9) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:86:63+126
    assume {:print "$at(2,2133,2259)"} true;
    assume {:print "$track_return(1,12,0):", $t9} $t9 == $t9;

    // trace_local[coin]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:86:63+126
    $temp_0'$42_prover_basics_Coin' := $Dereference($t0);
    assume {:print "$track_local(1,12,0):", $temp_0'$42_prover_basics_Coin'} $temp_0'$42_prover_basics_Coin' == $temp_0'$42_prover_basics_Coin';

    // goto L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:86:63+126
    goto L2;

    // label L0 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:87:9+6
    assume {:print "$at(2,2144,2150)"} true;
L0:

    // drop($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:87:9+6
    assume {:print "$at(2,2144,2150)"} true;

    // $t10 := 3 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:87:39+1
    $t10 := 3;
    assume $IsValid'u64'($t10);

    // trace_abort($t10) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:87:9+6
    assume {:print "$at(2,2144,2150)"} true;
    assume {:print "$track_abort(1,12):", $t10} $t10 == $t10;

    // $t7 := move($t10) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:87:9+6
    $t7 := $t10;

    // goto L3 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:87:9+6
    goto L3;

    // label L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:90:5+1
    assume {:print "$at(2,2258,2259)"} true;
L2:

    // assert Not(false) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:103:9+16
    assume {:print "$at(2,2633,2649)"} true;
    assert {:msg "assert_failed(2,2633,2649): function does not abort under this condition"}
      !false;

    // assert Eq<num>(Add(select prover_basics::Coin.value<0x42::prover_basics::Coin>($t0), select prover_basics::Coin.value<0x42::prover_basics::Coin>($t9)), select prover_basics::Coin.value<0x42::prover_basics::Coin>($t2)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:94:9+53
    assume {:print "$at(2,2351,2404)"} true;
    assert {:msg "assert_failed(2,2351,2404): post-condition does not hold"}
      $IsEqual'num'(($Dereference($t0)->$value + $t9->$value), $t2->$value);

    // assert Eq<u64>(select prover_basics::Coin.value<0x42::prover_basics::Coin>($t9), $t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:97:9+31
    assume {:print "$at(2,2450,2481)"} true;
    assert {:msg "assert_failed(2,2450,2481): post-condition does not hold"}
      $IsEqual'u64'($t9->$value, $t1);

    // assert Eq<u64>(select prover_basics::Coin.value<0x42::prover_basics::Coin>($t0), Sub(select prover_basics::Coin.value<0x42::prover_basics::Coin>($t2), $t1)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:98:9+47
    assume {:print "$at(2,2491,2538)"} true;
    assert {:msg "assert_failed(2,2491,2538): post-condition does not hold"}
      $IsEqual'u64'($Dereference($t0)->$value, ($t2->$value - $t1));

    // return $t9 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:98:9+47
    $ret0 := $t9;
    $ret1 := $t0;
    return;

    // label L3 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:90:5+1
    assume {:print "$at(2,2258,2259)"} true;
L3:

    // assert false at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:92:5+389
    assume {:print "$at(2,2267,2656)"} true;
    assert {:msg "assert_failed(2,2267,2656): abort not covered by any of the `aborts_if` clauses"}
      false;

    // abort($t7) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:92:5+389
    $abort_code := $t7;
    $abort_flag := true;
    return;

}

// fun prover_basics::transfer [verification] at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:182:5+140
procedure {:timeLimit 40} $42_prover_basics_transfer$verify(_$t0: $Mutation ($42_prover_basics_Wallet), _$t1: $Mutation ($42_prover_basics_Wallet), _$t2: int) returns ($ret0: $Mutation ($42_prover_basics_Wallet), $ret1: $Mutation ($42_prover_basics_Wallet))
{
    // declare local variables
    var $t3: $42_prover_basics_Wallet;
    var $t4: $42_prover_basics_Wallet;
    var $t5: int;
    var $t0: $Mutation ($42_prover_basics_Wallet);
    var $t1: $Mutation ($42_prover_basics_Wallet);
    var $t2: int;
    var $temp_0'$42_prover_basics_Wallet': $42_prover_basics_Wallet;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();
    assume $t0->l == $Param(0);
    assume $t1->l == $Param(1);

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:182:5+1
    assume {:print "$at(2,4766,4767)"} true;
    assume $IsValid'$42_prover_basics_Wallet'($Dereference($t0));

    // assume WellFormed($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:182:5+1
    assume $IsValid'$42_prover_basics_Wallet'($Dereference($t1));

    // assume WellFormed($t2) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:182:5+1
    assume $IsValid'u64'($t2);

    // assume And(Not(select prover_basics::Wallet.frozen<0x42::prover_basics::Wallet>($t0)), Not(select prover_basics::Wallet.frozen<0x42::prover_basics::Wallet>($t1))) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:188:9+36
    assume {:print "$at(2,4939,4975)"} true;
    assume (!$Dereference($t0)->$frozen && !$Dereference($t1)->$frozen);

    // assume Ge(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t0), $t2) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:189:9+32
    assume {:print "$at(2,4985,5017)"} true;
    assume ($Dereference($t0)->$balance >= $t2);

    // assume Le(Add(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t1), $t2), 18446744073709551615) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:190:9+40
    assume {:print "$at(2,5027,5067)"} true;
    assume (($Dereference($t1)->$balance + $t2) <= 18446744073709551615);

    // $t3 := read_ref($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:190:9+40
    $t3 := $Dereference($t0);

    // $t4 := read_ref($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:190:9+40
    $t4 := $Dereference($t1);

    // trace_local[from]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:182:5+1
    assume {:print "$at(2,4766,4767)"} true;
    $temp_0'$42_prover_basics_Wallet' := $Dereference($t0);
    assume {:print "$track_local(1,13,0):", $temp_0'$42_prover_basics_Wallet'} $temp_0'$42_prover_basics_Wallet' == $temp_0'$42_prover_basics_Wallet';

    // trace_local[to]($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:182:5+1
    $temp_0'$42_prover_basics_Wallet' := $Dereference($t1);
    assume {:print "$track_local(1,13,1):", $temp_0'$42_prover_basics_Wallet'} $temp_0'$42_prover_basics_Wallet' == $temp_0'$42_prover_basics_Wallet';

    // trace_local[amount]($t2) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:182:5+1
    assume {:print "$track_local(1,13,2):", $t2} $t2 == $t2;

    // assert Not(select prover_basics::Wallet.frozen<0x42::prover_basics::Wallet>($t0)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:174:9+24
    assume {:print "$at(2,4504,4528)"} true;
    assert {:msg "assert_failed(2,4504,4528): precondition does not hold at this call"}
      !$Dereference($t0)->$frozen;

    // assert Ge(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t0), $t2) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:175:9+34
    assume {:print "$at(2,4538,4572)"} true;
    assert {:msg "assert_failed(2,4538,4572): precondition does not hold at this call"}
      ($Dereference($t0)->$balance >= $t2);

    // prover_basics::withdraw($t0, $t2) on_abort goto L2 with $t5 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:183:9+22
    assume {:print "$at(2,4846,4868)"} true;
    call $t0 := $42_prover_basics_withdraw($t0, $t2);
    if ($abort_flag) {
        assume {:print "$at(2,4846,4868)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(1,13):", $t5} $t5 == $t5;
        goto L2;
    }

    // assert Not(select prover_basics::Wallet.frozen<0x42::prover_basics::Wallet>($t1)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:159:9+24
    assume {:print "$at(2,4006,4030)"} true;
    assert {:msg "assert_failed(2,4006,4030): precondition does not hold at this call"}
      !$Dereference($t1)->$frozen;

    // assert Le(Add(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t1), $t2), 18446744073709551615) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:160:9+44
    assume {:print "$at(2,4040,4084)"} true;
    assert {:msg "assert_failed(2,4040,4084): precondition does not hold at this call"}
      (($Dereference($t1)->$balance + $t2) <= 18446744073709551615);

    // prover_basics::deposit($t1, $t2) on_abort goto L2 with $t5 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:184:9+19
    assume {:print "$at(2,4879,4898)"} true;
    call $t1 := $42_prover_basics_deposit($t1, $t2);
    if ($abort_flag) {
        assume {:print "$at(2,4879,4898)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(1,13):", $t5} $t5 == $t5;
        goto L2;
    }

    // trace_local[from]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:182:74+71
    assume {:print "$at(2,4835,4906)"} true;
    $temp_0'$42_prover_basics_Wallet' := $Dereference($t0);
    assume {:print "$track_local(1,13,0):", $temp_0'$42_prover_basics_Wallet'} $temp_0'$42_prover_basics_Wallet' == $temp_0'$42_prover_basics_Wallet';

    // trace_local[to]($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:182:74+71
    $temp_0'$42_prover_basics_Wallet' := $Dereference($t1);
    assume {:print "$track_local(1,13,1):", $temp_0'$42_prover_basics_Wallet'} $temp_0'$42_prover_basics_Wallet' == $temp_0'$42_prover_basics_Wallet';

    // label L1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:185:5+1
    assume {:print "$at(2,4905,4906)"} true;
L1:

    // assert Not(false) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:203:9+16
    assume {:print "$at(2,5513,5529)"} true;
    assert {:msg "assert_failed(2,5513,5529): function does not abort under this condition"}
      !false;

    // assert Eq<num>(Add(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t0), select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t1)), Add(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t3), select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t4))) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:193:9+73
    assume {:print "$at(2,5121,5194)"} true;
    assert {:msg "assert_failed(2,5121,5194): post-condition does not hold"}
      $IsEqual'num'(($Dereference($t0)->$balance + $Dereference($t1)->$balance), ($t3->$balance + $t4->$balance));

    // assert Eq<u64>(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t0), Sub(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t3), $t2)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:196:9+51
    assume {:print "$at(2,5243,5294)"} true;
    assert {:msg "assert_failed(2,5243,5294): post-condition does not hold"}
      $IsEqual'u64'($Dereference($t0)->$balance, ($t3->$balance - $t2));

    // assert Eq<u64>(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t1), Add(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t4), $t2)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:197:9+47
    assume {:print "$at(2,5304,5351)"} true;
    assert {:msg "assert_failed(2,5304,5351): post-condition does not hold"}
      $IsEqual'u64'($Dereference($t1)->$balance, ($t4->$balance + $t2));

    // assert Eq<bool>(select prover_basics::Wallet.frozen<0x42::prover_basics::Wallet>($t0), select prover_basics::Wallet.frozen<0x42::prover_basics::Wallet>($t3)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:200:9+40
    assume {:print "$at(2,5407,5447)"} true;
    assert {:msg "assert_failed(2,5407,5447): post-condition does not hold"}
      $IsEqual'bool'($Dereference($t0)->$frozen, $t3->$frozen);

    // assert Eq<bool>(select prover_basics::Wallet.frozen<0x42::prover_basics::Wallet>($t1), select prover_basics::Wallet.frozen<0x42::prover_basics::Wallet>($t4)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:201:9+36
    assume {:print "$at(2,5457,5493)"} true;
    assert {:msg "assert_failed(2,5457,5493): post-condition does not hold"}
      $IsEqual'bool'($Dereference($t1)->$frozen, $t4->$frozen);

    // return () at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:201:9+36
    $ret0 := $t0;
    $ret1 := $t1;
    return;

    // label L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:185:5+1
    assume {:print "$at(2,4905,4906)"} true;
L2:

    // assert false at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:187:5+622
    assume {:print "$at(2,4914,5536)"} true;
    assert {:msg "assert_failed(2,4914,5536): abort not covered by any of the `aborts_if` clauses"}
      false;

    // abort($t5) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:187:5+622
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun prover_basics::withdraw [baseline] at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:167:5+197
procedure {:inline 1} $42_prover_basics_withdraw(_$t0: $Mutation ($42_prover_basics_Wallet), _$t1: int) returns ($ret0: $Mutation ($42_prover_basics_Wallet))
{
    // declare local variables
    var $t2: bool;
    var $t3: int;
    var $t4: bool;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: $Mutation (int);
    var $t9: int;
    var $t10: int;
    var $t0: $Mutation ($42_prover_basics_Wallet);
    var $t1: int;
    var $temp_0'$42_prover_basics_Wallet': $42_prover_basics_Wallet;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // assume Not(select prover_basics::Wallet.frozen<0x42::prover_basics::Wallet>($t0)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:174:9+24
    assume {:print "$at(2,4504,4528)"} true;
    assume !$Dereference($t0)->$frozen;

    // assume Ge(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t0), $t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:175:9+34
    assume {:print "$at(2,4538,4572)"} true;
    assume ($Dereference($t0)->$balance >= $t1);

    // trace_local[wallet]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:167:5+1
    assume {:print "$at(2,4274,4275)"} true;
    $temp_0'$42_prover_basics_Wallet' := $Dereference($t0);
    assume {:print "$track_local(1,14,0):", $temp_0'$42_prover_basics_Wallet'} $temp_0'$42_prover_basics_Wallet' == $temp_0'$42_prover_basics_Wallet';

    // trace_local[amount]($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:167:5+1
    assume {:print "$track_local(1,14,1):", $t1} $t1 == $t1;

    // $t2 := get_field<0x42::prover_basics::Wallet>.frozen($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:168:18+13
    assume {:print "$at(2,4348,4361)"} true;
    $t2 := $Dereference($t0)->$frozen;

    // if ($t2) goto L0 else goto L1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:168:17+14
    if ($t2) { goto L0; } else { goto L1; }

    // label L1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:169:17+14
    assume {:print "$at(2,4384,4398)"} true;
L1:

    // $t3 := get_field<0x42::prover_basics::Wallet>.balance($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:169:17+14
    assume {:print "$at(2,4384,4398)"} true;
    $t3 := $Dereference($t0)->$balance;

    // $t4 := >=($t3, $t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:169:17+24
    call $t4 := $Ge($t3, $t1);

    // if ($t4) goto L3 else goto L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:169:9+6
    if ($t4) { goto L3; } else { goto L2; }

    // label L3 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:170:26+14
    assume {:print "$at(2,4440,4454)"} true;
L3:

    // $t5 := get_field<0x42::prover_basics::Wallet>.balance($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:170:26+14
    assume {:print "$at(2,4440,4454)"} true;
    $t5 := $Dereference($t0)->$balance;

    // $t6 := -($t5, $t1) on_abort goto L5 with $t7 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:170:26+23
    call $t6 := $Sub($t5, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,4440,4463)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(1,14):", $t7} $t7 == $t7;
        goto L5;
    }

    // $t8 := borrow_field<0x42::prover_basics::Wallet>.balance($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:170:9+14
    $t8 := $ChildMutation($t0, 0, $Dereference($t0)->$balance);

    // write_ref($t8, $t6) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:170:9+40
    $t8 := $UpdateMutation($t8, $t6);

    // write_back[Reference($t0).balance (u64)]($t8) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:170:9+40
    $t0 := $UpdateMutation($t0, $Update'$42_prover_basics_Wallet'_balance($Dereference($t0), $Dereference($t8)));

    // trace_local[wallet]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:170:9+40
    $temp_0'$42_prover_basics_Wallet' := $Dereference($t0);
    assume {:print "$track_local(1,14,0):", $temp_0'$42_prover_basics_Wallet'} $temp_0'$42_prover_basics_Wallet' == $temp_0'$42_prover_basics_Wallet';

    // trace_local[wallet]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:167:59+143
    assume {:print "$at(2,4328,4471)"} true;
    $temp_0'$42_prover_basics_Wallet' := $Dereference($t0);
    assume {:print "$track_local(1,14,0):", $temp_0'$42_prover_basics_Wallet'} $temp_0'$42_prover_basics_Wallet' == $temp_0'$42_prover_basics_Wallet';

    // goto L4 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:167:59+143
    goto L4;

    // label L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:169:9+6
    assume {:print "$at(2,4376,4382)"} true;
L2:

    // drop($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:169:9+6
    assume {:print "$at(2,4376,4382)"} true;

    // $t9 := 5 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:169:43+1
    $t9 := 5;
    assume $IsValid'u64'($t9);

    // trace_abort($t9) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:169:9+6
    assume {:print "$at(2,4376,4382)"} true;
    assume {:print "$track_abort(1,14):", $t9} $t9 == $t9;

    // $t7 := move($t9) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:169:9+6
    $t7 := $t9;

    // goto L5 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:169:9+6
    goto L5;

    // label L0 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:168:9+6
    assume {:print "$at(2,4339,4345)"} true;
L0:

    // drop($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:168:9+6
    assume {:print "$at(2,4339,4345)"} true;

    // $t10 := 4 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:168:33+1
    $t10 := 4;
    assume $IsValid'u64'($t10);

    // trace_abort($t10) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:168:9+6
    assume {:print "$at(2,4339,4345)"} true;
    assume {:print "$track_abort(1,14):", $t10} $t10 == $t10;

    // $t7 := move($t10) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:168:9+6
    $t7 := $t10;

    // goto L5 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:168:9+6
    goto L5;

    // label L4 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:171:5+1
    assume {:print "$at(2,4470,4471)"} true;
L4:

    // return () at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:171:5+1
    assume {:print "$at(2,4470,4471)"} true;
    $ret0 := $t0;
    return;

    // label L5 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:171:5+1
L5:

    // abort($t7) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:171:5+1
    assume {:print "$at(2,4470,4471)"} true;
    $abort_code := $t7;
    $abort_flag := true;
    return;

}

// fun prover_basics::withdraw [verification] at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:167:5+197
procedure {:timeLimit 40} $42_prover_basics_withdraw$verify(_$t0: $Mutation ($42_prover_basics_Wallet), _$t1: int) returns ($ret0: $Mutation ($42_prover_basics_Wallet))
{
    // declare local variables
    var $t2: $42_prover_basics_Wallet;
    var $t3: bool;
    var $t4: int;
    var $t5: bool;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: $Mutation (int);
    var $t10: int;
    var $t11: int;
    var $t0: $Mutation ($42_prover_basics_Wallet);
    var $t1: int;
    var $temp_0'$42_prover_basics_Wallet': $42_prover_basics_Wallet;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();
    assume $t0->l == $Param(0);

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:167:5+1
    assume {:print "$at(2,4274,4275)"} true;
    assume $IsValid'$42_prover_basics_Wallet'($Dereference($t0));

    // assume WellFormed($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:167:5+1
    assume $IsValid'u64'($t1);

    // assume Not(select prover_basics::Wallet.frozen<0x42::prover_basics::Wallet>($t0)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:174:9+24
    assume {:print "$at(2,4504,4528)"} true;
    assume !$Dereference($t0)->$frozen;

    // assume Ge(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t0), $t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:175:9+34
    assume {:print "$at(2,4538,4572)"} true;
    assume ($Dereference($t0)->$balance >= $t1);

    // $t2 := read_ref($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:175:9+34
    $t2 := $Dereference($t0);

    // trace_local[wallet]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:167:5+1
    assume {:print "$at(2,4274,4275)"} true;
    $temp_0'$42_prover_basics_Wallet' := $Dereference($t0);
    assume {:print "$track_local(1,14,0):", $temp_0'$42_prover_basics_Wallet'} $temp_0'$42_prover_basics_Wallet' == $temp_0'$42_prover_basics_Wallet';

    // trace_local[amount]($t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:167:5+1
    assume {:print "$track_local(1,14,1):", $t1} $t1 == $t1;

    // $t3 := get_field<0x42::prover_basics::Wallet>.frozen($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:168:18+13
    assume {:print "$at(2,4348,4361)"} true;
    $t3 := $Dereference($t0)->$frozen;

    // if ($t3) goto L0 else goto L1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:168:17+14
    if ($t3) { goto L0; } else { goto L1; }

    // label L1 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:169:17+14
    assume {:print "$at(2,4384,4398)"} true;
L1:

    // $t4 := get_field<0x42::prover_basics::Wallet>.balance($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:169:17+14
    assume {:print "$at(2,4384,4398)"} true;
    $t4 := $Dereference($t0)->$balance;

    // $t5 := >=($t4, $t1) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:169:17+24
    call $t5 := $Ge($t4, $t1);

    // if ($t5) goto L3 else goto L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:169:9+6
    if ($t5) { goto L3; } else { goto L2; }

    // label L3 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:170:26+14
    assume {:print "$at(2,4440,4454)"} true;
L3:

    // $t6 := get_field<0x42::prover_basics::Wallet>.balance($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:170:26+14
    assume {:print "$at(2,4440,4454)"} true;
    $t6 := $Dereference($t0)->$balance;

    // $t7 := -($t6, $t1) on_abort goto L5 with $t8 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:170:26+23
    call $t7 := $Sub($t6, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,4440,4463)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(1,14):", $t8} $t8 == $t8;
        goto L5;
    }

    // $t9 := borrow_field<0x42::prover_basics::Wallet>.balance($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:170:9+14
    $t9 := $ChildMutation($t0, 0, $Dereference($t0)->$balance);

    // write_ref($t9, $t7) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:170:9+40
    $t9 := $UpdateMutation($t9, $t7);

    // write_back[Reference($t0).balance (u64)]($t9) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:170:9+40
    $t0 := $UpdateMutation($t0, $Update'$42_prover_basics_Wallet'_balance($Dereference($t0), $Dereference($t9)));

    // trace_local[wallet]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:170:9+40
    $temp_0'$42_prover_basics_Wallet' := $Dereference($t0);
    assume {:print "$track_local(1,14,0):", $temp_0'$42_prover_basics_Wallet'} $temp_0'$42_prover_basics_Wallet' == $temp_0'$42_prover_basics_Wallet';

    // trace_local[wallet]($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:167:59+143
    assume {:print "$at(2,4328,4471)"} true;
    $temp_0'$42_prover_basics_Wallet' := $Dereference($t0);
    assume {:print "$track_local(1,14,0):", $temp_0'$42_prover_basics_Wallet'} $temp_0'$42_prover_basics_Wallet' == $temp_0'$42_prover_basics_Wallet';

    // goto L4 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:167:59+143
    goto L4;

    // label L2 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:169:9+6
    assume {:print "$at(2,4376,4382)"} true;
L2:

    // drop($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:169:9+6
    assume {:print "$at(2,4376,4382)"} true;

    // $t10 := 5 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:169:43+1
    $t10 := 5;
    assume $IsValid'u64'($t10);

    // trace_abort($t10) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:169:9+6
    assume {:print "$at(2,4376,4382)"} true;
    assume {:print "$track_abort(1,14):", $t10} $t10 == $t10;

    // $t8 := move($t10) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:169:9+6
    $t8 := $t10;

    // goto L5 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:169:9+6
    goto L5;

    // label L0 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:168:9+6
    assume {:print "$at(2,4339,4345)"} true;
L0:

    // drop($t0) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:168:9+6
    assume {:print "$at(2,4339,4345)"} true;

    // $t11 := 4 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:168:33+1
    $t11 := 4;
    assume $IsValid'u64'($t11);

    // trace_abort($t11) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:168:9+6
    assume {:print "$at(2,4339,4345)"} true;
    assume {:print "$track_abort(1,14):", $t11} $t11 == $t11;

    // $t8 := move($t11) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:168:9+6
    $t8 := $t11;

    // goto L5 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:168:9+6
    goto L5;

    // label L4 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:171:5+1
    assume {:print "$at(2,4470,4471)"} true;
L4:

    // assert Not(false) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:178:9+16
    assume {:print "$at(2,4701,4717)"} true;
    assert {:msg "assert_failed(2,4701,4717): function does not abort under this condition"}
      !false;

    // assert Eq<u64>(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t0), Sub(select prover_basics::Wallet.balance<0x42::prover_basics::Wallet>($t2), $t1)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:176:9+55
    assume {:print "$at(2,4582,4637)"} true;
    assert {:msg "assert_failed(2,4582,4637): post-condition does not hold"}
      $IsEqual'u64'($Dereference($t0)->$balance, ($t2->$balance - $t1));

    // assert Eq<bool>(select prover_basics::Wallet.frozen<0x42::prover_basics::Wallet>($t0), select prover_basics::Wallet.frozen<0x42::prover_basics::Wallet>($t2)) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:177:9+44
    assume {:print "$at(2,4647,4691)"} true;
    assert {:msg "assert_failed(2,4647,4691): post-condition does not hold"}
      $IsEqual'bool'($Dereference($t0)->$frozen, $t2->$frozen);

    // return () at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:177:9+44
    $ret0 := $t0;
    return;

    // label L5 at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:171:5+1
    assume {:print "$at(2,4470,4471)"} true;
L5:

    // assert false at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:173:5+245
    assume {:print "$at(2,4479,4724)"} true;
    assert {:msg "assert_failed(2,4479,4724): abort not covered by any of the `aborts_if` clauses"}
      false;

    // abort($t8) at /mnt/c/Development/move/source-code/move-security-lab/move_security_lab/sources/move_security_lab.move:173:5+245
    $abort_code := $t8;
    $abort_flag := true;
    return;

}
