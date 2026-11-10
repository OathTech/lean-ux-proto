import Image
open Kraken.X64.Parser

/-! The two 8-byte KCOV comparison entries of the pinned s5 image, stated once.

`__sanitizer_cov_trace_cmp8` (0xffffffff810f40a0) and
`__sanitizer_cov_trace_const_cmp8` (0xffffffff810f4120): five instructions each, ending
in a jump into `write_comp_data` (0xffffffff810f3fb0), whose body is in `ServiceImage`.

This module is neutral: it imports only `Image`, so the C1 and the C2 branch can both
take it unchanged. Each result's own statement file has its own copy of these literal
terms (`Binary.C2.Range.cmp8Stub`, `Binary.StatementC1CallbackImage.decoded`); a result
connects its copy to this one by an adapter lemma on its side (`Agreement` below), and
the rule about the code (`CallbackCmp8Rule`) is proved once, against this module. -/
namespace Binary.Callback.Cmp8

def cmp8Entry : Int64 := .ofNat 18446744071579844768       -- 0xffffffff810f40a0
def constCmp8Entry : Int64 := .ofNat 18446744071579844896  -- 0xffffffff810f4120

def cmp8Stub : List (Kraken.Sized Directive) :=
  List.zipWith (fun d n => ⟨d, n⟩) (parse("mov    (%rsp),%rcx
mov    %rsi,%rdx
mov    %rdi,%rsi
mov    $0x6,%edi
jmp L_ffffffff810f3fb0")) [4, 3, 3, 5, 5]

def constCmp8Stub : List (Kraken.Sized Directive) :=
  List.zipWith (fun d n => ⟨d, n⟩) (parse("mov    (%rsp),%rcx
mov    %rsi,%rdx
mov    %rdi,%rsi
mov    $0x7,%edi
jmp L_ffffffff810f3fb0")) [4, 3, 3, 5, 5]

/-- The literal instructions of `__sanitizer_cov_trace_cmp8`. -/
def cmp8Fetch (pc : Int64) : Option Binary.Decoded :=
  Binary.Image.fetchIn cmp8Entry cmp8Stub pc

/-- The literal instructions of `__sanitizer_cov_trace_const_cmp8`. -/
def constCmp8Fetch (pc : Int64) : Option Binary.Decoded :=
  Binary.Image.fetchIn constCmp8Entry constCmp8Stub pc

/-- The literal instructions of the two entries. -/
def fetch (pc : Int64) : Option Binary.Decoded :=
  (cmp8Fetch pc).orElse fun _ => constCmp8Fetch pc

/-- The ten instruction addresses. -/
def addresses : List Int64 :=
  [.ofNat 18446744071579844768, .ofNat 18446744071579844772, .ofNat 18446744071579844775,
   .ofNat 18446744071579844778, .ofNat 18446744071579844783,
   .ofNat 18446744071579844896, .ofNat 18446744071579844900, .ofNat 18446744071579844903,
   .ofNat 18446744071579844906, .ofNat 18446744071579844911]

/-- The ambient decoder agrees with the literal terms of `__sanitizer_cov_trace_cmp8`.
The premise of `Cmp8Rule`; each result derives it from its own reading of the image. A
result that calls only this entry (C1) needs only this premise. -/
def Cmp8Agreement (fetch : Int64 → Option Binary.Decoded) : Prop :=
  ∀ pc instruction, cmp8Fetch pc = some instruction → fetch pc = some instruction

/-- The same for `__sanitizer_cov_trace_const_cmp8`: the premise of `ConstCmp8Rule`. -/
def ConstCmp8Agreement (fetch : Int64 → Option Binary.Decoded) : Prop :=
  ∀ pc instruction, constCmp8Fetch pc = some instruction → fetch pc = some instruction

/-- Agreement on both entries (what C2 derives from its range's reading). -/
def Agreement (fetch : Int64 → Option Binary.Decoded) : Prop :=
  Cmp8Agreement fetch ∧ ConstCmp8Agreement fetch

end Binary.Callback.Cmp8
