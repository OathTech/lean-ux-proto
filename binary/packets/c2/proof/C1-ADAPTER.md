# For the C1 branch: taking the shared 8-byte comparison callback

The callback `__sanitizer_cov_trace_cmp8` is stated once, on branch `task/binary-c2`:

- `binary/CallbackCmp8Image.lean`: the entry's literal terms (`Cmp8.cmp8Fetch`) and the
  premise `Cmp8.Cmp8Agreement`;
- `binary/CallbackCmp8Rule.lean`: the rule `Cmp8Rule` (and `cmp8_kcov`, the same rule in
  `TrustBase`'s vocabulary: `KcovReady .cmp8`, `KcovWrites .cmp8`, `KcovEffect .cmp8`,
  with the call's interior confined to the callbacks' text);
- `binary/CallbackCmp8.lean` and files named `CallbackCmp8*.lean`: the proof, by C2's
  work package 1.

C1 takes those files unchanged (they import only landed modules) and does not edit
them. It registers them as roots in its own `binary/lakefile.toml`. Its own image terms
(`binary/StatementC1CallbackImage.lean`, a statement file, unchanged) are connected by
the lemma below, which was compiled in scratch against the C1 branch's file at
`7d39d508` and prints `[propext]`. It belongs in a C1 file, not in the shared modules.

```lean
import StatementC1CallbackImage
import CallbackCmp8Image
open Binary Binary.Callback

/-- What the C1 branch proves on its side: its own image terms give the premise of `Cmp8Rule`. -/
theorem c1_agreement (fetch : Int64 → Option Decoded)
    (reading : ∀ pc i, StatementC1CallbackImage.fetch pc = some i → fetch pc = some i) :
    Cmp8.Cmp8Agreement fetch := by
  intro pc i here
  apply reading
  by_cases h0 : pc = .ofNat 18446744071579844768
  · subst h0; exact here
  by_cases h1 : pc = .ofNat 18446744071579844772
  · subst h1; exact here
  by_cases h2 : pc = .ofNat 18446744071579844775
  · subst h2; exact here
  by_cases h3 : pc = .ofNat 18446744071579844778
  · subst h3; exact here
  by_cases h4 : pc = .ofNat 18446744071579844783
  · subst h4; exact here
  exfalso
  have h0' : ¬pc = Cmp8.cmp8Entry := h0
  have h1' : ¬pc = Cmp8.cmp8Entry + 4 := h1
  have h2' : ¬pc = Cmp8.cmp8Entry + 4 + 3 := h2
  have h3' : ¬pc = Cmp8.cmp8Entry + 4 + 3 + 3 := h3
  have h4' : ¬pc = Cmp8.cmp8Entry + 4 + 3 + 3 + 5 := h4
  simp [Cmp8.cmp8Fetch, Cmp8.cmp8Stub, Image.fetchIn, h0', h1', h2', h3', h4'] at here
```

From `Cmp8.Leaf fetch Cmp8.cmp8Entry (KcovPlan .cmp8)` C1 gets
`AllowedipsTraceCmp8Contract fetch`: the returned state, the frame and the effect are
the same three conjuncts; `NoAnchoredReentry` is the `leafGuard` half of `Interior`;
`NoAllowedipsReentry` follows from the `Text` half and the disjointness of the
callbacks' text from `AllowedipsImage.fetch`'s domain, which is C1's to prove.

`__sanitizer_cov_trace_cmp1`, the other entry in C1's image file, is not shared: C2
does not call it.
