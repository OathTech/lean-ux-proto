# The image bridge: `instructionStep fetch` against the fork's `Host` / `Program` model

Status: stage 0c of [the Ascent probe](2026-11-09-charter-ascent-probe.md).
A design, with its central theorems checked in a scratch package against the
fork at `add7e55` on `nightly-2026-11-07`. Nothing here is landed and nothing
is a result about the s5 image: the scratch package uses copies of our
definitions, not the `binary/` package. Recommendations are **[AGENT
2026-11-09, stage 0c worker]**; none is a user decision.

Names on our side are from `binary/` (`Binary.Decoded`,
`Binary.instructionStep`, `Binary.LaidOut`, `Binary.region_eventually`,
`Binary.Image.linkedLabels`, `Binary.Image.fetchIn`,
`Binary.AllowedipsMutationImage.Add.*`,
`Binary.TrustBase.AllowedipsMutationDecoderAgreement`,
`Binary.TrustBase.AllowedipsTracePcContract`). Names on the fork's side are
from `Kraken/X64/WP/{Host,Step,Basic,Instance,Spec}.lean`, `Kraken/FunSpec.lean`
and `Kraken/Layout.lean`; names on Ascent's side are from `demo/Demo/`.

## Summary

- A sound bridge exists and needs no new trusted premise. For any `Host` whose
  positive-size instructions agree with the image's `fetch`, an execution of
  the host is an execution of the image:
  `Eventually (step1 Host.exe) post st → Eventually (instructionStep fetch) post st`.
  This is proved (scratch, standard axioms only).
- A `Host` is built from a list of sized directives at real addresses, and all
  six `Host` side conditions follow from one boolean check evaluated by the
  kernel. Proved, and instantiated for the client segment with its real
  sizes and addresses.
- The fork's call rule does not apply to our callbacks: `Program.wp` steps
  over a call only when the callee's code is a `Fragment` of the host in
  `FunDecls`. A callback known only through a contract over
  `instructionStep` is an exit of the fragment. The composition with the
  contract happens on the image side, after the bridge.
- Of the client's 11 instructions the fork's `Spec.lean` covers 5. Stage 1
  must prove 4 new instruction specs (two `movzx` address forms, `sar %cl`
  at 32 bits, `and` with an immediate at 32 bits).

## 1. Presenting a region of the image to the fork's WP layer

### What the two sides are

Ours. `fetch : Int64 → Option Decoded` gives, at a real linked address, one
instruction and its byte length. The step is

```lean
def instructionStep [Labels] (fetch : Int64 → Option Decoded)
    (s : MachineState) (post : MachineState → Prop) : Prop :=
  match fetch s.pc with
  | none => False
  | some i => i.size > 0 ∧
    (i.instruction.interp s.data ⟨s.pc, s.pc + .ofNat i.size⟩
      (fun d => .done ⟨d, s.pc + .ofNat i.size⟩)
      (fun p d => .done ⟨d, p⟩)).All post
```

under `Labels := Image.linkedLabels`, a fixed function from label names to
addresses (an explicit table, then `canonicalAddress`, which reads the
address out of the name `L_<16 hex digits>`). Client theorems quantify over
`fetch` and assume it extends the generated image
(`AllowedipsMutationDecoderAgreement fetch`).

The fork's. A `Host` is a `Program` (a list of `Directive`: `.instr`,
`.label`, `.byteArray`) and a `Layout` (a start address and a size per index).
`Host.exe : Executable` is the program with its sizes;
`Host.addrOf k = start + ofNat (sum of the first k sizes)`. The step is

```lean
def step1 [Layout] (e : Executable) (s : MachineState) (post) : Prop :=
  (Executable.step e s .done).All post
-- Executable.step e s ret =
--   let := Executable.labels e
--   Directives.interp (e.directivesAtAddress s.pc) s.data s.pc (fun pc s => ret ⟨s, pc⟩)
```

Labels are not a parameter: `Executable.labels e` resolves a label to the
address of the first `.label` directive with that name in the program, and to
`-1` when there is none. Everything in the WP layer (`Program.wp`,
`Host.label_eq`, the `@[spec]` triples) is stated under this instance.

The instruction interpreter (`Instr.interp`, `Operation.interp`,
`Effects`, `Effects.All`) is the same definition on both sides. The fork's
`Directives.interp` has a separate `jmp` continuation that defaults to `ret`;
our pin has one continuation used for both. `Executable.step` passes the
default, so the meaning is the same.

### The obstacle and its resolution

The only place the two steps can disagree is label resolution. A jump or call
in the image names its target `L_ffffffff…`, and `linkedLabels` sends it to
the real address whether or not that address is in the region. In a host, the
same label resolves to the real address only if the host's program contains a
`.label` directive laid out exactly there.

Resolution: the host program for a region is the region's instructions in
address order, with

- a `.label l` directive (size 0) at each address that an instruction of the
  region names, inside or outside the region;
- a `.byteArray` directive of the right size as a gap filler between
  non-adjacent addresses. A positive-size `.byteArray` is never executed:
  `Directive.interp` of it is `.unimplemented`, whose `Effects.All` is
  `False`.

For the client segment the host is 15 directives: the callee's label at
`0xffffffff810f31f0`, a gap of 2808474 bytes, the 11 instructions from
`Add.entry + 0xca` with their real sizes, a gap of 1128 bytes, and the label
`L_ffffffff813a111f` at `Add.entry + 0x55f`.

### Definitions and theorems (proved once)

All of the following is checked in the scratch package (section 6). The
proofs carry over to `binary-ascent/` unchanged once `Decoded` and
`instructionStep` are the real ones, which are textually identical.

```lean
/-- Every positive-size instruction of the host is the image's instruction at that
address, with the same size and the same meaning under the image's labels. -/
def Agrees [Host] (L : Labels) (fetch : Int64 → Option Decoded) : Prop :=
  ∀ k ins, Host.prog[k]? = some (.instr ins) → 0 < Kraken.Layout.size Directive k →
    ∃ ins', fetch (Host.addrOf k) = some ⟨ins', Kraken.Layout.size Directive k⟩ ∧
      ∀ s p next jmp,
        @Instr.interp Host.exe.labels ins s p next jmp = @Instr.interp L ins' s p next jmp

/-- B1, the bridge. -/
theorem eventually_of_step1 [Host] (L : Labels) (fetch : Int64 → Option Decoded)
    (agree : Agrees L fetch) {post : MachineState → Prop} {st : MachineState}
    (h : Eventually (step1 Host.exe) post st) :
    Eventually (@instructionStep L fetch) post st
```

Proof of B1, by induction on `h`. At a state whose `pc` is `Host.addrOf k`
for a positive-size directive: `Host.interp_addrOf` turns the host step into
the interpretation of that one directive between `addrOf k` and
`addrOf (k+1)`; a label is excluded by `Host.label_size`, a `.byteArray` makes
the step `False`, and an instruction is rewritten by `agree` into the image
step. At any other `pc` every directive at that address has size 0 and is
inert (`Host.inert_of_size_zero`, `Directives.interp_inert_append`), so the
host step is a stutter (`step1 Host.exe st mid → mid st`) and the induction
hypothesis applies to the same state. The stutter case is why B1 holds for
every `Eventually (step1 Host.exe)` and not only for those produced by
`Program.step1_of_wp`.

`Agrees` is monotone in `fetch` (if `g` extends `f` and `Agrees L f` then
`Agrees L g`; three lines, not yet written), which is how an agreement
proved for `Add.fetch` serves a client that quantifies over `fetch` under
`AllowedipsMutationDecoderAgreement`.

```lean
def shapeOK : List (Kraken.Sized Directive) → Bool   -- labels have size 0, all else > 0
def sizesOf (code) : List Nat := code.map (·.size)
def check (start : Int64) (code : List (Kraken.Sized Directive)) : Bool :=
  shapeOK code && Nat.blt (start.toBitVec.toNat + (sizesOf code).sum) (2 ^ 64 - 1) &&
    nodupB (Program.labels (code.map (·.directive)))

/-- B2, the host of a region. -/
def hostOf (start : Int64) (code : List (Kraken.Sized Directive))
    (h : check start code = true) : Host
-- prog := code.map (·.directive);  layout.start := start;
-- layout.size i := (code[i]?.map (·.size)).getD 0

theorem exe_hostOf (h) : @Host.exe (hostOf start code h) = ⟨start, code⟩
theorem addrOf_hostOf (h) (k : Nat) :
    @Host.addrOf (hostOf start code h) k = start + .ofNat ((sizesOf code).take k).sum
theorem label_hostOf (h) {i : Nat} {l : Label}
    (hi : (code.map (·.directive))[i]? = some (.label l)) :
    (@Host.exe (hostOf start code h)).labels.label l
      = start + .ofNat ((sizesOf code).take i).sum
```

The `Host` side conditions, and how `hostOf` discharges each from `check`:

| Condition | Holds for the image because | Discharged by |
| --- | --- | --- |
| `labels_nodup` | each label is listed once in the synthesized program | `nodupB` in `check` |
| `label_size` | synthesized labels have size 0 | `shapeOK` |
| `instr_size_pos` | every decoded instruction has its real length, at least 1 | `shapeOK` |
| `instr_addr_ne` (no instruction at `-1`) | `start + total size < 2^64 - 1`, no wraparound | the bound in `check` |
| `zero_inert` | the only size-0 directives are labels, which are inert | `shapeOK` and `label_inert` |
| `addr_determines_offset` | no wraparound, so addresses determine offsets | the bound in `check` |

Per region the check is one `by decide +kernel` (kernel evaluation of a
structural boolean function; no `native_decide`, no axiom beyond the
standard three). This is the pattern of Ascent's `Host.ofCheck` /
`Binary.assembles_of_check` in `demo/Demo/BinaryCheck.lean`, without the byte
decoder.

```lean
/-- B3, one pass over the host's code. -/
inductive Walk (H L : Labels) (fetch : Int64 → Option Decoded) :
    Int64 → List (Kraken.Sized Directive) → Prop
  | nil (pc) : Walk H L fetch pc []
  | label (pc l n t) (rest : Walk H L fetch (pc + .ofNat n) t) :
      Walk H L fetch pc (⟨.label l, n⟩ :: t)
  | gap (pc b n t) (rest : Walk H L fetch (pc + .ofNat n) t) :
      Walk H L fetch pc (⟨.byteArray b, n⟩ :: t)
  | instr (pc ins ins' n t) (here : fetch pc = some ⟨ins', n⟩)
      (same : ∀ s p next jmp,
        @Instr.interp H ins s p next jmp = @Instr.interp L ins' s p next jmp)
      (rest : Walk H L fetch (pc + .ofNat n) t) :
      Walk H L fetch pc (⟨.instr ins, n⟩ :: t)

theorem agrees_of_walk (h : check start code = true) (L : Labels) (fetch)
    (w : Walk (@Host.exe (hostOf start code h)).labels L fetch start code) :
    @Agrees (hostOf start code h) L fetch
```

`Walk` is `LaidOut` with the label agreement added. Per instruction:

- `here` is `rfl`, the same obligation `binary_layout` discharges today;
- `same` is `fun _ _ _ _ => rfl` for an instruction that names no label (the
  two sides are the same term up to an unused instance; this is also how
  `Binary.decode_interp` in Ascent's demo proves it);
- for `jcc l`, `jmp l` and `call l`: unfold
  `Instr.interp, Operation.interp, RelRegOrMem.interp, ConstExpr.interp`
  and rewrite with one label lemma per label,
  `Host.exe.labels.label l = linkedLabels.label l`, which is
  `(label_hostOf h (i := idx) rfl).trans (by decide +kernel)`.

A missing or misplaced `.label` directive makes the host resolve the label to
`-1` or to another address, and the `same` obligation fails: the bridge fails
closed.

### The three options

(i) **A `Host` synthesized from the image, bridge at `Eventually`.** The
construction above. Proved once: B1, B2, B3 (about 320 lines, written).
Per region: the code list with labels and gaps (15 entries for the client;
generated by `generate_allowedips_mutation.py` for larger regions), one
`check`, one label lemma per named label, one `Walk` (a tactic in the style
of `binary_layout`). Per fragment: an `Embeds` instance (`⟨⟨k, ⟨_, rfl⟩⟩⟩`)
and the two address equations
`startAddr = Add.entry + a`, `endAddr = Add.entry + b`
(`(addrOf_hostOf h k).trans (by decide +kernel)`). Assumed: nothing beyond
what client theorems already assume (`AllowedipsMutationDecoderAgreement`).
New trusted premise: none.

(ii) **A fork-style `wp` defined directly over `instructionStep`, reusing only
the instruction specs and `vcgen`.** The instruction specs are `Triple`s
whose `WP` instance for `Directive` is `Program.wp [d]` in a `Host`
(`Program.WP.instWP`), and every spec is proved through
`Program.wp_single`, which needs the host's layout to name the two addresses
of the instruction. So the specs cannot be reused without a host: either each
spec is re-proved against a new `wp` (and `vcgen`'s structural rules
`Spec.cons`, `straight_instr`, `Program.wp_cons`, `Program.run_infix`, the
`StateCfg` loop rules with them, on the order of 1500 lines of the fork, an estimate), or a host is
built anyway and the facts are pulled out with `Host.stepIn_elim`, which is
option (i) with extra steps. Rejected as a first route. It becomes relevant
only if the fork generalizes `Program.wp` over the step.

(iii) **Ascent's `Binary` route.** `demo/Demo/Binary.lean` defines
`Binary.wp b done exit s` as the same `While` loop as `Program.wp` over a step
that decodes bytes (`Binary.decode`, 10 encodings), interprets each jump
under a per-instruction label map (`Binary.labelsAt`, with `Instr.eraseLabel`),
and continues on jump targets found by a sweep (`Binary.targets`).
`Binary.Assembles p b` relates it to a host; `Binary.wp_of_program_wp` and
`Binary.refines_program` transfer `Program.wp` and `⪯`;
`Binary.assembles_of_check` proves `Assembles` from `Binary.check … = true`.
For us the "binary" is `fetch`, so the byte decoder is not needed and the
label erasure is replaced by `Agrees`. What (iii) adds over (i) is a `WP`
instance on an image-region type, so that Ascent's refinement
`⦃P⦄ region ⪯[…] program ⦃…⦄` can be stated about the image. Stage 1 does not
need it: its statements are `Eventually (instructionStep fetch)`. Stage 2
needs either this (an `Image.wp` with `Image.wp_of_program_wp`, about 150
lines following `Binary.lean` lines 161 to 370) or a lifted statement that
stays at `Program` level and is bridged only at the end through B1.
Same once/per-region split as (i); no new trusted premise.

## 2. How the semantics differ

**What a step is.** `instructionStep fetch` executes exactly one fetched
instruction and is `False` where `fetch` is `none`. `step1 Host.exe` executes
every directive at the address: the size-0 labels, then the one positive-size
directive. Where the host has nothing it does not fail; it stutters
(`Directives.interp [] = ret pc s`). B1 absorbs both differences. The
converse of B1 is false and not needed.

**`Effects`.** One datatype and one `Effects.All` on both sides:
`unimplemented`, `gp_unaligned`, `nonmem_load`, `nonmem_store` are `False`;
`undefined` quantifies over every value; `require_read_access`,
`require_write_access`, `require_exec_access` continue. B1 never inspects
them: it transports `(… ).All post` whole. In specs, `undefined` shows up as
a universally quantified flag or status (`∀ af : Bool` in
`Spec.test_reg_reg`, `∀ st : StatusFlags` in `Spec.shl_reg32_imm`), and a
load or store shows up as a mapped-ness precondition
(`(Mem.loadInt s.dmem a n).isSome = true`). These are the same obligations
our region lemmas discharge today by `simp` over the interpreter.

**Jumps out of a fragment.** `Program.wp p done exit s` runs
`Executable.StepOver` until `pc` reaches the fragment's end address, where
`done` must hold. A jump to a label of `p` with the stack at or below the
entry stack continues (`Program.ContinueOnInternalExit`,
`Program.InternalTarget`); any other jump must satisfy `exit` at the target
state. `Spec.jcc_label` and `Spec.jmp_label` give `E (label l) s`. With a
synthesized host, `label l` is the real address (by `label_hostOf`), so an
exit post can say `a = Add.entry + 0x55f`. `Program.step1_of_wp` (in
`Basic.lean`; takes both `done` and `exit`) turns the `wp` into
`Eventually (step1 Host.exe) post` for any `post` implied by `done` at the
end address and by `exit`. The variant `Program.WP.step1_of_wp` in
`Instance.lean` requires the exit post to be `False` and is not the one to
use for our fragments.

**`ret`.** `Spec.ret` requires `s.retAddr.isSome` and gives
`E s.retAddr.get! { s with rsp := rsp + 8 }`: a return is an exit to the
address in the return slot. This matches our `Returned` shape
(`final.pc = returnAddress`, `rsp = entry rsp + 8`).

**Calls, and the callback in particular.** On our side a callee is a contract
over the image step:

```lean
def AllowedipsServiceReturns (fetch) (address : Int64) ready writes effect : Prop :=
  ∀ s returnAddress, s.pc = address → ready s → EntryFrame s returnAddress →
    Eventually (historyStep fetch) (fun t => Returned s t.machine returnAddress ∧
      EqualOutside (writes s) s.data.dmem t.machine.data.dmem ∧ effect s t.machine ∧ …) ⟨s, [s]⟩
```

`AllowedipsTracePcContract fetch` is this at `0xffffffff810f31f0`, and it is
a hypothesis of `ChildInput.segment`. The caller executes the real `call`
(`Instrumentation.call_instruction`, giving `calledState s (pc+5) target`)
and then applies the contract (`Frame.call`).

On the fork's side a callee is code. `Program.wp` fixes
`callee a := (FunDecls.at a).map fun f => f.prog.wp (fun _ => False)`, where
a `Fragment` is a `Program` embedded in the host; `Executable.StepOut` steps
over a call only when the target is the start of such a fragment and the
stack went down. `Program.WP.wp_call_iff` and `Spec.call_label` are stated
for `FunDecls.body f`; `funspec … autoframes` (`FunSpec.autoframes`) proves a
triple for the callee's code and frames registers and memory. When
`FunDecls.at (label f) = none`, `Spec.call_label` is vacuous (its
precondition asks for `wp [] (fun _ _ => False) …`), and `vcgen` reports
"No spec found for program `FunDecls.body …`" (checked).

So the fork's call rule cannot consume `AllowedipsTracePcContract`. Three
ways to handle the callback, in order of preference:

1. *Exit and compose on the image side.* The call is an exit of the fragment
   at the callee's entry. Either the existing `Frame.call` executes the call
   and applies the contract (no fork machinery, one line as today), or the
   call is a one-instruction fragment through this spec, proved from the
   interpreter in the scratch package:

   ```lean
   theorem call_external_wp [Host] [FunDecls] {f : Label} (asz osz : Width)
       (hf : FunDecls.at (label f) = none) (s : MachineData)
       (hm : (Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true)
       {done exit : MachineState → Prop}
       (he : ∀ h : Embeds [Directive.instr (.regular asz osz (.call (.rel
               (.sub (.label f) .after_current_instruction))))],
         exit ⟨s.push64 h.embedding.endAddr, label f⟩) :
       Program.wp [Directive.instr (.regular asz osz (.call (.rel
         (.sub (.label f) .after_current_instruction))))] done exit s
   ```

   and its `vcgen` form `call_external` with `∀ ra, E (label f) (s.push64 ra)`.
   The `∀ ra` form forgets which address was pushed, so the continuation
   after the callee cannot be stated inside one `vcgen` run: the proof is cut
   at every external call into fragment, contract, fragment, joined by
   `eventually_trans`. That is the structure the current proofs already have.
2. *Generalize `Program.wp` over the callee table* (it is already a parameter
   of `Executable.StepOver`), so an abstract contract can be registered at an
   address. This is fork work: `Program.wp`, `wp_mono`, `wp_and`,
   `step1_of_wp`, `wp_call_iff` and the `funspec` command all mention the
   fixed table. A named engine gap, not stage 1 work.
3. *Put the callback's code in the host and prove a `funspec` for it.* This
   re-proves `binary/CallbackPc.lean` inside the fork and changes the type of
   the client (no `pcContract` hypothesis), so it does not meet the charter's
   exact-type condition.

**Stack-return-slot conventions.** The fork: `s.push64 ra` sets
`rsp := rsp - 8` and stores `ra` at the new `rsp`; a function triple is
stated from `(· = s.push64 ra)`; Ascent's `RetRel s ra` is
`a = ra ∧ l' = .exit ∧ s'.regs.get64 .rsp = s.regs.get64 .rsp` and
`SameStackFrame` keeps `rsp` and `retAddr` fixed inside the body. Ours:
`calledState s returnPC target` is the same state as
`⟨s.push64 returnPC, target⟩` (same `rsp`, same stored word; the two are
written with `s.regs.rsp` and `s.regs.get64 .rsp`, so equality needs the
register-projection lemmas, not `rfl`; unverified), and
`EntryFrame s ra` / `Returned s t ra` are the entry and exit halves:
`Returned` gives `t.pc = ra`, `rsp = entry rsp + 8` and the callee-saved
registers, which is `RetRel` plus the System V preserved set of
`CallingConvention.SysV`. `EntryFrame` also requires `rsp % 8 = 0`, which the
fork does not track.

## 3. The client segment, instruction by instruction

`ChildInput.segment` runs from `Add.entry + 0xca` to `+0x55f` (child is null)
or `+0xf7`. The regions are `Add.rca`, `Add.rcf`, `Add.ree`, `Add.rf4` of
`binary/AllowedipsMutationImage.lean`. The fork's parser accepts all 11
lines (checked). "Fork spec" is checked by running `vcgen` on the single
instruction; "L1 rule" is by reading `demo/Demo/L1.lean` and is not checked
by running `ascend`.

| Offset | Instruction (size) | Fork `Spec.lean` | Ascent `L1.lean` |
| --- | --- | --- | --- |
| `+0xca` | `call L_ffffffff810f31f0` (5) | not covered: `call_label` needs the callee in `FunDecls`; see section 2 | no call rule |
| `+0xcf` | `movzbl 0x19(%rbx),%eax` (4) | not covered: no `movzx` spec | not covered (`wrp_movzxRegSib1` needs an index) |
| `+0xd3` | `movzbl 0x1a(%rbx),%ecx` (4) | not covered, same form | not covered |
| `+0xd7` | `mov %rbx,(%rsp)` (4) | covered: `mov_mem_reg` | not covered |
| `+0xdb` | `movzbl 0x0(%r13,%rax,1),%eax` (6) | not covered | covered by reading: `Spec.movzx_reg32_sib1`, `wrp_movzxRegSib1` (the spec lives in the demo, not the fork) |
| `+0xe1` | `sar %cl,%eax` (2) | not covered: only `shl_reg32_imm` | not covered |
| `+0xe3` | `and $0x1,%eax` (3) | not covered: `and_reg_imm` is 64-bit only | not covered |
| `+0xe6` | `mov 0x8(%rbx,%rax,8),%rax` (5) | covered: `mov_reg_sib8` | covered: `wrp_movRegSib8` |
| `+0xeb` | `test %rax,%rax` (3) | covered: `test_reg_reg` | covered with the branch: `wrp_testJcc` |
| `+0xee` | `je L_ffffffff813a111f` (6) | covered: `jcc_label` | covered: `wrp_testJcc`, `wrp_jcc` |
| `+0xf4` | `mov %rax,%rbx` (3) | covered: `mov_reg_reg` | covered: `wrp_movRegReg` |

New specs stage 1 must prove from the interpreter (none may be assumed):
`movzx` to a 32-bit register from a byte at `disp(base)`; `movzx` to a 32-bit
register from a byte at `disp(base,index,1)` (Ascent's
`Spec.movzx_reg32_sib1` can be copied with its proof); `sar` of a 32-bit
register by `%cl` (flags undefined or count-dependent: model on
`shl_reg32_imm`, with the masked count as a variable); `and` of a 32-bit
register with an immediate. Plus `call_external` if the call goes through
the WP layer. Stage 2 additionally needs `ascend` rules for six of these
forms.

## 4. Recommendation, size, and the likely failure

**Route: option (i).** Stage 1 ports the scratch files (B1, B2, B3) into
`binary-ascent/` against the real `Binary.instructionStep`, builds the host of
the client segment, keeps `Frame.call` (or `call_external_wp`) for the
callback, proves the remaining ten instructions as one `Program.wp` fragment
with `vcgen`, and lands at the old statement of `ChildInput.follow` and then
`ChildInput.segment` through B1 and `Agrees` monotonicity. The statement is
the old theorem's exact type: B1 ends in `Eventually (instructionStep fetch)`
under `Image.linkedLabels` and mentions no host.

Size estimate:

| Piece | Lines | State |
| --- | --- | --- |
| B1 `eventually_of_step1` with `Agrees`, `stutter` | 90 | written, checked |
| B2/B3 `hostOf`, `check`, `label_hostOf`, `Walk`, `agrees_of_walk` | 225 | written, checked |
| `Agrees` monotonicity, a `walk` tactic | 30 | to write |
| Client host: code list, check, 2 label lemmas, walk, embeddings | 60 | written for a copy of the image, checked |
| `call_external_wp`, `call_external` | 40 | written, checked |
| Four new instruction specs | 100 to 150 | to write |
| The fragment proof and the connection to `ChildInput` / `Frame` | unknown | this is what stage 1 measures |

Check time is not a concern at this scale: the scratch package (bridge, host,
agreement, a four-instruction `vcgen` fragment carried to the image) builds
in under 2 seconds.

**The single most likely way it fails.** Not the bridge. The verification
conditions. `vcgen` leaves the post in the fork's vocabulary
(`s.regs.get64 .rbx`, `Reg64s.set64`, `StatusFlags.ofLogic`,
`BitVec.ofInt 64 (Mem.loadInt …).get!`, `Mem.storeInt`), while `ChildInput`,
`Frame` and `child_step`'s neighbours speak `s.regs.rbx.toBitVec`,
`loadInt … = some x.toNat`, `EqualOutside`, `selected byte shift`. The
existing `child_step` needed hand arithmetic for the address
`rbx + 8 + 8 * selected …`, for the byte-index extension and for the masked
shift count. If `kfinish` (grind) does not close those conditions with a
small lemma set, stage 1 ends with the interpreter no longer unfolded but
the same address and width arithmetic still done by hand, which is the
"usable with named engine gaps" verdict at best. The second risk is the
callback: three of the verdict's measures (call setup, frame reconstruction)
are not touched by the fork's machinery at all under route 1 of section 2.

## 5. Unverified

- That the scratch proofs compile against the ported `binary/` closure
  (stages 0a and 0b). They use copies of `Decoded`, `instructionStep`,
  `fetchIn`, and of the four regions' text and sizes.
- `Walk` against the real `Add.fetch` (a nested range search over 127 regions)
  and the real `linkedLabels` table. The `here` obligations are the ones
  `binary_layout` already proves by `rfl`; label agreement through
  `canonicalAddress` was checked on a copy of that function and costs
  milliseconds.
- Scaling of `check` and `Walk` to a whole function (506 instructions, 38
  labels for `Add`). `nodupB` is quadratic in the number of labels.
- `calledState s ra target = ⟨s.push64 ra, target⟩`.
- Ascent `L1.lean` coverage in section 3 (by reading only), and anything
  about `ascend` on the client.
- That `vcgen` handles a fragment containing internal labels of a synthesized
  host (the `Program.cfg` path with invariants) on our code. The checked
  fragment is label-free with one conditional exit.
- The 150-line estimate for `Image.wp` (option iii).

## 6. The scratch experiment

A lake package requiring the fork by path, five files, 520 lines, standard
axioms only (`propext`, `Classical.choice`, `Quot.sound`), no `sorry`. It
lives in the run's scratch directory
(`/tmp/ascent-assess-182411/scratch-0c/bridge/`), which is not preserved;
stage 1 copies it into `binary-ascent/`.

| File | Content |
| --- | --- |
| `Bridge/Core.lean` | `Decoded`, `instructionStep` (copies), `Agrees`, `stutter`, `eventually_of_step1` |
| `Bridge/HostOf.lean` | `check`, `hostOf`, `exe_hostOf`, `addrOf_hostOf`, `label_hostOf`, `Walk`, `Walk.same`, `agrees_of_walk` |
| `Bridge/Client.lean` | the client segment's host (`hostCode`, `hostCode_check`, `host`), `label_tracePc`, `label_exit`, `walk`, `agrees` |
| `Bridge/Tail.lean` | `tail_wp` (the last four instructions, by `vcgen [tail] with kfinish [child]`, for any host) and `tail_image`: the same fragment as `Eventually (instructionStep fetch)` from `entry + 0xe6` to `entry + 0x55f` or `entry + 0xf7` |
| `Bridge/CallExternal.lean` | `call_external_wp`, `call_external` |

One negative control was run and removed: `tail_wp` with a wrong
fall-through post is rejected (`finish` fails).

## 7. Part 1 measurements, for the record

Host shared with other sessions; `nightly-2026-11-07`; fork at `add7e55`.
Memory is the largest single process, not the job total.

| Build | Result | Wall | Largest process | Warnings |
| --- | --- | --- | --- | --- |
| Ascent `lake build` | passed, 116 jobs | 16.6 s | 1.28 GB | 2 |
| `lake build AscentTests` | passed, 176 jobs | 2.1 s | 0.96 GB | 2 (replayed) |
| `demo/` `lake build` (builds the fork's WP modules) | passed, 226 jobs | 18.1 s | 1.66 GB | 85: 51 in the fork, 32 in the demo (20 of them module-system import notices), 2 replayed |

The demo builds against `vcgen` head; no other fork commit was tried.
`#print axioms` for `zipWithAdd_correct`, `zipWithAddHost_correct` and
`memmove_correct`: `[propext, Classical.choice, Quot.sound]` each.

Single-file elaboration, median of three, wall including about 0.36 s of
imports:

| Program (instructions) | `ascend_def` file | elaborator alone | `sym_simp_def` file | all stages, less imports |
| --- | --- | --- | --- | --- |
| `zipWithAdd` (10) | 0.69 s | 79 ms | 0.53 s (50 ms) | 2.2 s over 5 files |
| `memmove` (21) | 0.75 s | 103 ms | 0.73 s (234 ms) | 2.6 s over 5 files |
| `bsearch` (24) | 0.69 s | 88 ms | 1.28 s (705 ms) | 1.3 s over 2 files |

First figure: 4 to 8 ms per instruction for the `ascend` elaborator, 15 to 32
ms per instruction for the whole first-stage file less imports, 0.12 to 0.22 s
per instruction for the full chain to a pure program with its correctness
proof.

Fork bench, median of three (stepping / kernel, ms): `manycalls` 8: 508 / 14,
16: 767 / 22, 32: 1388 / 54; `changingframes` 8: 1274 / 21, 16: 3325 / 91,
32: 10367 / 201. `changingframes` grows faster than linearly (about 8x from 8
to 32 calls).
