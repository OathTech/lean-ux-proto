import C2Image
import TrustBase
import Layouts
import Leanux.WG.RxData

/-! Result C2, the final statement: the receive replay window in the pinned s5 image.
Statements only: every declaration here is a `def` or a `structure` of propositions.
Nothing here is proved. A root of `BinaryProofs`, so that it is built and scanned by
`scripts/binary-proof-gate`; the headline is `HeadlineRefinement`, at the end.

Range: `counter_validate` (drivers/net/wireguard/receive.c) as inlined in
`wg_packet_rx_poll`, `[0xffffffff8139d2a6, 0xffffffff8139d3ea)`, 70 instructions:
the load of the packet's counter, `spin_lock_bh` (in this single-CPU build: one add to
the preempt count, no lock word), the three rejection tests, the clear loop, the counter
store, `bts`, and `setb %bpl`. `spin_unlock_bh` and the branch on `%bpl` come after the
range and are not in it. Thirteen calls to three KCOV callbacks are in it. -/
namespace Binary.C2
open Binary TrustBase Leanux
local instance : Labels := Binary.Image.linkedLabels

/-! ## Part 1. Premises: nothing checks these; a reader has to judge them -/

/-- The ambient decoder agrees with the committed literal terms of the range (70
instructions, the `bts` among them) and of the two callback entries. -/
def RangeDecoderAgreement (fetch : Int64 → Option Decoded) : Prop :=
  ∀ pc instruction, Range.fetch pc = some instruction → fetch pc = some instruction

/-- What is assumed of the code: two readings of the image.
`ServiceDecoderAgreement` is the landed one: it covers the PC callback and the body
shared by the comparison callbacks. -/
structure Reading (fetch : Int64 → Option Decoded) : Prop where
  range : RangeDecoderAgreement fetch
  services : ServiceDecoderAgreement fetch

/-- `struct noise_replay_counter` inside the keypair at `kp`: 1032 bytes at offset 136
(the counter, then 128 bitmap words; the spinlock has size zero in this build). -/
def windowBytes (kp : BitVec 64) : BitVec 64 → Prop :=
  InRange (kp + .ofNat 64 Layouts.keypair_receiving_counter) Layouts.replaySize

/-- Stack bytes the range writes: the return-address slot of its calls, and the two
spill slots `0x10(%rsp)` and `0x18(%rsp)`. -/
def stackBytes (sp : BitVec 64) (a : BitVec 64) : Prop :=
  InRange (sp - 8) 8 a ∨ InRange (sp + 0x10) 16 a

/-- Everything the range itself writes, the coverage buffer apart. -/
def Footprint (sp kp : BitVec 64) (a : BitVec 64) : Prop :=
  stackBytes sp a ∨ windowBytes kp a ∨ InRange preemptCountAddress 4 a

/-- Bytes the coverage callbacks read as metadata or, in a recording mode, write. -/
def coverageBytes (layout : KcovLayout) (a : BitVec 64) : Prop :=
  KcovMetadataBytes layout a ∨ ((layout.mode = 2 ∨ layout.mode = 3) ∧ KcovStorageBytes layout a)

/-- The machine state at the entry cut `0xffffffff8139d2a6`, without any reference to
the mirror. `r13` and `rbx` are the inlining context: the caller loaded the keypair
pointer and holds the packet. The window is only required to be mapped. -/
structure Context (layout : KcovLayout) (preempt : BitVec 32) (s : MachineState)
    (kp skb nonce : BitVec 64) : Prop where
  pc : s.pc = Range.entry
  keypair : s.data.regs.r13.toBitVec = kp
  packet : s.data.regs.rbx.toBitVec = skb
  nonce : s.data.dmem.loadInt (skb + 0x28) 8 = some (nonce.toNat : Int)
  window : ∀ a, windowBytes kp a → (s.data.dmem.get? a).isSome = true
  aligned : s.data.regs.rsp.toNat % 8 = 0
  stack : ∀ a, stackBytes s.data.regs.rsp.toBitVec a → (s.data.dmem.get? a).isSome = true
  coverage : KcovState layout preempt s.data.dmem
  stackWindow : ∀ a, stackBytes s.data.regs.rsp.toBitVec a → ¬windowBytes kp a
  stackPreempt : ∀ a, stackBytes s.data.regs.rsp.toBitVec a → ¬InRange preemptCountAddress 4 a
  windowPreempt : ∀ a, windowBytes kp a → ¬InRange preemptCountAddress 4 a
  coverageApart : ∀ a, coverageBytes layout a → ¬Footprint s.data.regs.rsp.toBitVec kp a
  /-- Revision 2 (review finding H1): the coverage buffer does not lie over the coverage
  metadata. The landed entries carry the same premise (`LookupEntry.coverageMetadata`).
  Without it a callback's record can overwrite the task's `kcov_area` field and later
  records land anywhere, the window included. -/
  coverageMetadata : ∀ a, (layout.mode = 2 ∨ layout.mode = 3) → KcovStorageBytes layout a →
    ¬KcovMetadataBytes layout a

/-! ## Part 2. What the headline concludes, in machine terms only -/

def exits : List Int64 := [Range.donePC, Range.rejectWindowPC, Range.rejectLimitPC]

/-- The observation: the range left by its last instruction with `%bpl = 0`. This is
the byte the branch at `0xffffffff8139d3ff` tests after the range; `%bpl = 1` there, and
either rejection exit, is a refusal. -/
def accepted (t : MachineState) : Bool :=
  t.pc == Range.donePC && t.data.regs.rbp.toNat % 256 == 0

/-- `t` is the first state at an exit on an actual execution from `s`. -/
def FirstExit (fetch : Int64 → Option Decoded) (s t : MachineState) : Prop :=
  ∃ history, ActualHistory fetch s history ∧ history.getLast? = some t ∧
    t.pc ∈ exits ∧ ∀ u ∈ history.dropLast, u.pc ∉ exits

/-- What holds at every exit whatever the outcome: bottom halves are still disabled
(the count is 0x200 higher), the coverage state is intact, the registers the caller
relies on are kept, and only the footprint and the coverage buffer were written. At
`donePC` the low half of `%rsi` is 0x200, the argument the unlock that follows passes
(revision 2, review finding L1: so a later result about the unlock can compose). -/
structure Kept (layout : KcovLayout) (preempt : BitVec 32) (kp : BitVec 64)
    (s t : MachineState) : Prop where
  coverage : KcovState layout (preempt + 0x200) t.data.dmem
  rsp : t.data.regs.rsp = s.data.regs.rsp
  rbx : t.data.regs.rbx = s.data.regs.rbx
  r12 : t.data.regs.r12 = s.data.regs.r12
  r13 : t.data.regs.r13 = s.data.regs.r13
  unlockArgument : t.pc = Range.donePC → t.data.regs.rsi.toNat % 2 ^ 32 = 0x200
  frame : EqualOutside
    (fun a => Footprint s.data.regs.rsp.toBitVec kp a ∨
      ((layout.mode = 2 ∨ layout.mode = 3) ∧ KcovStorageBytes layout a))
    s.data.dmem t.data.dmem

/-- CLAUSE 1. From every entry state the code reaches an exit, never
faulting, and `Kept` holds at the first one. -/
def ExitsCleanly : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (layout : KcovLayout) (preempt : BitVec 32)
    (s : MachineState) (kp skb nonce : BitVec 64),
    Reading fetch → Context layout preempt s kp skb nonce →
    Eventually (historyStep fetch)
      (fun e => e.machine.pc ∈ exits ∧ (∀ u ∈ e.history.dropLast, u.pc ∉ exits) ∧
        Kept layout preempt kp s e.machine)
      ⟨s, [s]⟩

/-- One execution of the range: its entry state, its first exit state, and the packet
counter the entry state holds at `skb + 0x28`. -/
structure Visit where
  entry : MachineState
  exit : MachineState
  nonce : BitVec 64

/-- Between one visit's exit and the next visit's entry the 1032 window bytes are the
same. Anything else may have happened to the machine. -/
def WindowRetained (kp : BitVec 64) : List Visit → Prop
  | first :: second :: rest =>
    (∀ a, windowBytes kp a → first.exit.data.dmem.get? a = second.entry.data.dmem.get? a) ∧
      WindowRetained kp (second :: rest)
  | _ => True

/-- The visits of one keypair's window, in order. -/
structure Visits (fetch : Int64 → Option Decoded) (kp : BitVec 64) (visits : List Visit) : Prop where
  entries : ∀ v ∈ visits, ∃ layout preempt skb, Context layout preempt v.entry kp skb v.nonce
  exits : ∀ v ∈ visits, FirstExit fetch v.entry v.exit
  retained : WindowRetained kp visits

def acceptedNonces (visits : List Visit) : List (BitVec 64) :=
  (visits.filter (fun v => accepted v.exit)).map (·.nonce)

/-- CLAUSE 2. Over any sequence of executions of the range on one keypair
address between which the window bytes are not changed, starting from any mapped window
contents, no packet counter is accepted twice. -/
def NoCounterAcceptedTwice : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (kp : BitVec 64) (visits : List Visit),
    Reading fetch → Visits fetch kp visits → (acceptedNonces visits).Nodup

/-- Optional third clause (the landed inclusive floor): an accepted counter is at most
one window, 8128, behind every counter accepted before it. -/
def AcceptedWithinWindow : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (kp : BitVec 64) (visits : List Visit),
    Reading fetch → Visits fetch kp visits →
    (acceptedNonces visits).Pairwise (fun earlier later => earlier.toNat ≤ later.toNat + 8128)

/-! ## Part 3. The refinement: what the code computes, in the mirror's terms

The adequacy half of the track's objective for this function. A clause of the
headline (`HeadlineRefinement`, at the end of the file). It mentions only the mirror,
never the proof tree. -/

/-- The keypair's replay state in the mirror's world. -/
def windowOf (world : WGWorld) (id : WG.KeypairId) : Option WG.ReplayCounter :=
  (world.dev.bind fun d => d.keypairs.get? id).map (·.receivingCounter)

/-- Which exit the image takes: its three rejection tests in their order, two of which
share an exit. The same tests, in the same order, are the mirror's decisions
`ctrRejectCounter`, `ctrRejectTheirs`, `ctrTooOld`. -/
def exitPC (c : WG.ReplayCounter) (nonce : Nat) : Int64 :=
  if c.counter ≥ WG.REJECT_AFTER_MESSAGES + 1 then Range.rejectWindowPC
  else if nonce ≥ WG.REJECT_AFTER_MESSAGES then Range.rejectLimitPC
  else if WG.COUNTER_WINDOW_SIZE + (nonce + 1) < c.counter then Range.rejectWindowPC
  else Range.donePC

/-- THE REFINEMENT. If the window bytes represent `c` (the landed `Layouts.ReplayFields`)
and the mirror's `counterValidate` on a world holding `c` returns `result` and leaves
`world'`, then the machine reaches, as its first exit, the exit the tests name; it
accepts exactly when the mirror returns `true`; and the window bytes then represent the
replay state of `world'`. -/
def Refines : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (layout : KcovLayout) (preempt : BitVec 32)
    (s : MachineState) (kp skb nonce : BitVec 64)
    (world world' : WGWorld) (ambient ambient' : Ambient) (id : WG.KeypairId)
    (c : WG.ReplayCounter) (result : Bool),
    Reading fetch → Context layout preempt s kp skb nonce →
    Layouts.ReplayFields s.data.dmem (kp + .ofNat 64 Layouts.keypair_receiving_counter) c →
    windowOf world id = some c →
    ((WG.counterValidate id nonce.toNat).run world).run ambient = .ok ((result, world'), ambient') →
    Eventually (historyStep fetch)
      (fun e => e.machine.pc = exitPC c nonce.toNat ∧
        (∀ u ∈ e.history.dropLast, u.pc ∉ exits) ∧
        accepted e.machine = result ∧
        (∃ c', windowOf world' id = some c' ∧
          Layouts.ReplayFields e.machine.data.dmem (kp + .ofNat 64 Layouts.keypair_receiving_counter) c') ∧
        Kept layout preempt kp s e.machine)
      ⟨s, [s]⟩

/-! ## Part 4. Against vacuity: a witness and two exclusions

A witness that the premises can be met, and two statements naming behaviours to rule
out or in. The two exclusions (`ReplayRefused`, `AdvanceAccepted`) are in no headline:
the first is a corollary of `NoCounterAcceptedTwice`, the second of `Refines`. -/

/-- The premises are satisfiable, by a replay: the same packet counter presented twice
to one retained window is accepted the first time and refused the second. And the
further premises of `Refines` are satisfiable with them (review finding F1): the first
visit's window bytes represent a replay state `c`, a world holds `c`, and the mirror's
`counterValidate` on that world succeeds, accepting, as the machine does. -/
def ReplayWitness : Prop :=
  ∃ (fetch : Int64 → Option Decoded) (kp : BitVec 64) (first second : Visit),
    Reading fetch ∧ Visits fetch kp [first, second] ∧ first.nonce = second.nonce ∧
    accepted first.exit = true ∧ accepted second.exit = false ∧
    ∃ (world world' : WGWorld) (ambient ambient' : Ambient) (id : WG.KeypairId)
      (c : WG.ReplayCounter),
      Layouts.ReplayFields first.entry.data.dmem
        (kp + .ofNat 64 Layouts.keypair_receiving_counter) c ∧
      windowOf world id = some c ∧
      ((WG.counterValidate id first.nonce.toNat).run world).run ambient =
        .ok ((true, world'), ambient')

/-- Excluded: accepting a packet counter that an earlier visit accepted. -/
def ReplayRefused : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (kp : BitVec 64) (before between : List Visit)
    (earlier later : Visit),
    Reading fetch → Visits fetch kp (before ++ earlier :: between ++ [later]) →
    earlier.nonce = later.nonce → accepted earlier.exit = true → accepted later.exit = false

/-- Excluded: refusing everything. A packet counter below the limit whose bitmap word
lies beyond the word of the stored counter (the quadword at `kp + 136`, itself not past
the limit) is accepted. -/
def AdvanceAccepted : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (layout : KcovLayout) (preempt : BitVec 32)
    (s t : MachineState) (kp skb nonce high : BitVec 64),
    Reading fetch → Context layout preempt s kp skb nonce → FirstExit fetch s t →
    s.data.dmem.loadInt (kp + .ofNat 64 Layouts.keypair_receiving_counter) 8 = some (high.toNat : Int) →
    high.toNat ≤ 0xffffffffffffe03e → nonce.toNat < 0xffffffffffffe03e →
    high.toNat / 64 < (nonce.toNat + 1) / 64 →
    accepted t = true

/-! ## Part 5. The headline -/

/-- THE HEADLINE. What the code computes (`Refines`), that it exits cleanly, the
transported property, and a witness that all of it is inhabited. (Rejected alternative:
a machine-states-only conjunction with `AdvanceAccepted` in place of `Refines`, which
holds of code that permutes the bits of a bitmap word.) -/
def HeadlineRefinement : Prop :=
  ExitsCleanly ∧ Refines ∧ NoCounterAcceptedTwice ∧ ReplayWitness

end Binary.C2
