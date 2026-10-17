import Leanux.Proofs.WG.Queues.FundedHandoff
import Leanux.Proofs.WG.Queues.RxCarrierInitial

/-! Complete state-facing accounts of lasting peer references. Temporary
source locals remain explicit loans; aliases and notification queues are not
additional holders. Every holder and RX carrier uses one combined budget. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes

structure DurableHolders where
  base : Reservations := []
  send : Reservations := []
  clear : Reservations := []
  tx : List TxHandoff := []
  cursor7 : Option Owner := none
  cursor8 : Option Owner := none

namespace DurableHolders

def owners (h : DurableHolders) : Reservations :=
  h.base ++ h.send ++ h.clear ++ h.tx.map TxHandoff.owner ++
    h.cursor7.toList ++ h.cursor8.toList

def items (h : DurableHolders) (pid : PeerId) : List (List SkbId) :=
  (h.tx.filter fun e => e.owner.slot == pid).map TxHandoff.item

/-- Completion pays the cursor before clearing cbRunning. hasWg is a recorded
condition, not a guard on that payment, so it cannot erase an obligation here. -/
def activeCursor (sock : NlSock) : Option PeerId :=
  if sock.cbRunning then sock.ctx.nextPeer else none

/-- These holders are unaffected by a TX/send handoff, but their frame must
be established from its actual caller: Handoff.base alone does not supply it. -/
def passiveView (w : WGWorld) :=
  ((w.dev.map Device.peerList).getD [],(w.dev.map Device.clearWorkQueue).getD [],
    activeCursor w.nlSock7,activeCursor w.nlSock8)

structure Aligned (h : DurableHolders) (w : WGWorld) : Prop where
  base : h.base.map Owner.slot = (w.dev.map Device.peerList).getD []
  send : ∀ d, w.dev = some d → d.sendWorkQueue = h.send.map Owner.slot
  clear : h.clear.map Owner.slot = (w.dev.map Device.clearWorkQueue).getD []
  tx : ∀ pid batches, handoffTxView w pid = some batches → batches = h.items pid
  cursor7 : h.cursor7.map Owner.slot = activeCursor w.nlSock7
  cursor8 : h.cursor8.map Owner.slot = activeCursor w.nlSock8

/-- No absent peer is filtered from the proof account. Funding ensures every
listed occurrence, including a TX item, refers to a live stamped allocation. -/
structure Funded (h : DurableHolders) (cs : Ledger) (loans : Reservations)
    (w : WGWorld) : Prop where
  aligned : h.Aligned w
  carriers : CarrierState cs (h.owners ++ loans) w

/-- This existential is proof state only. It does not add operational records
or substitute a new interpreter for the mirror. -/
def Boundary (cs : Ledger) (loans : Reservations) (w : WGWorld) : Prop :=
  ∃ h : DurableHolders, h.Funded cs loans w ∧ StableRx cs w

def absorb (h : DurableHolders) (delta : HandoffDelta) : DurableHolders :=
  {h with tx := h.tx ++ delta.tx, send := h.send ++ delta.send}

theorem absorb_items (h : DurableHolders) (delta : HandoffDelta) (pid : PeerId) :
    (h.absorb delta).items pid = h.items pid ++ delta.items pid := by
  simp [absorb,items,HandoffDelta.items]

theorem absorb_count (h : DurableHolders) (delta : HandoffDelta) (o : Owner) :
    (h.absorb delta).owners.count o = h.owners.count o + delta.owners.count o := by
  simp [absorb,owners,HandoffDelta.owners,List.count_append]
  simp only [show (fun x : TxHandoff => x.owner) = TxHandoff.owner from rfl]
  omega

theorem Funded.resident {h : DurableHolders} (hi : h.Funded cs loans w) (member : o ∈ h.owners) :
    ∃ p, resident w o = some p := by
  have pos : 0 < h.owners.count o := List.count_pos_iff.mpr member
  have demandPos : 0 < demand cs (h.owners ++ loans) o := by
    simp only [demand,List.count_append]; omega
  obtain ⟨p,hp,_⟩ := protected_resident hi.carriers.funded demandPos
  exact ⟨p,hp⟩

theorem Aligned.absorb {h : DurableHolders} (hi : h.Aligned w) (step : Handoff w v before after delta)
    (passive : passiveView v = passiveView w) : (h.absorb delta).Aligned v := by
  have list := congrArg Prod.fst passive
  have clear := congrArg (fun x => x.2.1) passive
  have cursor7 := congrArg (fun x => x.2.2.1) passive
  have cursor8 := congrArg (fun x => x.2.2.2) passive
  have epoch := congrArg Prod.fst step.base
  refine ⟨hi.base.trans list.symm,?_,hi.clear.trans clear.symm,?_,
    hi.cursor7.trans cursor7.symm,hi.cursor8.trans cursor8.symm⟩
  · intro d hd
    cases hw : w.dev with
    | none => simp [baseView,hd,hw] at epoch
    | some old =>
      have send := step.send
      simp only [sendView,hd,hw,Option.map_some,Option.some.injEq] at send
      simpa only [DurableHolders.absorb,List.map_append,hi.send old hw] using send
  · intro pid batches found
    have first := step.tx pid
    cases old : handoffTxView w pid with
    | none => simp [old,found] at first
    | some previous =>
      have eq : batches = previous ++ delta.items pid := by
        simpa only [old,found,Option.map_some,Option.some.injEq] using first
      rw [eq,hi.tx pid previous old,absorb_items]

/-- Absorb precisely the actual durable delta while exchanging only the
supplied transient loans. The unaffected-holder frame is explicit. -/
theorem Funded.handoff {h : DurableHolders} (hi : h.Funded cs (loans ++ before) w)
    (step : Handoff w v before after delta) (keys : KeysCompatible v)
    (passive : passiveView v = passiveView w) :
    (h.absorb delta).Funded cs (loans ++ after) v := by
  have initial : CarrierState cs ((h.owners ++ loans) ++ before) w := by
    simpa only [List.append_assoc] using hi.carriers
  have funded := initial.handoff step keys
  refine ⟨hi.aligned.absorb step passive,WorkReservations.carrier_loans_perm funded ?_⟩
  apply List.perm_iff_count.mpr
  intro o
  simp only [List.count_append,absorb_count]
  omega

theorem Funded.transfer {h : DurableHolders} (hi : h.Funded cs loans w) (step : Transfer w v)
    (keys : KeysCompatible v) (passive : passiveView v = passiveView w) :
    ∃ delta, Handoff w v [] [] delta ∧ (h.absorb delta).Funded cs loans v := by
  obtain ⟨delta,step⟩ := step
  have initial : h.Funded cs (loans ++ []) w := by simpa using hi
  exact ⟨delta,step,by simpa using initial.handoff step keys passive⟩

theorem aligned_initial (net bare : Bool) :
    ({} : DurableHolders).Aligned (Runner.initialWG net bare) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · cases net <;> cases bare <;> rfl
  · intro d hd
    simp only [Runner.initialWG] at hd
    split at hd
    · cases hd; rfl
    · cases hd
  · cases net <;> cases bare <;> rfl
  · intro pid batches found
    simp only [handoffTxView,Runner.initialWG] at found
    split at found
    · simp at found
    · simp at found
  · simp [Runner.initialWG,activeCursor]
  · simp [Runner.initialWG,activeCursor]

theorem boundary_initial (net bare : Bool) : Boundary [] [] (Runner.initialWG net bare) := by
  refine ⟨{},⟨aligned_initial net bare,?_⟩,stable_initial net bare _ rfl⟩
  exact carrier_initial net bare _ rfl

end DurableHolders
end Leanux.Proofs.WG.Queues.RxCredits
