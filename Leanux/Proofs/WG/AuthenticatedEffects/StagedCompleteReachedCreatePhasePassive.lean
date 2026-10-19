import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePhaseAtoms

/-! Concrete passive segments of the canonical create tree. This covers
ordinary reads, guards, packet-state marks and metadata, while reserving
queue installation, counted repayment and erasure for phase transitions. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CreateDisposal CompleteCarrier StagedTerminalComplete Staged.Obligations
open HandshakeSecurity.StagedDisposal CreatePoints
set_option maxHeartbeats 600000

def PassiveChild : {α : Type} → {action : PrefixM CausalJournal.Event α} → Child action → Prop
  | _,_,.repay _=>True
  | _,_,_=>False

def OnlyPassive : {α : Type} → {action : PrefixM CausalJournal.Event α} → Shape action → Prop
  | _,_,.pure _=>True
  | _,_,.atom token=>Passive token
  | _,_,.child token=>PassiveChild token
  | _,_,.bind head tail=>OnlyPassive head ∧ ∀ value,OnlyPassive (tail value)
  | _,_,.marked _ body=>OnlyPassive body

theorem onlyPassive_cast {left right : PrefixM CausalJournal.Event α}
    (types : Shape left=Shape right) (same : left=right) (shape : Shape left) :
    OnlyPassive (cast types shape)=OnlyPassive shape := by
  cases same
  rfl

theorem passive_child (token : Child action) (passive : PassiveChild token)
    (before : Live rootLedger debts locals pid items h w.wg)
    (performed : runPrefix action w h=(.ok (value,v),last)) : Live rootLedger debts locals pid items last v.wg := by
  cases token with
  | release=>exact passive.elim
  | free=>exact passive.elim
  | repay kid=>exact access_normal _ _ (keypairPutPrefix_erases _ _) (KeyFrames.put kid false) before performed

theorem passive_covers {shape : Shape action} (passive : OnlyPassive shape)
    (before : Live rootLedger debts locals pid items h w.wg) :
    Covers (fun h w=>Live rootLedger debts locals pid items h w.wg) shape w h := by
  induction shape generalizing w h with
  | pure=>exact before
  | atom token=>exact atom_covers token passive before
  | child token=>exact covers_child token before (fun _ _ _ run=>passive_child token passive before run)
  | bind head tail ih rest=>
    have headSafe:=ih passive.1 before
    exact covers_bind headSafe (fun value _ _ run=>rest value (passive.2 value) (headSafe.normal run))
  | marked label shape ih=>exact ih passive before

theorem before_passive (pid : PeerId) (items : List SkbId) : OnlyPassive (beforeShape pid items) := by
  cases items with
  | nil=>exact True.intro
  | cons id rest=>
    change True ∧ ∀ _ : Unit,True ∧ ∀ peer : Peer,True ∧ ∀ full : Bool,_
    refine ⟨trivial,fun _=>⟨trivial,fun _=>⟨trivial,?_⟩⟩⟩
    intro full
    cases full <;> exact True.intro

theorem after_passive (items : List SkbId) : OnlyPassive (afterShape items) := by
  change True ∧ ∀ d : Device,True ∧ ∀ cpu : Int,True ∧ ∀ _ : Unit,True ∧ ∀ full : Bool,_
  refine ⟨trivial,fun _=>⟨trivial,fun _=>⟨trivial,fun _=>⟨trivial,?_⟩⟩⟩⟩
  intro full
  cases full <;> simp [OnlyPassive,Passive]

theorem offered_passive (items : List SkbId) (ret : Int) : OnlyPassive (offeredShape items ret) := by
  unfold offeredShape
  dsimp only
  split
  · erw [onlyPassive_cast _ (by simp_all [offered])]
    exact ⟨trivial,fun _=>trivial⟩
  · erw [onlyPassive_cast _ (by simp_all [offered])]
    split
    · erw [onlyPassive_cast _ (by simp_all <;> grind)]
      exact ⟨trivial,fun _=>trivial⟩
    · erw [onlyPassive_cast _ (by simp_all <;> grind)]
      exact trivial

theorem borrow_passive (items : List SkbId) : OnlyPassive (borrowShape items) := by
  cases items <;> simp [borrowShape,OnlyPassive,Passive,id]

theorem mark_passive (pid : PeerId) (first : SkbId) (state : PacketState) : OnlyPassive (markShape pid first state) := by
  change True ∧ ∀ peer : Peer,_
  refine ⟨trivial,?_⟩
  intro peer
  dsimp only
  split <;> erw [onlyPassive_cast _ (by simp_all <;> grind)] <;> simp only [OnlyPassive,Passive,and_self,forall_const]

theorem schedule_passive (pid : PeerId) : OnlyPassive (scheduleShape pid) := by
  change True ∧ ∀ _ : Nat,True ∧ ∀ d : Device,True ∧ ∀ queued : Bool,_
  refine ⟨trivial,fun _=>⟨trivial,fun _=>⟨trivial,?_⟩⟩⟩
  intro queued
  dsimp only
  split <;> erw [onlyPassive_cast _ (by simp_all <;> grind)] <;> simp only [OnlyPassive,Passive,and_self,forall_const]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
