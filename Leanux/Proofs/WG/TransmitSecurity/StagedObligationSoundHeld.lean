import Leanux.Proofs.WG.TransmitSecurity.StagedObligationHeldFrontierFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationCheckedCarrier
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationSelectedClosure
import Leanux.Proofs.WG.AuthenticatedEffects.StagedAllocationLineage

/-! Selected ownership carries semantic receipt evidence as well as physical
backing. The sole active take position prevents an invocation from leaving a
selected ticket behind at an earlier cut. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.SoundHeld
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open Staged.Origins AuthenticatedEffects CausalJournal StagedProvenance
open HandshakeSecurity.StagedConservation

structure Held (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (history : List Event) (w : WGWorld) (a : Ambient) : Prop
    extends HeldFrontier.Held ledger debts generation pid peer position history w a where
  justified : Justified history ledger
  links : AllocationLinks history ledger
  only : OnlySelected position ledger

def Active (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat) (history : List Event) : Prop :=
  HeldFrontier.Anchor ledger debts generation pid peer position history ∧
    Justified history ledger ∧ AllocationLinks history ledger ∧ OnlySelected position ledger

theorem Held.active (before : Held ledger debts generation pid peer position history w a) :
    Active ledger debts generation pid peer position history :=
  ⟨before.anchor,before.justified,before.links,before.only⟩

/-- An append-only fixed-ledger source frame preserves receipt meaning on
both normal and stopped runs. The original source rule supplies the active
take certificate; provenance cannot be invented by a physical view frame. -/
theorem decorate {action : WGPrefix Event α} {Safe : List Event → Prop}
    (admitted : ∀ h, Active ledger debts generation pid peer position h → Safe h)
    (rule : StatePrefixPreserves (HeldFrontier.Held ledger debts generation pid peer position)
      (HeldFrontier.Anchor ledger debts generation pid peer position) action) :
    StatePrefixPreserves (Held ledger debts generation pid peer position) Safe action := by
  intro w a h before
  obtain ⟨suffix,extended,active,after⟩ := rule w a h before.toHeld
  have justified : Justified (runPrefix (action.run w) a h).2 ledger := by
    rw [extended]
    exact before.justified.append suffix
  have links : AllocationLinks (runPrefix (action.run w) a h).2 ledger := by
    rw [extended]
    exact before.links.append suffix
  refine ⟨suffix,extended,admitted _ ⟨active,justified,links,before.only⟩,?_⟩
  cases outcome : (runPrefix (action.run w) a h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    exact ⟨by simpa only [outcome] using after,justified,links,before.only⟩

theorem taken (r : Take.Receipt) (native : r.Valid) (chosen : r.run.value = some peer)
    (before : Core history ledger debts r.run.before)
    (justified : Justified history ledger) (links : AllocationLinks history ledger)
    (idle : NoSelected ledger) :
    ∃ after generation, Step ledger after ∧ Held after debts generation r.pid peer history.length
      (history ++ [.stagingTaken r]) r.run.after r.run.ambientAfter := by
  obtain ⟨after,accounted,core⟩ := core_take r native before
  have transfer := accounted.exactTransfer
  rw [chosen] at transfer
  obtain ⟨generation,epoch,sameLedger,_,aligned⟩ := transfer
  obtain ⟨_,_,same,_,empty,_⟩ := take_receipt_views r native peer chosen
  have vacant : RestoreEntry.Vacant generation r.pid peer.internalId r.run.after := ⟨same.trans epoch,empty⟩
  have base : HeldFrontier.Held after debts generation r.pid peer history.length
      (history ++ [.stagingTaken r]) r.run.after r.run.ambientAfter :=
    ⟨core,vacant,aligned,⟨history,[],r,by simp,rfl,rfl,native,chosen,core,vacant,aligned,by simp⟩⟩
  refine ⟨after,generation,accounted.step,base,?_,?_,take_selected_only r chosen accounted idle⟩
  · rw [sameLedger]
    exact (justified.transfer _ _).append _
  · rw [sameLedger]
    exact (links.transferred _ _ (by intros; simp) (by intros; simp)).append _

/-- The actual checked loop preserves terminal receipt evidence, birth links
and the sole selected location alongside native packet shape. Its two owning
callbacks must discharge the same richer source contract. -/
theorem checked (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (keypair : Option KeypairId) (Safe : List Event → Prop)
    (admitted : ∀ h, Active ledger debts generation pid peer position h → Safe h)
    (Post : List Event → WGWorld → Ambient → Prop) (postSafe : ∀ h w a, Post h w a → Safe h)
    (noKey : Option KeypairId → Bool → WGPrefix Event Unit)
    (submit : KeypairId → List DataPacket → WGPrefix Event Unit)
    (rejected : ∀ kp invalid, StatePrefixEnsures (Held ledger debts generation pid peer position) Safe
      (noKey kp invalid) (fun _ => Post))
    (submitted : ∀ kid packets, StatePrefixEnsures
      (fun h w a => Held ledger debts generation pid peer position h w a ∧
        BatchPayload.Shape pid kid peer.staged packets) Safe (submit kid packets) (fun _ => Post)) :
    StatePrefixEnsures (Held ledger debts generation pid peer position) Safe
      (RestoreEntry.checkedWith liftWGPrefix (fun kid => state (Journal.reserve kid)) noKey submit pid peer keypair)
      (fun _ => Post) :=
  CheckedCarrier.checked (Held ledger debts generation pid peer position) pid peer keypair Safe
    (fun _ _ _ before => admitted _ before.active)
    (fun action => decorate admitted (HeldFrontier.held_ambient (fun _ => id) action))
    (fun action same => decorate admitted (HeldFrontier.held_world (fun _ => id) action same))
    (fun kid => decorate admitted (HeldFrontier.held_read_key (fun _ => id) kid))
    (fun kid => decorate admitted (HeldFrontier.reservation_held (fun _ => id) kid))
    Post postSafe noKey submit rejected submitted

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.SoundHeld
