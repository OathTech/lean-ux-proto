import Leanux.Proofs.WG.RetirementSecurity.RxCompletionOccurrences
import Leanux.Proofs.WG.Queues.TxHolderStep

/-! Actual peer-holder funding discharges the final-peer-release side
condition at TX disposal. It is deliberately separate from key-reference
credit. A peer with published key slots retains a base or caller reference;
detached base references can live in the native removal caller's loans. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

/-- Published key slots retain a peer base/caller reference independently of
queued TX batch references. Native removal may detach the base into loans
before clearing the slots, so membership in peerList alone is too strong at
that internal source cut. Initialized whole-driver transport is separate. -/
def SlotPeerReferences (holders : DurableHolders) (loans : Reservations) (w : WGWorld) : Prop :=
  ∀ d pid p, w.dev = some d → d.peers[pid]? = some p →
    (p.keypairNext ≠ none ∨ p.keypairPrevious ≠ none ∨ p.keypairCurrent ≠ none) →
    (⟨d.ifindex,pid,p.internalId⟩ : Owner) ∈ holders.base ++ loans

theorem initial_slot_peer_references (net bare : Bool) :
    SlotPeerReferences {} [] (Runner.initialWG net bare) := by
  intro d pid p device found slots
  unfold Runner.initialWG at device
  split at device
  · cases device
    simp at found
  · cases device

theorem selected_peer_release_funded {holders : DurableHolders}
    (funded : holders.Funded carriers loans w)
    (anchors : SlotPeerReferences holders loans w)
    (selected : DurableHolders.TxSelected holders.tx pid chosen rest) : PeerReleaseFunded pid w := by
  intro p found
  obtain ⟨d,device,stored⟩ := Option.bind_eq_some_iff.mp found
  have chosenMember : chosen ∈ holders.tx := selected.perm.mem_iff.mpr (by simp)
  have ownerMember : chosen.owner ∈ holders.tx.map TxHandoff.owner := List.mem_map.mpr ⟨chosen,chosenMember,rfl⟩
  have allMember : chosen.owner ∈ holders.owners := by simp [DurableHolders.owners,ownerMember]
  obtain ⟨q,resident⟩ := funded.resident allMember
  obtain ⟨old,oldDevice,epoch,oldStored,stamp⟩ := resident_fields resident
  have devices : old = d := Option.some.inj (oldDevice.symm.trans device)
  subst old
  rw [selected.slot] at oldStored
  have peers : q = p := Option.some.inj (oldStored.symm.trans stored)
  subst q
  have owner : chosen.owner = ⟨d.ifindex,pid,p.internalId⟩ := by
    have slot := selected.slot
    cases own : chosen.owner
    simp only [own] at epoch stamp slot
    simp_all
  have budget := funded.carriers.funded chosen.owner
  have balanceEq : RxCredits.balance w chosen.owner = p.refcount := by
    simp [RxCredits.balance,resident]
  rw [balanceEq] at budget
  have txPositive : 0 < (holders.tx.map TxHandoff.owner).count chosen.owner :=
    List.count_pos_iff.mpr ownerMember
  simp only [demand,DurableHolders.owners,List.count_append] at budget
  refine ⟨by omega,?_⟩
  intro final
  have noSlots : ¬ (p.keypairNext ≠ none ∨ p.keypairPrevious ≠ none ∨ p.keypairCurrent ≠ none) := by
    intro slots
    have anchored := anchors d pid p device stored slots
    rw [← owner] at anchored
    have positive := List.count_pos_iff.mpr anchored
    simp only [List.count_append] at positive
    omega
  refine ⟨?_,?_,?_⟩
  · by_cases same : p.keypairNext = none
    · exact same
    · exact False.elim (noSlots (Or.inl same))
  · by_cases same : p.keypairPrevious = none
    · exact same
    · exact False.elim (noSlots (Or.inr (Or.inl same)))
  · by_cases same : p.keypairCurrent = none
    · exact same
    · exact False.elim (noSlots (Or.inr (Or.inr same)))

/-- Full native TX iteration derives peer-release readiness from its selected
actual batch and the independently funded base/caller occurrence. Idle
iterations need no peer-release premise. Key accounting remains its own
incoming invariant; physical uniqueness supplies the disposal separation. -/
theorem HolderAccount.tx_step_holders (account : HolderAccount temporary w)
    (inventory : TxInventory locals w) (funded : holders.Funded carriers loans w)
    (stable : StableRx carriers w) (anchors : SlotPeerReferences holders loans w)
    (pid : PeerId) (a b : Ambient)
    (run : ((txStep pid).run w).run a = .ok ((result,v),b)) : HolderAccount temporary v := by
  rcases DurableHolders.txStep_funded pid funded stable a b run with idle | active
  · obtain ⟨rfl,_,_⟩ := idle
    exact account.tx_stopped pid a b run
  · obtain ⟨rfl,chosen,rest,_,selected,_,_,_,_⟩ := active
    exact account.tx_step (inventory.separated pid)
      (selected_peer_release_funded funded anchors selected) a b run

end Leanux.Proofs.WG.RetirementSecurity
