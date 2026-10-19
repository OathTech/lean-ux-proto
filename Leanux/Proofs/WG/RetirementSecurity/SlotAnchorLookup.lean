import Leanux.Proofs.WG.RetirementSecurity.HolderPeerCreationSlots

/-! Lookup acquisition changes peer counts and nullable embedded owner words,
but cannot create or redirect a published key slot's stamped peer anchor. The
proof observes just the affiliation projection used by the existing lookup. -/
namespace Leanux.Proofs.WG.RetirementSecurity.SlotAnchors
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits Affiliation

def Anchored (owners : List Owner) (s : Affiliation.State) : Prop :=
  ∀ pid p,s.peers pid=some p →
    (p.2.2.1≠none ∨ p.2.2.2.1≠none ∨ p.2.2.2.2≠none) →
    (⟨s.epoch,pid,p.1⟩ : Owner)∈owners

theorem anchored_iff : SlotPeerReferences holders loans w ↔
    ∀ s,Affiliation.view w=some s → Anchored (holders.base++loans) s := by
  constructor
  · intro before s view pid cell resident slots
    obtain ⟨d,device,rfl⟩ := Option.map_eq_some_iff.mp view
    obtain ⟨p,stored,rfl⟩ := Option.map_eq_some_iff.mp resident
    exact before d pid p device stored (by
      change p.keypairCurrent≠none ∨ p.keypairPrevious≠none ∨ p.keypairNext≠none at slots
      rcases slots with current|previous|next
      · exact Or.inr (Or.inr current)
      · exact Or.inr (Or.inl previous)
      · exact Or.inl next)
  · intro before d pid p device stored slots
    apply before (Affiliation.state d) (by simp [Affiliation.view,device]) pid
      (Affiliation.peerCell p) (by simp [Affiliation.state,stored])
    rcases slots with next|previous|current
    · exact Or.inr (Or.inr next)
    · exact Or.inr (Or.inl previous)
    · exact Or.inl current

theorem affiliation {action : WG.M α} (same : SameView Affiliation.view action) :
    Preserves (SlotPeerReferences holders loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have fields := (ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run
  apply anchored_iff.mpr
  intro s found
  exact anchored_iff.mp before s (fields.symm.trans found)

theorem anchored_word (before : Anchored owners s) (owner : IndexOwner) (word : Option PeerId) :
    Anchored owners (s.setWord owner word) := by
  intro pid p resident slots
  cases owner with
  | keypair _ => exact before pid p resident slots
  | handshake other =>
    by_cases same : pid=other
    · subst other
      simp only [Affiliation.State.setWord,ite_true] at resident
      obtain ⟨old,found,rfl⟩ := Option.map_eq_some_iff.mp resident
      exact before pid old found slots
    · exact before pid p (by simpa [Affiliation.State.setWord,same] using resident) slots

theorem acquire (owner : IndexOwner) :
    Preserves (SlotPeerReferences holders loans) (Affiliation.acquireOwner owner) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have fields := (Affiliation.acquireOwner_acquisition owner w v result a b run).facts.2
  apply anchored_iff.mpr
  intro s found
  rw [fields] at found
  obtain ⟨old,resident,rfl⟩ := Option.map_eq_some_iff.mp found
  exact anchored_word (anchored_iff.mp before old resident) owner result

theorem lookup (kinds : List IndexKind) (number : Nat) :
    Preserves (SlotPeerReferences holders loans) (indexLookup kinds number) := by
  rw [←indexLookupSource_eq]
  unfold indexLookupSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head Affiliation.acquireOwner; exact acquire _)
    | (allocation_release_lift_from IndexM; exact index _)
    | (rx_retention_head liftIndex; exact index _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (SlotPeerReferences holders loans)
       intro x u
       change Preserves (SlotPeerReferences holders loans) _)
    | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rxstack_preserves_join
    | rx_retention_step

theorem pubkey_lookup (key : Key) :
    Preserves (SlotPeerReferences holders loans) (pubkeyLookup key) := by
  unfold pubkeyLookup
  simp only [branch]
  repeat' first
    | (rx_retention_head peerGetMaybeZero; exact affiliation (Affiliation.peerGetMaybeZero_view _))
    | (rx_retention_head getDev; exact affiliation (Affiliation.kernel getDev_sameWGStore))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

end Leanux.Proofs.WG.RetirementSecurity.SlotAnchors
