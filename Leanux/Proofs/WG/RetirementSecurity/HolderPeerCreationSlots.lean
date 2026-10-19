import Leanux.Proofs.WG.RetirementSecurity.HolderPeerCreation

/-! The allocated peer initially has no key slots. Original initialization
retains all existing slot anchors, while the actual funded publication adds
exactly its new base occurrence to the independent peer ledger. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

namespace HolderPeerCreation

theorem core_slots (before : SlotPeerReferences holders loans w)
    (device : w.dev=some d) (key : Key) :
    SlotPeerReferences holders loans (Peers.creationCoreWorld w d.nextPeer key) := by
  intro after pid p final stored slots
  have equality : after = {d with nextPeer := d.nextPeer+1, peers := d.peers.insert d.nextPeer (Peers.createdPeer key (w.peerCounter+1))} := by
    simpa [Peers.creationCoreWorld,device] using final.symm
  subst after
  by_cases chosen : d.nextPeer=pid
  · subst pid
    have equal : p=Peers.createdPeer key (w.peerCounter+1) := by simpa using stored.symm
    subst p
    simp [Peers.createdPeer] at slots
  · exact before d pid p device (by simpa [Std.TreeMap.getElem?_insert,chosen] using stored) slots

theorem finish_slots (pid : PeerId) (key : Key) (psk : Option Key) :
    Preserves (SlotPeerReferences holders loans) (BaseCreation.finish pid key psk) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  exact before.transport
    (congrArg (fun s => s.1.1) (BaseCreation.finish_normal pid key psk w v a b run).1)
    ((ProjectedAction.iff_run_ambient _ _ _).mp (finish_points pid key psk) w a () v b run)
    (List.Perm.refl _)

theorem slots (key : Key) (psk : Option Key) (before : SlotPeerReferences holders loans w)
    (a b : Ambient)
    (run : ((peerCreate key psk).run w).run a = .ok ((result,v),b)) :
    SlotPeerReferences holders loans v :=
  (hoare_iff_run_ambient _ _ _).mp
    (source (SlotPeerReferences holders loans) w key psk before
      (fun _ device => core_slots before device key) (fun pid => finish_slots pid key psk))
    w a result v b rfl run

/-- Creation obtains its peer base reference at the actual allocation cut.
That new peer adds no key demand, and existing key holders retain exact credit. -/
theorem accounts (key : Key) (psk : Option Key)
    (keys : HolderAccount temporary w) (peers : holders.Funded carriers loans w)
    (stable : StableRx carriers w) (anchors : SlotPeerReferences holders loans w)
    (configured : ConfiguredIdentity.Inv w) (a b : Ambient)
    (run : ((peerCreate key psk).run w).run a = .ok ((result,v),b)) :
    match result with
    | .error _ => HolderDrain.Ready holders carriers loans temporary v
    | .ok pid => ∃ d,w.dev=some d ∧ pid=d.nextPeer ∧
        HolderDrain.Ready (HolderCreation.addBase holders (BaseCreation.owner w d)) carriers loans temporary v := by
  have kept := HolderPeerCreation.keys key psk keys configured a b run
  have anchored := slots key psk anchors a b run
  have funded := HolderCreation.peerCreate_funded key psk peers stable configured a b run
  cases result with
  | error _ => exact HolderDrain.initial kept funded.1 funded.2 anchored
  | ok pid =>
    obtain ⟨d,device,slot,paid,stable⟩ := funded
    refine ⟨d,device,slot,HolderDrain.initial kept paid stable ?_⟩
    intro out other p final stored slots
    have original := anchored out other p final stored slots
    rcases List.mem_append.mp original with base | loan
    · exact List.mem_append_left _ (List.mem_append_left _ base)
    · exact List.mem_append_right _ loan

end HolderPeerCreation
end Leanux.Proofs.WG.RetirementSecurity
