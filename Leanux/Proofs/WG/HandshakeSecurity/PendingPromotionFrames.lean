import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionH1
import Leanux.Proofs.WG.HandshakeSecurity.RetentionFrames
import Leanux.Proofs.WG.Lifetimes.AllocationReleaseFrames
import Leanux.Proofs.WG.Keypairs.Frames.WGTransitions
import Leanux.Proofs.WG.Queues.CurrentSlotFrames
import Leanux.Proofs.WG.RetirementSecurity.Frames

/-! Frames for the pending-allocation projection. These are independent of
confirmation history; the history invariant follows from the C1 retained-store
laws. Native H1 session/rotation facts are kept in their separate package. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do

theorem retained (w v : WGWorld) (counter : v.keypairCounter = w.keypairCounter)
    (slots : ResidentsRetained (nextSlot w) (nextSlot v))
    (keys : ResidentsRetained (keypairResidents w) (keypairResidents v)) :
    Retained (view w) (view v) := by
  refine ⟨counter,?_⟩
  intro pid stamp present
  obtain ⟨kid,slot,key⟩ := Option.bind_eq_some_iff.mp present
  exact Option.bind_eq_some_iff.mpr ⟨kid,slots pid kid slot,keys kid stamp key⟩

theorem next_fields (same : CurrentSlots.fields v = CurrentSlots.fields w) :
    nextSlot v = nextSlot w := by
  funext pid
  have slots := congrFun (congrArg (fun t => t.2.1) same) pid
  have next := congrArg (fun item => item.bind (fun cell => cell.2.2)) slots
  simpa only [CurrentSlots.fields,CurrentSlots.slotCell,nextSlot,Option.bind_map,
    Option.bind_assoc,Function.comp_def] using next

theorem key_snapshot (same : Keypairs.snapshot v = Keypairs.snapshot w) :
    keypairResidents v = keypairResidents w := by
  funext kid
  have keys := congrFun (congrArg Keypairs.Snapshot.slots same) kid
  have stamps := congrArg (fun item => item.map Keypairs.Cell.stamp) keys
  simpa only [Keypairs.snapshot,Keypairs.cell,keypairResidents,Option.map_map,
    Function.comp_def] using stamps

theorem view_fields (slots : CurrentSlots.fields v = CurrentSlots.fields w)
    (keys : Keypairs.snapshot v = Keypairs.snapshot w) : view v = view w := by
  apply Store.ext
  · exact congrArg Keypairs.Snapshot.frontier keys
  · funext pid
    simp only [view,next_fields slots,key_snapshot keys]

theorem frame {action : WG.M α} (slots : SameView CurrentSlots.fields action)
    (keys : Keypairs.SameSnapshot action) : SameView view action := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  exact view_fields
    ((ProjectedAction.iff_run_ambient _ _ _).mp slots w a x v b run)
    ((ProjectedAction.iff_run_ambient _ _ _).mp keys w a x v b run)

theorem preserves {action : WG.M α} (effect : ProjectedAction view Retained action)
    (confirmed : List Nat) : Preserves (Inv confirmed) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  exact hi.retained ((ProjectedAction.iff_run_ambient _ _ _).mp effect w a x v b run)

theorem frame_preserves {action : WG.M α} (same : SameView view action)
    (confirmed : List Nat) : Preserves (Inv confirmed) action := by
  apply preserves _ confirmed
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  rw [(ProjectedAction.iff_run_ambient _ _ _).mp same w a x v b run]
  exact Retained.refl _

theorem store {action : WG.M α} (same : SameWGStore action) : SameView view action := by
  apply same.of_factor
    (fun s : WGStoreView => (⟨s.keypairCounter,fun pid =>
      ((s.dev.bind fun d => d.peers[pid]?).bind Peer.keypairNext).bind
        (fun kid => (s.dev.bind fun d => d.keypairs[kid]?).map Keypair.internalId)⟩ : Store PeerId))
  intro w
  rfl

theorem key_put (kid : Option KeypairId) (now : Bool) :
    ProjectedAction view Retained (keypairPut kid now) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  have allocation := keypairPut_retention kid now w v a b run
  have peers := RetirementSecurity.put_peers kid now w v a b run
  apply retained w v (congrArg AllocationMetadata.keyCounter allocation.metadata) _ allocation.key
  intro pid slot present
  have same := congrArg (fun maps => (maps.bind fun table => table[pid]?).bind Peer.keypairNext) peers
  have same : nextSlot v pid = nextSlot w pid := by
    simpa only [nextSlot,RetirementSecurity.peersAt,Option.bind_map,Function.comp_def] using same
  rwa [same] at present

theorem peer_put (pid : Option PeerId) : ProjectedAction view Retained (peerPut pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  have allocation := peerPut_retention pid w v a b run
  have peers := peerPut_retains_handshake pid w v a b x run
  apply retained w v (congrArg AllocationMetadata.keyCounter allocation.metadata) _ allocation.key
  intro q kid present
  obtain ⟨p,resident,next⟩ := Option.bind_eq_some_iff.mp present
  have before := peers q (handshakeView p) (by simp only [peerView,resident,Option.map_some])
  obtain ⟨old,found,same⟩ := Option.map_eq_some_iff.mp before
  have slots := congrArg HandshakeView.next same
  exact Option.bind_eq_some_iff.mpr ⟨old,found,slots.trans next⟩

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
