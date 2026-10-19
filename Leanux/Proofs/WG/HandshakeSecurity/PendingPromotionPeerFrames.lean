import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionHistory
import Leanux.Proofs.WG.RetirementSecurity.CarrierFrames

/-! Native peer metadata and key borrowing retain pending allocation tickets.
Saved-peer writes are tied to the actual preceding read, so arbitrary caller
records cannot introduce a pending ticket. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Origins

theorem peer_write (w : WGWorld) (d : Device) (pid : PeerId) (old p : Peer)
    (device : w.dev = some d) (resident : d.peers[pid]? = some old)
    (same : p.keypairNext = old.keypairNext) :
    view {w with dev := some {d with peers := d.peers.insert pid p}} = view w := by
  have keys : keypairResidents {w with dev := some {d with peers := d.peers.insert pid p}} =
      keypairResidents w := by
    funext kid
    simp only [keypairResidents,device,Option.bind_some]
  apply Store.ext
  · rfl
  · funext q
    by_cases equal : pid = q
    · subst q
      simp [view,nextSlot,keys,device,resident,same]
    · simp [view,nextSlot,keys,device,Std.TreeMap.getElem?_insert,equal]

theorem modify_peer (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, (f p).keypairNext = p.keypairNext) :
    SameView view (do let p ← getPeer pid; setPeer pid (f p)) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,read,write⟩ := run
  obtain ⟨sameWorld,sameAmbient,d,device,resident⟩ := getPeer_normal pid w u p a c read
  subst u c
  cases result
  have actual : v = {w with dev := some {d with peers := d.peers.insert pid (f p)}} ∧ b = a := by
    simpa [setPeer,modifyDev,device] using write.symm
  rw [actual.1]
  exact peer_write w d pid p (f p) device resident (same p)

theorem key_get (kid : Option KeypairId) : SameView view (keypairGet kid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have carriers := (ProjectedAction.iff_run_ambient _ _ _).mp
    (RetirementSecurity.get_carriers kid) w a result v b run
  have peers := congrArg Prod.fst carriers
  have keys := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Keypairs.keypairGet_sameSnapshot kid) w a result v b run
  apply Store.ext
  · exact congrArg Keypairs.Snapshot.frontier keys
  · funext pid
    have slots := congrArg (fun maps => (maps.bind fun table => table[pid]?).bind Peer.keypairNext) peers
    have slots : nextSlot v pid = nextSlot w pid := by
      simpa only [RetirementSecurity.carrierShape,RetirementSecurity.peersAt,nextSlot,
        Option.bind_map,Function.comp_def] using slots
    simp only [view,slots,key_snapshot keys]

theorem Carrier.join (confirmed : List Nat) {action : WG.M α}
    (configured : Preserves ConfiguredIdentity.Inv action)
    (slots : Preserves CurrentSlots.Inv action)
    (pending : Preserves (Inv confirmed) action) : Preserves (Carrier confirmed) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp configured _ _ _ _ _ hi.1 run,
    (hoare_iff_run_ambient _ _ _).mp slots _ _ _ _ _ hi.2.1 run,
    (hoare_iff_run_ambient _ _ _).mp pending _ _ _ _ _ hi.2.2 run⟩

theorem Carrier.key_get (confirmed : List Nat) (kid : Option KeypairId) :
    Preserves (Carrier confirmed) (keypairGet kid) :=
  Carrier.join confirmed
    (ConfiguredRemoval.frame
      ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentTraffic.«0».Leanux.Proofs.WG.CurrentTraffic.keypairGet_view) kid))
    (CurrentSlots.keypairGet_preserves kid) (frame_preserves (PendingPromotion.key_get kid) confirmed)

theorem Carrier.get_peer (confirmed : List Nat) (pid : PeerId) :
    Hoare (getPeer pid) (Carrier confirmed)
      (fun p w => Carrier confirmed w ∧ Responder.SavedNativePeer pid p w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi run
  obtain ⟨rfl,rfl,d,device,resident⟩ := getPeer_normal pid w v p a b run
  exact ⟨hi,d,device,resident⟩

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
