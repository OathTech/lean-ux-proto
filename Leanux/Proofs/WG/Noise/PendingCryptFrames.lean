import Leanux.Proofs.WG.Noise.PendingPollCompleteSource
import Leanux.Proofs.WG.Noise.PendingReceptionSource
import Leanux.Proofs.WG.Noise.PendingControlSource
import Leanux.Proofs.WG.Noise.PendingTicketStagingFrames
import Leanux.Proofs.WG.Queues.CurrentSlotWorkers
import Leanux.Proofs.WG.Origins.ConfiguredTraffic

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingCrypt
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues PendingSession

theorem getKeypair_native (kid : KeypairId) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (getKeypair kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient k v after hi run
  exact (KeyTimes.getKeypair_return kid w v k ambient after run).1 ▸ hi

theorem encryptPoll_native (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) TxRing.pollSource := by
  unfold TxRing.pollSource
  apply preserves_bind (PendingReception.native_store _ getDev_sameWGStore seen)
  intro d
  exact preserves_bind
    (PendingReception.native_modifyDevice
      (fun q => {q with encryptQueue := d.encryptQueue.consume.2})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) seen)
    (fun _ => preserves_pure _)

theorem enqueue_native (item : List SkbId) (state : PacketState) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (enqueuePerPeerTx item state) :=
  PendingReception.native_preserves _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredTraffic.«0».Leanux.Proofs.WG.ConfiguredTraffic.enqueue) item state)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotTraffic.«0».Leanux.Proofs.WG.CurrentSlots.enqueuePeer_preserves) item state)
    (PendingTickets.retained_of_staging_ordinary _
      (fun entry => (ensures_iff _ _ _).mpr (Index.enqueuePerPeerTx_staging item state entry))
      (Keypairs.SameView.ordinary (Keypairs.WGTransitions.enqueuePerPeerTx_sameSnapshot item state))) seen

/-- Cached key edits retain pending stamps when the actual loaded stamp is kept. -/
theorem key_update_pending (kid : KeypairId) (f : Keypair → Keypair)
    (stamp : ∀ k, (f k).internalId = k.internalId) :
    SameView PendingTickets.view (getKeypair kid >>= fun k => setKeypair kid (f k)) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v after run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨k,read,middle,hread,hwrite⟩ := run
  obtain ⟨readEq,_,d,device,resident⟩ := KeyTimes.getKeypair_return kid w read k ambient middle hread
  subst read
  cases hwrite
  have keys : keypairResidents
      {w with dev := some {d with keypairs := d.keypairs.insert kid (f k)}} = keypairResidents w := by
    funext q
    by_cases same : kid = q
    · subst q; simp [keypairResidents,device,resident,stamp]
    · simp [keypairResidents,device,Std.TreeMap.getElem?_insert,same]
  change PendingTickets.view {w with dev := w.dev.map (fun d => {d with keypairs := d.keypairs.insert kid (f k)})} = _
  simp only [device,Option.map_some]
  apply Store.ext
  · rfl
  · funext pid
    rw [PendingTickets.view_slot,PendingTickets.view_slot,keys]
    simp only [PendingTickets.nextSlots,device,Option.bind_some]

theorem key_update_native (kid : KeypairId) (f : Keypair → Keypair)
    (cell : ∀ k, Affiliation.keyCell (f k) = Affiliation.keyCell k)
    (stamp : ∀ k, (f k).internalId = k.internalId) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (getKeypair kid >>= fun k => setKeypair kid (f k)) :=
  PendingReception.native_preserves _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredTraffic.«0».Leanux.Proofs.WG.ConfiguredTraffic.keyUpdate) kid f)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotTraffic.«0».Leanux.Proofs.WG.CurrentSlots.keyUpdate) kid f cell)
    (PendingTickets.retained_of_frame (key_update_pending kid f stamp)) seen

theorem peerGet_native (pid : PeerId) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (peerGet pid) :=
  PendingReception.native_view _ (RxCredits.CreationLoan.peerGet_configured_view pid)
    (CurrentSlots.fields_preserves (project := id) (CurrentSlots.peerGet_fields pid))
    (PendingTickets.frame_from_fields (CurrentSlots.peerGet_fields pid)
      (Keypairs.WGFrames.peerGet_sameSnapshot pid)) seen

/-- The setter is justified by its actual still-resident saved peer. -/
theorem publish_setter (pid : PeerId) (p : Peer) (seen : List Nat) :
    Hoare (setPeer pid {p with napiScheduled := true})
      (fun w => NativeInv w seen ∧ (w.dev.bind fun d => d.peers[pid]?) = some p)
      (fun _ w => NativeInv w seen) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v after hi run
  obtain ⟨d,device,resident⟩ := Option.bind_eq_some_iff.mp hi.2
  have read : ((getPeer pid).run w).run ambient = .ok ((p,w),ambient) := by
    simp [getPeer,getDev,device,resident]
  have original : (((getPeer pid >>= fun q => setPeer pid {q with napiScheduled := true}).run w).run ambient) =
      .ok ((result,v),after) := by
    rw [MaterialOrigin.bind_ok_ambient]
    exact ⟨p,w,ambient,read,run⟩
  exact (hoare_iff_run_ambient _ _ _).mp
    (PendingReception.native_update pid (fun q => {q with napiScheduled := true})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) seen)
    w ambient result v after hi.1 original


end Leanux.Proofs.WG.Noise.PendingCrypt
