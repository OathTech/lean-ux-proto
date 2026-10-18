import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverCuts
import Leanux.Proofs.WG.HandshakeSecurity.ResponderPeerConfiguration

/-! The state-only source carrier needed by the shared driver. It carries the
configured-peer invariant and current-slot bounds directly; no RX history is
assumed to exist at a TX cut. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Origins Origins.Retaining Lifetimes Queues

def Carrier (confirmed : List Nat) (w : WGWorld) : Prop :=
  ConfiguredIdentity.Inv w ∧ History.Native confirmed w

theorem Carrier.initial (net bare : Bool) : Carrier [] (Runner.initialWG net bare) :=
  ⟨ConfiguredMaintenance.configured_initial net bare _ rfl, History.Native.initial net bare⟩

theorem carrier_join {action : WG.M α} (confirmed : List Nat)
    (configured : Preserves ConfiguredIdentity.Inv action)
    (native : Preserves (History.Native confirmed) action) :
    Preserves (Carrier confirmed) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp configured _ _ _ _ _ hi.1 run,
    (hoare_iff_run_ambient _ _ _).mp native _ _ _ _ _ hi.2 run⟩

theorem carrier_frame {action : WG.M α} (confirmed : List Nat)
    (configured : SameView ConfiguredIdentity.view action)
    (native : Preserves (History.Native confirmed) action) :
    Preserves (Carrier confirmed) action :=
  carrier_join confirmed (ConfiguredRemoval.frame configured) native

/-- The source session retains configured identity and derives slot bounds from
that same actual entry; the H1 current-edge premise stays explicit. -/
theorem carrier_session (H1 : H1ResponderCurrentEdges) (pid : PeerId)
    (confirmed : List Nat) : Preserves (Carrier confirmed) (beginSession pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp
      (ConfiguredRemoval.frame (ConfiguredMaintenance.beginSession_view pid)) _ _ _ _ _ hi.1 run,
    session_authorizes H1 pid confirmed ⟨result,w,v,a,b⟩ hi run⟩

/-- The current slot is authorized immediately after native confirmation. This
carrier is suitable for staging inside an otherwise stopped consumer. -/
theorem carrier_confirmation (H1 : H1ResponderCurrentEdges) (pid : PeerId)
    (kid : KeypairId) (confirmed : List Nat) (r : WGRunWitness Bool)
    (valid : r.Valid (receivedWithKeypair pid kid)) (hi : Carrier confirmed r.before) :
    Carrier (confirmed ++ confirmedAt r.before kid r.value) r.after :=
  ⟨(hoare_iff_run_ambient _ _ _).mp
      (ConfiguredRemoval.frame
        ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentTraffic.«0».Leanux.Proofs.WG.CurrentTraffic.receivedWithKeypair_view) pid kid))
      _ _ _ _ _ hi.1 valid,
    confirmation_native H1 pid kid confirmed r valid hi.2⟩

theorem carrier_borrow (kid : Option KeypairId) (confirmed : List Nat) :
    Preserves (Carrier confirmed) (keypairGet kid) :=
  carrier_frame confirmed
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentTraffic.«0».Leanux.Proofs.WG.CurrentTraffic.keypairGet_view) kid)
    (borrowKey_native kid confirmed)

theorem carrier_read (pid : PeerId) (confirmed : List Nat) :
    Hoare (getPeer pid) (Carrier confirmed)
      (fun p w => Carrier confirmed w ∧ SavedNativePeer pid p w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi run
  obtain ⟨rfl, rfl, d, device, peer⟩ := getPeer_normal pid w v p a b run
  exact ⟨hi,d,device,peer⟩

theorem carrier_write (pid : PeerId) (p : Peer) (f : Peer → Peer)
    (slots : ∀ p, CurrentSlots.slotCell (f p) = CurrentSlots.slotCell p)
    (configured : ∀ p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p)
    (confirmed : List Nat) :
    Hoare (setPeer pid (f p))
      (fun w => Carrier confirmed w ∧ SavedNativePeer pid p w)
      (fun _ => Carrier confirmed) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  obtain ⟨d, device, peer⟩ := hi.2
  have getter : ((getPeer pid).run w).run a = .ok ((p,w),a) := by
    simp [getPeer,getDev,device,peer]
  have whole : (((getPeer pid >>= fun p => setPeer pid (f p)) : WG.M Unit).run w).run a =
      .ok ((result,v),b) := by
    rw [MaterialOrigin.bind_ok_ambient]
    exact ⟨p,w,a,getter,run⟩
  exact (hoare_iff_run_ambient _ _ _).mp
    (carrier_frame confirmed (ConfiguredIdentity.modifyPeer_view pid f configured)
      (peerUpdate_native pid f slots confirmed)) _ _ _ _ _ hi.1 whole

/-- The original staging prefix preserves the smaller carrier. The saved peer
is connected to the actual read through the branch before its queue is cleared. -/
theorem carrier_selection (pid : PeerId) (confirmed : List Nat) :
    Preserves (Carrier confirmed) (selectionPrefix pid) := by
  unfold selectionPrefix
  apply hoare_bind _ _ (carrier_read pid confirmed)
  intro p
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .stagedEmpty p.staged.isEmpty) _)
  intro empty
  cases empty with
  | true =>
    exact hoare_consequence (preserves_pure none)
      (fun _ hi => hi.1) (fun _ _ hi => hi)
  | false =>
    apply hoare_bind _ _ (carrier_write pid p (fun p => {p with staged := []})
      (fun _ => rfl) (fun _ => rfl) confirmed)
    intro _
    exact preserves_bind (carrier_borrow p.keypairCurrent confirmed)
      (fun kp => preserves_pure (some (p,kp)))

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
