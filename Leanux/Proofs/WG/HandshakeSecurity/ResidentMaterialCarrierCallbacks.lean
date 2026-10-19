import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialReceiveFrames

/-! Shared source callbacks for the resident-material carrier. Receive-triggered
staging and encryption use this same journal, including pre-Stop AEAD receipts. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder
set_option maxHeartbeats 600000

theorem carrier_quiet {g : WGPrefix Journal.Event α} {action : WG.M α}
    (app : StateAppends g) (quiet : StateHistoryFrame Journal.encryption? g)
    (erase : ErasesStatePrefix g action) (native : ∀ h, Preserves (Inv h) action)
    (bounds : Preserves Bounds action) : CarrierSafe g := by
  apply state_quiet_extra app quiet erase
  intro h
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (native h) w a x v b hi.1 run,
    (hoare_iff_run_ambient _ _ _).mp bounds w a x v b hi.2 run⟩

theorem carrier_pure (x : α) : CarrierSafe (pure x) :=
  StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1.2) (fun _ _ _ hi => hi)

theorem carrier_ambient (action : AmbientM α) : CarrierSafe (liftWGPrefix (monadLift action)) :=
  carrier_lift _ (fun _ => hoare_liftAmbient _ _) (hoare_liftAmbient _ _)

def Saved (pid : PeerId) (peer : Peer) (h : List Journal.Event) (w : WGWorld) : Prop :=
  Carrier h w ∧ SavedNativePeer pid peer w

theorem read_saved (pid : PeerId) :
    StatePrefixEnsures (fun h w _ => Carrier h w) Safe (liftWGPrefix (getPeer pid))
      (fun peer h w _ => Saved pid peer h w) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1.2)
  intro h w a peer v b hi run
  obtain ⟨rfl,rfl,d,device,resident⟩ := getPeer_normal pid w v peer a b run
  exact ⟨hi,d,device,resident⟩

theorem saved_ambient (pid : PeerId) (peer : Peer) (action : AmbientM α) :
    StatePrefixPreserves (fun h w _ => Saved pid peer h w) Safe (liftWGPrefix (monadLift action)) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1.1.2)
  intro h w a x v b hi run
  exact (hoare_iff_run_ambient _ _ _).mp (hoare_liftAmbient action (Saved pid peer h)) w a x v b hi run

theorem saved_store (pid : PeerId) (peer : Peer) (action : WG.M α) (frame : SameWGStore action) :
    StatePrefixPreserves (fun h w _ => Saved pid peer h w) Safe (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1.1.2)
  intro h w a x v b hi run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp frame w a x v b run
  have device : v.dev = w.dev := congrArg WGStoreView.dev same
  refine ⟨⟨⟨(hoare_iff_run_ambient _ _ _).mp (NativeFrames.store frame) w a x v b hi.1.1.1 run,hi.1.1.2⟩,
    (hoare_iff_run_ambient _ _ _).mp (bounds_store frame) w a x v b hi.1.2 run⟩,?_⟩
  obtain ⟨d,hd,hp⟩ := hi.2
  exact ⟨d,device.trans hd,hp⟩

theorem write_saved (pid : PeerId) (peer : Peer) (f : Peer → Peer)
    (slots : ∀ p, CurrentSlots.slotCell (f p) = CurrentSlots.slotCell p)
    (identity : ∀ p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p) :
    StatePrefixEnsures (fun h w _ => Saved pid peer h w) Safe (liftWGPrefix (setPeer pid (f peer)))
      (fun _ h w _ => Carrier h w) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1.1.2)
  intro h w a x v b hi run
  obtain ⟨d,device,resident⟩ := hi.2
  have getter : ((getPeer pid).run w).run a = .ok ((peer,w),a) := by simp [getPeer,getDev,device,resident]
  have whole : (((do let p ← getPeer pid; setPeer pid (f p)) : WG.M Unit).run w).run a = .ok ((x,v),b) := by
    rw [MaterialOrigin.bind_ok_ambient]
    exact ⟨peer,w,a,getter,run⟩
  exact ⟨⟨(hoare_iff_run_ambient _ _ _).mp (NativeFrames.set_peer pid _) w a x v b hi.1.1.1 run,hi.1.1.2⟩,
    (hoare_iff_run_ambient _ _ _).mp (bounds_update pid f slots identity) w a x v b hi.1.2 whole⟩

theorem forget_saved (pid : PeerId) (peer : Peer) {g : WGPrefix Journal.Event α} (safe : CarrierSafe g) :
    StatePrefixEnsures (fun h w _ => Saved pid peer h w) Safe g (fun _ h w _ => Carrier h w) :=
  safe.consequence (fun _ _ _ hi => hi.1) (fun _ _ _ _ hi => hi)

theorem keepalive_carrier (pid : PeerId) : CarrierSafe (Driver.keepaliveObserved Journal.hooks pid) := by
  rw [Driver.keepalive_native _ rfl]
  unfold Driver.keepaliveInline
  apply StatePrefixEnsures.bind (read_saved pid)
  intro peer
  apply StatePrefixEnsures.bind (saved_ambient pid peer _)
  intro empty
  split
  · apply StatePrefixEnsures.bind (saved_ambient pid peer _)
    intro allocated
    apply StatePrefixEnsures.bind (saved_ambient pid peer _)
    intro failed
    split
    · exact forget_saved pid peer (carrier_pure ())
    · apply StatePrefixEnsures.bind (saved_store pid peer getDev getDev_sameWGStore)
      intro d
      apply StatePrefixEnsures.bind (write_saved pid peer
        (fun p => {p with staged := p.staged ++ [{mtu := d.mtu}]}) (fun _ => rfl) (fun _ => rfl))
      intro _
      exact staging_carrier pid
  · exact forget_saved pid peer (staging_carrier pid)

theorem confirmation_carrier (pid : PeerId) (kid : KeypairId) : CarrierSafe (Journal.confirmation pid kid) :=
  carrier_quiet (StateAppends.focus _ _ _)
    (fun w => focusPrefix_other _ _ _ (fun _ => rfl) ((DriverCuts.confirmation pid kid).run w))
    (focusStatePrefix_erases _ _ (DriverCuts.confirmation_erases pid kid))
    (fun _ => NativeFrames.confirmation pid kid) (bounds_confirmation pid kid)

theorem receive_tail_carrier (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    CarrierSafe (Driver.receiveTailObserved Journal.hooks pid pkt confirmed) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold Driver.receiveTailObserved
  simp only [Driver.nested_prepare_lift Journal.hooks rfl rfl,Driver.rxFinish_lift Journal.hooks rfl]
  repeat' first
    | (nonce_source_head Driver.stagingObserved; exact staging_carrier _)
    | (nonce_source_head timersHandshakeComplete; exact carrier_lift _ (fun _ => NativeFrames.complete _ _) (bounds_complete _ _))
    | (nonce_source_head RxCredits.prepareRest; exact carrier_lift _ (fun _ => NativeFrames.prepare _ _) (bounds_prepare _ _))
    | (nonce_source_head Packets.rxFinish; exact carrier_lift _ (fun _ => NativeFrames.finish _ _) (bounds_finish _ _))
    | (nonce_source_head branch; exact carrier_ambient _)
    | (nonce_source_head Pure.pure; exact carrier_pure _)
    | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
    | split
    | (with_reducible intro x; try dsimp only)

theorem consume_carrier (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    CarrierSafe (Driver.consumeObserved Journal.hooks pid pkt ep) := by
  unfold Driver.consumeObserved
  dsimp only [Journal.hooks]
  apply StatePrefixEnsures.bind (carrier_lift _ (fun _ => NativeFrames.endpoint pid ep) (bounds_endpoint pid ep))
  intro _
  apply StatePrefixEnsures.bind (confirmation_carrier pid pkt.keypair)
  intro confirmed
  exact receive_tail_carrier pid pkt confirmed

theorem encrypt_carrier (item : Option (List SkbId)) :
    PrefixPreserves (fun h w => Carrier h w.wg) Safe (Journal.encrypt item) := by
  intro w h hi
  obtain ⟨suffix,eq,safe,post⟩ := encrypt item w h hi.1
  refine ⟨suffix,eq,safe,?_⟩
  cases result : (runPrefix (Journal.encrypt item) w h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨value,v⟩ := out
    simp only [result] at post
    have native : (RxWorkers.encryptStepTailSource item).run w = .ok (value,v) := by
      have projected := congrArg Prod.fst (Journal.encrypt_projects item w h)
      rw [result] at projected
      exact projected
    exact ⟨post,(hoare_iff_run _ _ _).mp (bounds_encrypt item) w value v hi.2 native⟩

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
