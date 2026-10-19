import Leanux.Proofs.WG.Origins.OwnerBounds
import Leanux.Proofs.WG.Lifetimes.PeerAllocation
import Leanux.Proofs.WG.Origins.CurrentSession
import Leanux.Proofs.WG.Origins.CurrentLifecycle

/-! The concrete creation/session cuts preserve the receiving-owner carrier.
The session result uses its actual front receipt; no arbitrary key derivation
or initialized whole-program invariant is assumed. -/
namespace Leanux.Proofs.WG.OwnerCreation
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues.RxCredits OwnerBounds

private theorem peerCreate_rx (key : Key) (psk : Option Key) :
    SameView rxView (peerCreate key psk) := by
  intro initial
  let P : WGWorld → Prop := fun w => rxView w = initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have read (pid : PeerId) : Preserves P (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b hi hr
    obtain ⟨rfl, _, _, _, _⟩ := Origins.getPeer_return _ _ _ _ _ _ hr
    exact hi
  have device : Preserves P getDev := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a d v b hi hr
    cases hd : w.dev <;> simp [getDev, hd, invariant, AmbientM.invariant] at hr
    · cases hr
    · rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      exact hi
  have write (pid : PeerId) (p : Peer) : Preserves P (setPeer pid p) := by
    unfold setPeer modifyDev
    apply hoare_modify
    intro w hi
    cases hd : w.dev <;> simpa [P, rxView, hd] using hi
  have precompute (pid : PeerId) : Preserves P (precomputeStaticStatic pid) := by
    unfold precomputeStaticStatic
    simp (config := {zeta := false}) only [requireNotPending, branch]
    repeat' first
      | (allocation_release_head getPeer; exact read _)
      | (allocation_release_head getDev; exact device)
      | (allocation_release_head setPeer; exact write _ _)
      | (allocation_release_lift_from AmbientM; exact ambient _)
      | allocation_release_step
  change Preserves P (peerCreate key psk)
  unfold peerCreate handshakeInit IndexOwner.setPeerWord dstCacheReset resetLastSentHandshake
  simp (config := {zeta := false}) only
    [branch, branchCmp, hiddenAlloc, hiddenJiffies, hiddenClock64, getAmbient]
  repeat' first
    | (allocation_release_head precomputeStaticStatic; exact precompute _)
    | (allocation_release_head getPeer; exact read _)
    | (allocation_release_head getDev; exact device)
    | (allocation_release_head setPeer; exact write _ _)
    | (allocation_release_head modifyDev; unfold modifyDev)
    | (allocation_release_head modify; apply hoare_modify; intro w hi;
        cases hd : w.dev <;> simpa [P, rxView, hd] using hi)
    | (allocation_release_head get; exact hoare_consequence (hoare_get P)
        (fun _ h => h) (fun _ _ h => h.2))
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | allocation_release_step

theorem peerCreate_preserves (key : Key) (psk : Option Key) :
    Preserves OwnerBounds.Carrier (peerCreate key psk) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  have geometry := peerCreate_geometry key psk w v result a b hr
  have material := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Origins.Retaining.peerCreate_material key psk) w a result v b hr
  have rx := (ProjectedAction.iff_run_ambient _ _ _).mp
    (peerCreate_rx key psk) w a result v b hr
  constructor
  · apply owners_retain hi.owners (by
      unfold Origins.Retains; rw [material]; exact Origins.RetainsView.refl _)
    intro before after hb ha _
    obtain ⟨d, hd, _, _, _, next⟩ := geometry.device ha
    have eq : d = before := Option.some.inj (hd.symm.trans hb)
    subst d
    cases result with
    | error err => exact Nat.le_of_eq next.symm
    | ok pid =>
      have old : before.nextPeer = pid := by simpa [hb] using geometry.2.2
      rw [next, old]
      exact Nat.le_succ _
  · intro after id pkt ha hp other k ho hk
    have oldRx : (w.dev.bind fun d => d.rxSkbs[id]?) = some pkt := by
      simpa [rxView, ha, hp] using (congrFun (congrArg Prod.snd rx) id).symm
    obtain ⟨before, hb, oldPacket⟩ := Option.bind_eq_some_iff.mp oldRx
    have oldView : Origins.view w = some (other.ifindex, fun i => other.keypairs[i]?) :=
      material.symm.trans (by simp [Origins.view, ho])
    obtain ⟨d, hd, fields⟩ := Option.map_eq_some_iff.mp oldView
    have oldKey : d.keypairs[pkt.keypair]? = some k :=
      (congrFun (congrArg Prod.snd fields) pkt.keypair).trans hk
    exact hi.compatible before id pkt hb oldPacket d k hd oldKey
  · intro after ha id pkt hp
    obtain ⟨before, hb, _, keys, _, _⟩ := geometry.device ha
    have oldPacket : before.rxSkbs[id]? = some pkt := by
      simpa [rxView, ha, hb, hp] using (congrFun (congrArg Prod.snd rx) id).symm
    rw [keys]
    exact hi.rxKeys before hb id pkt oldPacket

theorem peerCreate_current (key : Key) (psk : Option Key)
    (history : List SessionOrigin.Receipt) :
    Preserves (fun w => CurrentLifecycle.Inv history w ∧ OwnerBounds.Carrier w)
      (peerCreate key psk) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  have configured := ((hoare_iff_run_ambient _ _ _).mp
    (ConfiguredIdentity.peerCreate_spec key psk) w a result v b hi.1.1 hr).1
  have current := (hoare_iff_run_ambient _ _ _).mp
    (CurrentIdentity.peerCreate_current key psk history) w a result v b ⟨hi.1.2, hi.2.owners⟩ hr
  exact ⟨⟨configured, current⟩,
    (hoare_iff_run_ambient _ _ _).mp (peerCreate_preserves key psk) w a result v b hi.2 hr⟩

private theorem front_device (pid : PeerId) (ctx : SessionOrigin.Context)
    (w v : WGWorld) (a b : Ambient)
    (hr : ((SessionOrigin.front pid).run w).run a = .ok ((some ctx, v), b)) :
    ∃ before after, w.dev = some before ∧ v.dev = some after ∧
      after.nextPeer = before.nextPeer ∧
      after.nextKeypairId = before.nextKeypairId + 1 ∧ after.rxSkbs = before.rxSkbs := by
  obtain ⟨read, init, derive, ar, ai, ad, entered, _, hi, hb, hd, _⟩ :=
    SessionOrigin.front_material _ _ _ _ _ _ hr
  obtain ⟨d, hw, _, _, _, _, hread⟩ := Origins.entered_peer _ _ _ _ _ _ entered
  obtain ⟨dev, old, hdev, _, hinit⟩ := Origins.initKey_effect _ _ _ _ _ _ _ hi
  have eq : dev = keyAllocationDevice d (w.keypairCounter + 1) ctx.word := by
    apply Option.some.inj
    simpa [hread, keyAllocationWorld] using hdev.symm
  subst dev
  have same : derive = init := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .sessionInitiator
      (ctx.state == HANDSHAKE_CONSUMED_RESPONSE)) (fun g => g = init))
    init ai ctx.initiator derive ad rfl hb
  obtain ⟨dev, prior, key, hdev, _, hv, _⟩ := Origins.derive_effect _ _ _ _ _ _ _ hd
  have eq : dev = {keyAllocationDevice d (w.keypairCounter + 1) ctx.word with
      keypairs := (keyAllocationDevice d (w.keypairCounter + 1) ctx.word).keypairs.insert ctx.slot
        {old with iAmTheInitiator := ctx.state == HANDSHAKE_CONSUMED_RESPONSE, remoteIndex := ctx.peer.remoteIndex}} :=
    Option.some.inj (hdev.symm.trans (by simpa [same] using hinit))
  subst dev
  exact ⟨d, _, hw, hv, rfl, rfl, rfl⟩

theorem front_preserves (pid : PeerId) :
    Preserves (fun w => ConfiguredIdentity.Inv w ∧ OwnerBounds.Carrier w)
      (SessionOrigin.front pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  have configuredView := (ProjectedAction.iff_run_ambient _ _ _).mp
    (ConfiguredSession.front_view pid) w a result v b hr
  have configured : ConfiguredIdentity.Inv v := by
    intro s hs
    exact hi.1 s (configuredView.symm.trans hs)
  refine ⟨configured, ?_⟩
  cases result with
  | none =>
    have same := Origins.front_none pid w v a b hr
    exact same ▸ hi.2
  | some ctx =>
    obtain ⟨d, key, hd, hp, _, word, slot, view, _, owner, _⟩ :=
      Origins.front_effect pid ctx w v a b hr
    obtain ⟨before, after, hb, ha, nextPeer, nextKey, rx⟩ := front_device pid ctx w v a b hr
    have eq : before = d := Option.some.inj (hb.symm.trans hd)
    subst before
    have keys : (fun q => after.keypairs[q]?) =
        (fun q => if ctx.slot = q then some key else d.keypairs[q]?) :=
      congrArg Prod.snd (Option.some.inj (by simpa only [Origins.view, ha, Option.map_some] using view))
    constructor
    · intro out ho id k hk valid pid hword
      have eq : out = after := Option.some.inj (ho.symm.trans ha)
      subst out
      rw [nextPeer]
      by_cases atSlot : ctx.slot = id
      · subst id
        have eq : k = key := by simpa [hk] using congrFun keys ctx.slot
        subst k
        exact configured_word_below hi.1 hd hp (word.symm.trans (owner.symm.trans hword))
      · exact hi.2.owners d hd id k (by simpa [atSlot, hk] using (congrFun keys id).symm)
          valid pid hword
    · intro out id pkt ho hpacket other k hkdev hk
      have eq : out = after := Option.some.inj (ho.symm.trans ha)
      have eq' : other = after := Option.some.inj (hkdev.symm.trans ha)
      subst out
      subst other
      have packet : d.rxSkbs[id]? = some pkt := by simpa [rx] using hpacket
      have below := hi.2.rxKeys d hd id pkt packet
      have different : ctx.slot ≠ pkt.keypair := by rw [slot]; exact Ne.symm (Nat.ne_of_lt below)
      have oldKey : d.keypairs[pkt.keypair]? = some k := by
        simpa [different, hk] using (congrFun keys pkt.keypair).symm
      exact hi.2.compatible d id pkt hd packet d k hd oldKey
    · intro out ho id pkt hpacket
      have eq : out = after := Option.some.inj (ho.symm.trans ha)
      subst out
      rw [nextKey]
      exact Nat.lt_trans (hi.2.rxKeys d hd id pkt (by simpa [rx] using hpacket))
        (Nat.lt_succ_self _)

theorem keypairPut_preserves (kp : Option KeypairId) (now : Bool) :
    Preserves OwnerBounds.Carrier (keypairPut kp now) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  have material := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Origins.Retaining.keypairPut_material kp now) w a result v b hr
  have geometry := keypairPut_retention kp now w v a b hr
  have rx := congrArg Prod.snd ((ProjectedAction.iff_run_ambient _ _ _).mp
    (keypairPut_credit_frame kp now) w a result v b hr)
  have effect := (KeyEffects.iff_run_ambient _ _).mp
    (keypairPut_keyEffect (allowed := NoPromotion) kp now) w a result v b hr
  constructor
  · apply owners_retain hi.owners material
    intro before after hb ha _
    obtain ⟨d, hd, fields⟩ := allocationMetadata_device geometry.metadata ha
    have eq : d = before := Option.some.inj (hd.symm.trans hb)
    subst d
    exact Nat.le_of_eq (congrArg DeviceAllocationMetadata.nextPeer fields).symm
  · exact effect.rxCompatible rx hi.compatible
  · intro after ha id pkt hp
    obtain ⟨before, hb, fields⟩ := allocationMetadata_device geometry.metadata ha
    have oldPacket : before.rxSkbs[id]? = some pkt := by
      simpa [rxView, ha, hb, hp] using (congrFun (congrArg Prod.snd rx) id).symm
    have frontier : after.nextKeypairId = before.nextKeypairId :=
      congrArg DeviceAllocationMetadata.nextKeypair fields
    rw [frontier]
    exact hi.rxKeys before hb id pkt oldPacket

private theorem carrier_map (f : Device → Device)
    (peer : ∀ d, (f d).nextPeer = d.nextPeer)
    (frontier : ∀ d, (f d).nextKeypairId = d.nextKeypairId)
    (keys : ∀ d, (f d).keypairs = d.keypairs)
    (rx : ∀ d, (f d).rxSkbs = d.rxSkbs)
    (hi : OwnerBounds.Carrier w) :
    OwnerBounds.Carrier {w with dev := w.dev.map f} := by
  constructor
  · intro d hd id k hk valid pid owner
    obtain ⟨before, hb, rfl⟩ := Option.map_eq_some_iff.mp hd
    rw [peer]
    exact hi.owners before hb id k (by simpa [keys] using hk) valid pid owner
  · intro d id pkt hd hp other k ho hk
    obtain ⟨before, hb, rfl⟩ := Option.map_eq_some_iff.mp hd
    obtain ⟨old, hold, rfl⟩ := Option.map_eq_some_iff.mp ho
    exact hi.compatible before id pkt hb (by simpa [rx] using hp)
      old k hold (by simpa [keys] using hk)
  · intro d hd id pkt hp
    obtain ⟨before, hb, rfl⟩ := Option.map_eq_some_iff.mp hd
    rw [frontier]
    exact hi.rxKeys before hb id pkt (by simpa [rx] using hp)

private theorem read_preserves (pid : PeerId) :
    Preserves OwnerBounds.Carrier (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi hr
  obtain ⟨rfl, _, _, _, _⟩ := Origins.getPeer_return _ _ _ _ _ _ hr
  exact hi

private theorem write_preserves (pid : PeerId) (p : Peer) :
    Preserves OwnerBounds.Carrier (setPeer pid p) := by
  unfold setPeer modifyDev
  apply hoare_modify
  intro w hi
  exact carrier_map _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hi

private theorem addNewKeypair_preserves (pid kp : Nat) :
    Preserves OwnerBounds.Carrier (addNewKeypair pid kp) := by
  have ambient {α : Type} (a : AmbientM α) :
      Preserves OwnerBounds.Carrier (monadLift a : WG.M α) :=
    hoare_liftAmbient a OwnerBounds.Carrier
  have readKey (id : KeypairId) : Preserves OwnerBounds.Carrier (getKeypair id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a k v b hi hr
    obtain ⟨rfl, _, _, _, _⟩ := KeyTimes.getKeypair_return _ _ _ _ _ _ hr
    exact hi
  unfold addNewKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head getPeer; exact read_preserves _)
    | (allocation_release_head setPeer; exact write_preserves _ _)
    | (allocation_release_head getKeypair; exact readKey _)
    | (allocation_release_head keypairPut; exact keypairPut_preserves _ _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | allocation_release_step

theorem tail_preserves (pid kp : Nat) :
    Preserves OwnerBounds.Carrier (SessionOrigin.tail pid kp) := by
  have ambient {α : Type} (a : AmbientM α) :
      Preserves OwnerBounds.Carrier (monadLift a : WG.M α) :=
    hoare_liftAmbient a OwnerBounds.Carrier
  have index {α : Type} (a : IndexM α) :
      Preserves OwnerBounds.Carrier (liftIndex a) := by
    apply hoare_liftIndex
    intro w d table hi hd
    have frame := carrier_map (w := w) (fun d => {d with indexTable := table})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hi
    simpa only [hd, Option.map_some] using frame
  unfold SessionOrigin.tail SessionOrigin.tailWith handshakeZero
  simp (config := {zeta := false}) only [branch, unsupported]
  repeat' first
    | (allocation_release_head getPeer; exact read_preserves _)
    | (allocation_release_head setPeer; exact write_preserves _ _)
    | (allocation_release_head addNewKeypair; exact addNewKeypair_preserves _ _)
    | (allocation_release_head IndexOwner.peerDeref
       exact indexOwner_peerDeref_preserves _ OwnerBounds.Carrier)
    | (allocation_release_head liftIndex; exact index _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | allocation_release_step

theorem beginSession_preserves (pid : PeerId) :
    Preserves (fun w => ConfiguredIdentity.Inv w ∧ OwnerBounds.Carrier w) (beginSession pid) := by
  rw [SessionOrigin.factor]
  apply preserves_bind (front_preserves pid)
  intro front
  cases front with
  | none => exact preserves_pure _
  | some ctx =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi hr
    have view := (ProjectedAction.iff_run_ambient _ _ _).mp
      (ConfiguredSession.tail_view pid ctx.slot) w a result v b hr
    exact ⟨fun s hs => hi.1 s (view.symm.trans hs),
      (hoare_iff_run_ambient _ _ _).mp (tail_preserves pid ctx.slot) w a result v b hi.2 hr⟩

/-- The new receiving material is certified by the actual front of this same
normal session, while the carrier remains available at its final endpoint. -/
theorem beginSession_current (pid : PeerId) (w v : WGWorld) (result : Bool)
    (a b : Ambient) (history : List SessionOrigin.Receipt)
    (hi : CurrentLifecycle.Inv history w ∧ OwnerBounds.Carrier w)
    (hr : ((beginSession pid).run w).run a = .ok ((result, v), b)) :
    ∃ front u middle, ((SessionOrigin.front pid).run w).run a = .ok ((front, u), middle) ∧
      CurrentLifecycle.Inv
        (history ++ [SessionOrigin.Receipt.material pid ⟨front, w, u, a, middle⟩]) v ∧
      OwnerBounds.Carrier v := by
  obtain ⟨front, u, middle, hf, current⟩ :=
    CurrentSession.beginSession_support pid w v result a b history hi.1.1 hi.1.2 hr
  have kept := (hoare_iff_run_ambient _ _ _).mp
    (beginSession_preserves pid) w a result v b ⟨hi.1.1, hi.2⟩ hr
  exact ⟨front, u, middle, hf, ⟨kept.1, current⟩, kept.2⟩

end Leanux.Proofs.WG.OwnerCreation
