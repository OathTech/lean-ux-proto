import Leanux.Proofs.WG.RetirementSecurity.HolderConfigurationAcquisition
import Leanux.Proofs.WG.Queues.SetPeerBoundary

/-! The whole original peer command retains exact key credit, including new
peer allocation, acquisition, ordinary edits, removal and early errno cleanup.
The source cuts derive their own acquired state before consuming it. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderConfiguration
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open Configuration

private theorem out_none (attrs : PeerAttrs) (ret : Int) :
    Hoare (do peerPut none; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
      (Entry temporary cs loans) (fun _=>HolderAccount temporary) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  change Except.ok ((ret,w),CounterWindow.record (CounterWindow.record a .peerPutNull true)
    .peerZeroPsk attrs.presharedKey.isSome)=.ok ((result,v),b) at run
  cases run
  exact before.1.1

private theorem create_update (attrs : PeerAttrs) (key : Key) (psk : Option Key) (flags : UInt32) :
    Hoare (do
      match ← peerCreate key psk with
      | .error e =>
        _ ← branch .peerCreateErr true
        peerPut none
        _ ← branch .peerZeroPsk attrs.presharedKey.isSome
        pure e
      | .ok pid =>
        _ ← branch .peerCreateErr false
        peerGet pid
        peerConfigUpdateSource attrs (some pid) flags psk pid)
      (Entry temporary cs loans) (fun _=>HolderAccount temporary) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨created,u,c,creation,tail⟩ := run
  cases created with
  | error e =>
    have keys := HolderPeerCreation.keys key psk before.1.1 before.2.2.2 a c creation
    change Except.ok ((e,u),CounterWindow.record
      (CounterWindow.record (CounterWindow.record c .peerCreateErr true) .peerPutNull true)
      .peerZeroPsk attrs.presharedKey.isSome)=.ok ((result,v),b) at tail
    cases tail
    exact keys
  | ok pid =>
    change ((peerGet pid >>= fun _=>peerConfigUpdateSource attrs (some pid) flags psk pid).run u).run
      (CounterWindow.record c .peerCreateErr false)=.ok ((result,v),b) at tail
    rw [MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨ignored,z,d,acquire,finish⟩ := tail
    cases ignored
    exact (hoare_iff_run_ambient _ _ _).mp (update_acquired attrs flags psk pid) z d result v b
      (creation_acquired key psk before a c d creation acquire) finish

private theorem read (P : WGWorld → Prop) : Preserves P getDev := by
  unfold getDev
  apply preserves_bind (hoare_consequence (hoare_get P)
    (fun _ h => h) (fun _ _ h => h.2))
  intro w
  cases w.dev
  · exact hoare_liftAmbient (AmbientM.invariant _) P
  · exact preserves_pure _

private theorem and_records (P : WGWorld → Prop) (first second : Decision) (a b : Bool) :
    Preserves P (WG.andM (branch first a) (branch second b)) := by
  unfold WG.andM
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch first a) P)
  intro yes
  cases yes with
  | false => exact preserves_pure false
  | true => exact hoare_liftAmbient (AmbientM.branch second b) P

private theorem acquired (attrs : PeerAttrs) (key : Key) (psk : Option Key)
    (flags : UInt32) (peer : Option PeerId) :
    Hoare (peerCommandAcquiredWith (fun {_} action => action) peerCreate peerGet
      (fun ret => do peerPut none; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
      (peerConfigUpdateSource attrs) key psk flags peer)
      (Acquired temporary cs loans peer) (fun _ => HolderAccount temporary) := by
  cases peer with
  | some pid =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi run
    change ((peerConfigUpdateSource attrs (some pid) flags psk pid).run w).run
      (CounterWindow.record a .peerNotFound false)=.ok ((result,v),b) at run
    exact (hoare_iff_run_ambient _ _ _).mp (update_acquired attrs flags psk pid) w _ result v b hi run
  | none =>
    let tail : WG.M Int := do
      if ← branch .peerNewRemoveOrUpdate (flags &&& (WGPEER_F_REMOVE_ME ||| WGPEER_F_UPDATE_ONLY) != 0) then
        peerPut none
        _ ← branch .peerZeroPsk attrs.presharedKey.isSome
        return 0
      let flags := flags &&& ~~~WGPEER_F_REPLACE_ALLOWEDIPS
      let identity := (← getDev).staticIdentity
      if ← WG.andM (branch .peerSelfHasIdentity identity.hasIdentity)
          (branch .peerSelfKeyMatch (key == identity.staticPublic)) then
        peerPut none
        _ ← branch .peerZeroPsk attrs.presharedKey.isSome
        return 0
      match ← peerCreate key psk with
      | .error e =>
        _ ← branch .peerCreateErr true
        peerPut none
        _ ← branch .peerZeroPsk attrs.presharedKey.isSome
        pure e
      | .ok pid =>
        _ ← branch .peerCreateErr false
        peerGet pid
        peerConfigUpdateSource attrs (some pid) flags psk pid
    have keeps : Hoare tail (Entry temporary cs loans) (fun _ => HolderAccount temporary) := by
      unfold tail
      apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .peerNewRemoveOrUpdate
        (flags &&& (WGPEER_F_REMOVE_ME ||| WGPEER_F_UPDATE_ONLY) != 0)) (Entry temporary cs loans))
      intro removeOrUpdate
      cases removeOrUpdate with
      | true => exact out_none attrs 0
      | false =>
        apply hoare_bind _ _ (read (Entry temporary cs loans))
        intro d
        apply hoare_bind _ _ (and_records (Entry temporary cs loans) .peerSelfHasIdentity .peerSelfKeyMatch
          d.staticIdentity.hasIdentity (key == d.staticIdentity.staticPublic))
        intro selfKey
        cases selfKey with
        | true => exact out_none attrs 0
        | false => exact create_update attrs key psk (flags &&& ~~~WGPEER_F_REPLACE_ALLOWEDIPS)
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi run
    change (tail.run w).run (CounterWindow.record a .peerNotFound true)=.ok ((result,v),b) at run
    exact (hoare_iff_run_ambient _ _ _).mp keeps w _ result v b hi run

private theorem commandPrefix (attrs : PeerAttrs) (out : Int → WG.M Int)
    (acquiredSource : Key → Option Key → UInt32 → Option PeerId → WG.M Int)
    (hout : ∀ ret, Hoare (out ret) (Entry temporary cs loans) (fun _ => HolderAccount temporary))
    (hacquired : ∀ key psk flags peer, Hoare (acquiredSource key psk flags peer)
      (Acquired temporary cs loans peer) (fun _ => HolderAccount temporary)) :
    Hoare (setPeerCmdWith (fun {_} action => action) pubkeyLookup out acquiredSource attrs)
      (Entry temporary cs loans) (fun _ => HolderAccount temporary) := by
  have finalLookup (key : Key) (psk : Option Key) (flags : UInt32) :
      Hoare (pubkeyLookup key >>= acquiredSource key psk flags)
        (Entry temporary cs loans) (fun _ => HolderAccount temporary) :=
    hoare_bind _ _ (lookup key) (hacquired key psk flags)
  have checkedFlags (key : Key) (psk : Option Key) (flags : UInt32) :
      Hoare (do
        if ← branch .peerBadFlags (flags &&& ~~~WGPEER_F_ALL != 0) then return ← out (-EOPNOTSUPP)
        if ← branch .peerHasProtocol attrs.protocolVersion.isSome then
          if ← branch .peerBadProtocol (attrs.protocolVersion != some 1) then return ← out (-EPFNOSUPPORT)
        pubkeyLookup key >>= acquiredSource key psk flags)
        (Entry temporary cs loans) (fun _ => HolderAccount temporary) := by
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .peerBadFlags
      (flags &&& ~~~WGPEER_F_ALL != 0)) (Entry temporary cs loans))
    intro bad
    cases bad with
    | true => exact hout (-EOPNOTSUPP)
    | false =>
      apply hoare_bind _ _ (hoare_liftAmbient
        (AmbientM.branch .peerHasProtocol attrs.protocolVersion.isSome) (Entry temporary cs loans))
      intro has
      cases has with
      | false => exact finalLookup key psk flags
      | true =>
        apply hoare_bind _ _ (hoare_liftAmbient
          (AmbientM.branch .peerBadProtocol (attrs.protocolVersion != some 1)) (Entry temporary cs loans))
        intro bad
        cases bad with
        | true => exact hout (-EPFNOSUPPORT)
        | false => exact finalLookup key psk flags
  unfold setPeerCmdWith
  apply hoare_bind _ _ (and_records (Entry temporary cs loans) .peerHasPubkey .peerPubkeyLen attrs.publicKey.isSome true)
  intro valid
  cases valid with
  | false => exact hout (-EINVAL)
  | true =>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false]
    cases attrs.publicKey with
    | none =>
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w a result v b _ run
      cases run
    | some publicKey =>
      apply hoare_bind _ _ (and_records (Entry temporary cs loans) .peerHasPsk .peerPskLen attrs.presharedKey.isSome true)
      intro hasPsk
      cases hasPsk with
      | false =>
        simp only [Bool.false_eq_true,↓reduceIte,pure_bind]
        apply hoare_bind _ _ (hoare_liftAmbient
          (AmbientM.branch .peerHasFlags attrs.flags.isSome) (Entry temporary cs loans))
        intro hasFlags
        cases hasFlags with
        | false => exact checkedFlags publicKey none 0
        | true => exact checkedFlags publicKey none (attrs.flags.getD 0)
      | true =>
        simp only [↓reduceIte,pure_bind]
        apply hoare_bind _ _ (hoare_liftAmbient
          (AmbientM.branch .peerHasFlags attrs.flags.isSome) (Entry temporary cs loans))
        intro hasFlags
        cases hasFlags with
        | false => exact checkedFlags publicKey attrs.presharedKey 0
        | true => exact checkedFlags publicKey attrs.presharedKey (attrs.flags.getD 0)

/-- Every normal native peer command retains exact physical key credit. Its
entry allocation, current-slot compatibility and independent peer ledgers are
explicit; complete initialized driver transport is a separate result. -/
theorem command (attrs : PeerAttrs) : Hoare (WG.setPeerCmd attrs)
    (Entry temporary cs loans) (fun _=>HolderAccount temporary) := by
  rw [←setPeerCmd_source,setPeerCmdSource_factor]
  exact commandPrefix attrs _ _ (out_none attrs) (acquired attrs)

end Leanux.Proofs.WG.RetirementSecurity.HolderConfiguration
