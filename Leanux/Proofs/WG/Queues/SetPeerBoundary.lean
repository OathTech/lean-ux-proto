import Leanux.Proofs.WG.Queues.CreationLoan
import Leanux.Proofs.WG.Queues.HolderConfigUpdate
import Leanux.Proofs.WG.Queues.JointPeerCommand

/-! Complete actual peer commands consume their lookup/creation loan on the
original out path. Structural coherence is retained on every normal errno or
success return, using supplied configured identity only before acquisition. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.SetPeerBoundary
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders Configuration

private def Entry (cs : Ledger) (loans : Reservations) (w : WGWorld) : Prop :=
  Boundary cs loans w ∧ BaseCoherence.Inv w ∧ ConfiguredIdentity.Inv w

private def Post (cs : Ledger) (loans : Reservations) (w : WGWorld) : Prop :=
  Boundary cs loans w ∧ BaseCoherence.Inv w

private def Acquired (cs : Ledger) (loans : Reservations)
    (peer : Option PeerId) (w : WGWorld) : Prop :=
  match peer with
  | none => Entry cs loans w
  | some pid => ∃ o : Owner, o.slot=pid ∧ Boundary cs (o::loans) w ∧
      BaseCoherence.Inv w ∧ ConfiguredIdentity.Inv w ∧ pid ∈ BaseCoherence.slots w

private theorem lookup (key : Key) :
    Hoare (pubkeyLookup key) (Entry cs loans) (Acquired cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  obtain ⟨⟨holders,funded,stable⟩,coherent,configured⟩ := hi
  have identity := (ProjectedAction.iff_run_ambient _ _ _).mp
    (ConfiguredReceive.pubkeyLookup_view key) w a result v b run
  have configuredOut : ConfiguredIdentity.Inv v := fun s hs => configured s (identity ▸ hs)
  cases result with
  | none =>
    obtain ⟨⟨fundedOut,stableOut⟩,coherentOut⟩ :=
      BaseLookupRemoval.lookup_funded key funded stable coherent a b run
    exact ⟨⟨holders,fundedOut,stableOut⟩,coherentOut,configuredOut⟩
  | some pid =>
    obtain ⟨o,slot,fundedOut,stableOut,coherentOut,_,member⟩ :=
      BaseLookupRemoval.lookup_selected key funded stable coherent configured a b run
    refine ⟨o,slot,⟨holders,fundedOut,stableOut⟩,coherentOut,configuredOut,?_⟩
    unfold BaseCoherence.slots
    rw [←fundedOut.aligned.base]
    exact member

private theorem out_none (attrs : PeerAttrs) (ret : Int) :
    Hoare (do peerPut none; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
      (Entry cs loans) (fun _ => Post cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  change Except.ok ((ret,w),CounterWindow.record (CounterWindow.record a .peerPutNull true)
    .peerZeroPsk attrs.presharedKey.isSome)=.ok ((result,v),b) at run
  cases run
  exact ⟨hi.1,hi.2.1⟩

private theorem update (attrs : PeerAttrs) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    Hoare (peerConfigUpdateSource attrs (some pid) flags psk pid)
      (Acquired cs loans (some pid)) (fun _ => Post cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  obtain ⟨o,slot,funded,coherent,_,member⟩ := hi
  subst pid
  exact ⟨HolderConfigUpdate.update_paid attrs o flags psk funded coherent member a b run,
    (hoare_iff_run_ambient _ _ _).mp
      (BaseCoherence.update_preserves attrs (some o.slot) flags psk o.slot) w a result v b coherent run⟩

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
      (Entry cs loans) (fun _ => Post cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨created,u,c,creation,tail⟩ := run
  obtain ⟨⟨holders,funded,stable⟩,coherent,configured⟩ := hi
  cases created with
  | error e =>
    obtain ⟨coherentOut,configuredOut,fundedOut,stableOut⟩ :=
      CreationLoan.creation key psk funded stable coherent configured a c creation
    change ((do peerPut none; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure e : WG.M Int).run u).run
      (CounterWindow.record c .peerCreateErr true)=.ok ((result,v),b) at tail
    exact (hoare_iff_run_ambient _ _ _).mp (out_none attrs e)
      u _ result v b ⟨⟨holders,fundedOut,stableOut⟩,coherentOut,configuredOut⟩ tail
  | ok pid =>
    change ((peerGet pid >>= fun _ => peerConfigUpdateSource attrs (some pid) flags psk pid).run u).run
      (CounterWindow.record c .peerCreateErr false)=.ok ((result,v),b) at tail
    rw [MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨ignored,z,d,acquire,finish⟩ := tail
    cases ignored
    obtain ⟨device,_,slot,fundedOut,stableOut,coherentOut,configuredOut,member⟩ :=
      CreationLoan.creation_acquire key psk funded stable coherent configured a c d creation acquire
    exact (hoare_iff_run_ambient _ _ _).mp (update attrs flags psk pid) z d result v b
      ⟨BaseCreation.owner w device,slot.symm,
        ⟨HolderCreation.addBase holders (BaseCreation.owner w device),fundedOut,stableOut⟩,
        coherentOut,configuredOut,member⟩ finish

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
      (Acquired cs loans peer) (fun _ => Post cs loans) := by
  cases peer with
  | some pid =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi run
    change ((peerConfigUpdateSource attrs (some pid) flags psk pid).run w).run
      (CounterWindow.record a .peerNotFound false)=.ok ((result,v),b) at run
    exact (hoare_iff_run_ambient _ _ _).mp (update attrs flags psk pid) w _ result v b hi run
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
    have keeps : Hoare tail (Entry cs loans) (fun _ => Post cs loans) := by
      unfold tail
      apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .peerNewRemoveOrUpdate
        (flags &&& (WGPEER_F_REMOVE_ME ||| WGPEER_F_UPDATE_ONLY) != 0)) (Entry cs loans))
      intro removeOrUpdate
      cases removeOrUpdate with
      | true => exact out_none attrs 0
      | false =>
        apply hoare_bind _ _ (read (Entry cs loans))
        intro d
        apply hoare_bind _ _ (and_records (Entry cs loans) .peerSelfHasIdentity .peerSelfKeyMatch
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
    (hout : ∀ ret, Hoare (out ret) (Entry cs loans) (fun _ => Post cs loans))
    (hacquired : ∀ key psk flags peer, Hoare (acquiredSource key psk flags peer)
      (Acquired cs loans peer) (fun _ => Post cs loans)) :
    Hoare (setPeerCmdWith (fun {_} action => action) pubkeyLookup out acquiredSource attrs)
      (Entry cs loans) (fun _ => Post cs loans) := by
  have finalLookup (key : Key) (psk : Option Key) (flags : UInt32) :
      Hoare (pubkeyLookup key >>= acquiredSource key psk flags)
        (Entry cs loans) (fun _ => Post cs loans) :=
    hoare_bind _ _ (lookup key) (hacquired key psk flags)
  have checkedFlags (key : Key) (psk : Option Key) (flags : UInt32) :
      Hoare (do
        if ← branch .peerBadFlags (flags &&& ~~~WGPEER_F_ALL != 0) then return ← out (-EOPNOTSUPP)
        if ← branch .peerHasProtocol attrs.protocolVersion.isSome then
          if ← branch .peerBadProtocol (attrs.protocolVersion != some 1) then return ← out (-EPFNOSUPPORT)
        pubkeyLookup key >>= acquiredSource key psk flags)
        (Entry cs loans) (fun _ => Post cs loans) := by
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .peerBadFlags
      (flags &&& ~~~WGPEER_F_ALL != 0)) (Entry cs loans))
    intro bad
    cases bad with
    | true => exact hout (-EOPNOTSUPP)
    | false =>
      apply hoare_bind _ _ (hoare_liftAmbient
        (AmbientM.branch .peerHasProtocol attrs.protocolVersion.isSome) (Entry cs loans))
      intro has
      cases has with
      | false => exact finalLookup key psk flags
      | true =>
        apply hoare_bind _ _ (hoare_liftAmbient
          (AmbientM.branch .peerBadProtocol (attrs.protocolVersion != some 1)) (Entry cs loans))
        intro bad
        cases bad with
        | true => exact hout (-EPFNOSUPPORT)
        | false => exact finalLookup key psk flags
  unfold setPeerCmdWith
  apply hoare_bind _ _ (and_records (Entry cs loans) .peerHasPubkey .peerPubkeyLen attrs.publicKey.isSome true)
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
      apply hoare_bind _ _ (and_records (Entry cs loans) .peerHasPsk .peerPskLen attrs.presharedKey.isSome true)
      intro hasPsk
      cases hasPsk with
      | false =>
        simp only [Bool.false_eq_true,↓reduceIte,pure_bind]
        apply hoare_bind _ _ (hoare_liftAmbient
          (AmbientM.branch .peerHasFlags attrs.flags.isSome) (Entry cs loans))
        intro hasFlags
        cases hasFlags with
        | false => exact checkedFlags publicKey none 0
        | true => exact checkedFlags publicKey none (attrs.flags.getD 0)
      | true =>
        simp only [↓reduceIte,pure_bind]
        apply hoare_bind _ _ (hoare_liftAmbient
          (AmbientM.branch .peerHasFlags attrs.flags.isSome) (Entry cs loans))
        intro hasFlags
        cases hasFlags with
        | false => exact checkedFlags publicKey attrs.presharedKey 0
        | true => exact checkedFlags publicKey attrs.presharedKey (attrs.flags.getD 0)

/-- Complete original command, including early errno cleanup, old-peer lookup,
new allocation, the extra caller loan, and both original update arms. -/
theorem setPeerCmd (attrs : PeerAttrs) :
    Hoare (WG.setPeerCmd attrs)
      (fun w => Boundary cs loans w ∧ BaseCoherence.Inv w ∧ ConfiguredIdentity.Inv w)
      (fun _ w => Boundary cs loans w ∧ BaseCoherence.Inv w) := by
  change Hoare (WG.setPeerCmd attrs) (Entry cs loans) (fun _ => Post cs loans)
  rw [← setPeerCmd_source,setPeerCmdSource_factor]
  exact commandPrefix attrs _ _ (out_none attrs) (acquired attrs)

/-- Native normal endpoints use the supplied entry account; no successful
execution or initialized funding premise is substituted for the source run. -/
theorem setPeerCmd_normal (attrs : PeerAttrs) (funded : Boundary cs loans w)
    (coherent : BaseCoherence.Inv w) (configured : ConfiguredIdentity.Inv w)
    (a b : Ambient)
    (run : ((WG.setPeerCmd attrs).run w).run a=.ok ((result,v),b)) :
    Boundary cs loans v ∧ BaseCoherence.Inv v :=
  (hoare_iff_run_ambient _ _ _).mp (setPeerCmd attrs) w a result v b
    ⟨funded,coherent,configured⟩ run

end Leanux.Proofs.WG.Queues.RxCredits.SetPeerBoundary
