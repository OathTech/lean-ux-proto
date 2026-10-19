import Leanux.Proofs.WG.Config.CreationScalarSource
import Leanux.Proofs.WG.Config.ScalarCommandSource
import Leanux.Proofs.WG.Index.ConfigurationCreationSource

/-! Actual missing-target creation, acquisition and update composition. The landed account cut supplies the selected base and loan; normal mixed-attribute results retain exact scalar writes. Original Stops expose no final state. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.CreationScalar
open Leanux Leanux.WG Noise Lifetimes Leanux.Proofs.Framing Std.Do Queues Queues.RxCredits
open PeerScalarRetention Leanux.Proofs.WG.Configuration

def CreatedResult (attrs : PeerAttrs) (key : Key) (start : WGWorld)
    (ret : Int) (g : WGWorld) : Prop :=
  (g=start ∧ (ret=0 ∨ ret=-ENOMEM)) ∨
  ∃pid,start.dev.map Device.nextPeer=some pid ∧ view g pid=some (ScalarTail.tailCell attrs ret
    (ScalarTail.prefixCell (initializedPeer key (start.peerCounter+1) attrs.presharedKey)
      attrs.presharedKey attrs.endpoint))

theorem create_update (cs : Ledger) (loans : Reservations)
    (attrs : PeerAttrs) (key : Key) (flags : UInt32)
    (keep : flags &&& WGPEER_F_REMOVE_ME=0)
    (start : WGWorld) (before : Device) (device : start.dev=some before)
    (entry : Index.ConfigurationIndex.Entry cs loans start) :
    Hoare (do
      match ←peerCreate key attrs.presharedKey with
      | .error code=>
        _ ←branch .peerCreateErr true
        peerPut none
        _ ←branch .peerZeroPsk attrs.presharedKey.isSome
        pure code
      | .ok pid=>
        _ ←branch .peerCreateErr false
        peerGet pid
        peerConfigUpdateSource attrs (some pid) flags attrs.presharedKey pid)
      (fun g=>g=start)
      (fun ret g=>Index.ConfigurationIndex.Entry cs loans g ∧ CreatedResult attrs key start ret g) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result final b pre run
  subst g
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨created,u,c,creation,tail⟩:=run
  have scalar:=create_selected key attrs.presharedKey start before device
    start a created u c rfl creation
  cases created with
  | error code=>
    obtain ⟨codeEq,same⟩:=scalar
    subst code
    rw [same] at tail
    change Except.ok ((-ENOMEM,start),CounterWindow.record
      (CounterWindow.record (CounterWindow.record c .peerCreateErr true) .peerPutNull true)
        .peerZeroPsk attrs.presharedKey.isSome)=.ok ((result,final),b) at tail
    cases tail
    exact ⟨entry,Or.inl ⟨rfl,Or.inr rfl⟩⟩
  | ok pid=>
    change ((peerGet pid >>= fun _=>peerConfigUpdateSource attrs (some pid) flags attrs.presharedKey pid).run u).run
      (CounterWindow.record c .peerCreateErr false)=.ok ((result,final),b) at tail
    rw [MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨ignored,z,e,acquire,update⟩:=tail
    cases ignored
    have current:=(hoare_iff_run_ambient _ _ _).mp
      (peerGet_selected pid (initCell attrs.presharedKey (newbornCell (start.peerCounter+1))))
        u _ () z e scalar acquire
    obtain ⟨paid,slot,account,member⟩:=Index.ConfigurationIndex.creation_acquire_entry
      cs loans key attrs.presharedKey start u z a c e pid entry creation acquire
    subst pid
    obtain ⟨d,p,present,stored,same⟩:=resident z paid.slot _ current
    have listed : paid.slot∈d.peerList:=by
      simpa only [BaseCoherence.slots,present,Option.map_some,Option.getD_some] using member
    have done:=ScalarTail.update_exact cs loans paid attrs flags attrs.presharedKey keep d p
      stored listed z e result final b ⟨account,present⟩ update
    have initialized : cell p=cell (initializedPeer key (start.peerCounter+1) attrs.presharedKey):=
      same.trans (initialized_cell key _ _).symm
    have prefixSame:=prefixCell_congr p (initializedPeer key (start.peerCounter+1) attrs.presharedKey)
      attrs.presharedKey attrs.endpoint initialized
    exact ⟨done.1,Or.inr ⟨paid.slot,
      (peerCreate_geometry key attrs.presharedKey start u (.ok paid.slot) a c creation).2.2,
      by simpa only [prefixSame] using done.2⟩⟩

theorem acquired_none_rule (attrs : PeerAttrs) (key : Key) (flags : UInt32)
    (P : WGWorld → Prop) (Q : Int → WGWorld → Prop)
    (read : Preserves P getDev)
    (quiet : Hoare (do
      peerPut none
      _ ←branch .peerZeroPsk attrs.presharedKey.isSome
      pure (0 : Int) : WG.M Int) P Q)
    (create : Hoare (do
      match ←peerCreate key attrs.presharedKey with
      | .error code=>
        _ ←branch .peerCreateErr true
        peerPut none
        _ ←branch .peerZeroPsk attrs.presharedKey.isSome
        pure code
      | .ok pid=>
        _ ←branch .peerCreateErr false
        peerGet pid
        peerConfigUpdateSource attrs (some pid)
          (flags &&& ~~~WGPEER_F_REPLACE_ALLOWEDIPS) attrs.presharedKey pid) P Q) :
    Hoare (peerCommandAcquiredWith (fun {_} action=>action) peerCreate peerGet
      (fun ret=>do peerPut none; _ ←branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
      (peerConfigUpdateSource attrs) key attrs.presharedKey flags none) P Q := by
  have comparison (identity : StaticIdentity) :
      Preserves P (WG.andM (branch .peerSelfHasIdentity identity.hasIdentity)
        (branch .peerSelfKeyMatch (key == identity.staticPublic))) := by
    unfold WG.andM
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .peerSelfHasIdentity identity.hasIdentity) P)
    intro has
    cases has with
    | false=>exact preserves_pure false
    | true=>exact hoare_liftAmbient (AmbientM.branch .peerSelfKeyMatch (key==identity.staticPublic)) P
  unfold peerCommandAcquiredWith
  dsimp only
  apply hoare_bind _ _ (branch_state_spec P .peerNotFound true)
  intro notFound
  cases notFound with
  | false=>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro g a result final b pre run
    contradiction
  | true=>
    apply hoare_consequence (P:=P) (Q:=Q) ?_ (fun _ pre=>pre.2) (fun _ _ post=>post)
    apply hoare_bind _ _ (hoare_liftAmbient
      (AmbientM.branch .peerNewRemoveOrUpdate (flags &&& (WGPEER_F_REMOVE_ME ||| WGPEER_F_UPDATE_ONLY)!=0)) P)
    intro blocked
    cases blocked with
    | true=>exact quiet
    | false=>
      apply hoare_bind _ _ read
      intro d
      apply hoare_bind _ _ (comparison d.staticIdentity)
      intro self
      cases self with
      | true=>exact quiet
      | false=>exact create

theorem acquired_none (cs : Ledger) (loans : Reservations)
    (attrs : PeerAttrs) (key : Key) (flags : UInt32)
    (keep : flags &&& WGPEER_F_REMOVE_ME=0)
    (start : WGWorld) (before : Device) (device : start.dev=some before)
    (entry : Index.ConfigurationIndex.Entry cs loans start) :
    Hoare (peerCommandAcquiredWith (fun {_} action=>action) peerCreate peerGet
      (fun ret=>do peerPut none; _ ←branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
      (peerConfigUpdateSource attrs) key attrs.presharedKey flags none)
      (fun g=>g=start)
      (fun ret g=>Index.ConfigurationIndex.Entry cs loans g ∧ CreatedResult attrs key start ret g) := by
  have read : Preserves (fun g=>g=start) getDev := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro g a result final b pre run
    subst g
    simp [getDev,device] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩:=run
    rfl
  have quiet : Hoare (do
      peerPut none
      _ ←branch .peerZeroPsk attrs.presharedKey.isSome
      pure (0 : Int) : WG.M Int)
      (fun g=>g=start)
      (fun ret g=>Index.ConfigurationIndex.Entry cs loans g ∧ CreatedResult attrs key start ret g) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro g a result final b pre run
    subst g
    change Except.ok ((0,start),_) = .ok ((result,final),b) at run
    cases run
    exact ⟨entry,Or.inl ⟨rfl,Or.inl rfl⟩⟩
  exact acquired_none_rule attrs key flags _ _ read quiet
    (create_update cs loans attrs key _ (by rw [masked_remove];exact keep)
      start before device entry)

theorem missing_command (cs : Ledger) (loans : Reservations)
    (attrs : PeerAttrs) (key : Key) (before : Device)
    (pubkey : attrs.publicKey=some key)
    (valid : attrs.flags.getD 0 &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (keep : attrs.flags.getD 0 &&& WGPEER_F_REMOVE_ME=0)
    (missing : before.peerHashtable.find? (·.1 == key)=none)
    (start : WGWorld) (device : start.dev=some before)
    (entry : Index.ConfigurationIndex.Entry cs loans start) :
    Noise.Ensures (setPeerCmd attrs) (fun g=>g=start)
      (fun ret g=>Index.ConfigurationIndex.Entry cs loans g ∧ CreatedResult attrs key start ret g) := by
  intro g a result final b pre run
  subst g
  obtain ⟨first,cut⟩:=QueuedRemove.command_lookup_default_cut attrs key pubkey valid protocol
    start final a b result run
  rw [MaterialOrigin.bind_ok_ambient] at cut
  obtain ⟨peer,u,c,lookup,tail⟩:=cut
  have selection:=(Noise.ensures_iff _ _ _).mpr
    (pubkeyLookup_absent key start before device missing) start first peer u c rfl lookup
  obtain ⟨rfl,same⟩:=selection
  rw [same] at tail
  exact (hoare_iff_run_ambient _ _ _).mp
    (acquired_none cs loans attrs key (attrs.flags.getD 0) keep start before device entry)
      start c result final b rfl tail

end Leanux.Proofs.WG.Config.CreationScalar
