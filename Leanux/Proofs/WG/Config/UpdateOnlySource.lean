import Leanux.Proofs.WG.Config.UpdateOnlyModel
import Leanux.Proofs.WG.Config.PeerScalars
import Leanux.Proofs.WG.Queues.JointPeerCommand

/-! Actual peer-command source equalities and total refusal branches.
The existing-target equality retains every original Stop and Ambient effect. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.UpdateOnly
open Leanux Leanux.WG Noise
open Leanux.Proofs.WG.Configuration

theorem update_flags (attrs : PeerAttrs) (flags : UInt32) (peer : Option PeerId)
    (psk : Option Key) (pid : PeerId) :
    Configuration.peerConfigUpdateSource {attrs with flags:=some (flags ||| WGPEER_F_UPDATE_ONLY)}
      peer (flags ||| WGPEER_F_UPDATE_ONLY) psk pid =
    Configuration.peerConfigUpdateSource {attrs with flags:=some flags} peer flags psk pid := by
  simp only [Configuration.peerConfigUpdateSource,(masks flags).2.1,(masks flags).2.2]
  rfl

theorem acquired_some (attrs : PeerAttrs) (key : Key) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) :
    peerCommandAcquiredWith (fun {_} action=>action) peerCreate peerGet
      (fun ret=>do peerPut none; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
      (Configuration.peerConfigUpdateSource {attrs with flags:=some (flags ||| WGPEER_F_UPDATE_ONLY)})
      key psk (flags ||| WGPEER_F_UPDATE_ONLY) (some pid) =
    peerCommandAcquiredWith (fun {_} action=>action) peerCreate peerGet
      (fun ret=>do peerPut none; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
      (Configuration.peerConfigUpdateSource {attrs with flags:=some flags})
      key psk flags (some pid) := by
  unfold peerCommandAcquiredWith
  simp only [Option.isNone_some]
  change (do _ ← branch .peerNotFound false
             Configuration.peerConfigUpdateSource {attrs with flags:=some (flags ||| WGPEER_F_UPDATE_ONLY)}
               (some pid) (flags ||| WGPEER_F_UPDATE_ONLY) psk pid) =
         (do _ ← branch .peerNotFound false
             Configuration.peerConfigUpdateSource {attrs with flags:=some flags} (some pid) flags psk pid)
  rw [update_flags]

theorem bind_run_congr {α β : Type} (action : WG.M α) (left right : α → WG.M β)
    (g : WGWorld) (a : Ambient)
    (same : ∀ value v b, (action.run g).run a=.ok ((value,v),b) →
      ((left value).run v).run b=((right value).run v).run b) :
    ((action >>= left).run g).run a=((action >>= right).run g).run a := by
  change (((action.run g).run a) >>= fun out=>((left out.1.1).run out.1.2).run out.2) =
    (((action.run g).run a) >>= fun out=>((right out.1.1).run out.1.2).run out.2)
  cases run : (action.run g).run a with
  | error stop => rfl
  | ok out =>
    rcases out with ⟨⟨value,v⟩,b⟩
    exact same value v b run

theorem lookup_follow (attrs : PeerAttrs) (key : Key) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) (d : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key)=some (key,pid))
    (resident : d.peers[pid]?=some p) (positive : 0<p.refcount)
    (g : WGWorld) (a : Ambient) (device : g.dev=some d) :
    ((do let peer ← pubkeyLookup key
         peerCommandAcquiredWith (fun {_} action=>action) peerCreate peerGet
           (fun ret=>do peerPut none; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
           (Configuration.peerConfigUpdateSource {attrs with flags:=some (flags ||| WGPEER_F_UPDATE_ONLY)})
           key psk (flags ||| WGPEER_F_UPDATE_ONLY) peer).run g).run a =
    ((do let peer ← pubkeyLookup key
         peerCommandAcquiredWith (fun {_} action=>action) peerCreate peerGet
           (fun ret=>do peerPut none; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
           (Configuration.peerConfigUpdateSource {attrs with flags:=some flags})
           key psk flags peer).run g).run a := by
  apply bind_run_congr
  intro peer v b run
  have selected := ((ensures_iff _ _ _).mpr (pubkeyLookup_present key pid d p found resident positive))
    g a peer v b device run
  have chosen := selected.1
  subst peer
  exact congrArg (fun action : WG.M Int => (action.run v).run b)
    (acquired_some attrs key flags psk pid)

theorem header_congr (attrs : PeerAttrs) (key : Key) (leftFlags rightFlags : UInt32)
    (left right : Key → Option Key → UInt32 → Option PeerId → WG.M Int)
    (pubkey : attrs.publicKey=some key)
    (leftValid : leftFlags &&& ~~~WGPEER_F_ALL=0)
    (rightValid : rightFlags &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (g : WGWorld) (a : Ambient)
    (same : ∀ before,
      ((pubkeyLookup key >>= left key attrs.presharedKey leftFlags).run g).run before =
      ((pubkeyLookup key >>= right key attrs.presharedKey rightFlags).run g).run before) :
    ((setPeerCmdWith (fun {_} action=>action) pubkeyLookup
      (fun ret=>do peerPut none; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
      left {attrs with flags:=some leftFlags}).run g).run a =
    ((setPeerCmdWith (fun {_} action=>action) pubkeyLookup
      (fun ret=>do peerPut none; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
      right {attrs with flags:=some rightFlags}).run g).run a := by
  rcases protocol with protocol | protocol
  all_goals cases psk : attrs.presharedKey
  all_goals simp [setPeerCmdWith,pubkey,protocol,leftValid,rightValid,
    WG.andM,branch,AmbientM.branch]
  all_goals simpa only [StateT.run_bind,psk] using same _

theorem existing_run (attrs : PeerAttrs) (key : Key) (flags : UInt32)
    (pid : PeerId) (d : Device) (p : Peer)
    (pubkey : attrs.publicKey=some key)
    (valid : flags &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (found : d.peerHashtable.find? (·.1 == key)=some (key,pid))
    (resident : d.peers[pid]?=some p) (positive : 0<p.refcount)
    (g : WGWorld) (a : Ambient) (device : g.dev=some d) :
    ((setPeerCmd {attrs with flags:=some (flags ||| WGPEER_F_UPDATE_ONLY)}).run g).run a =
    ((setPeerCmd {attrs with flags:=some flags}).run g).run a := by
  rw [←Configuration.setPeerCmd_source,Configuration.setPeerCmdSource_factor,
    ←Configuration.setPeerCmd_source,Configuration.setPeerCmdSource_factor]
  apply header_congr attrs key _ _ _ _ pubkey ((masks flags).1.trans valid) valid protocol g a
  intro before
  exact lookup_follow attrs key flags attrs.presharedKey pid d p found resident positive g before device

theorem absent_run (attrs : PeerAttrs) (key : Key) (flags : UInt32) (d : Device)
    (pubkey : attrs.publicKey=some key) (valid : flags &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (missing : d.peerHashtable.find? (·.1 == key)=none)
    (g : WGWorld) (a : Ambient) (device : g.dev=some d) :
    ∃ b, ((setPeerCmd {attrs with flags:=some (flags ||| WGPEER_F_UPDATE_ONLY)}).run g).run a
      =.ok ((0,g),b) := by
  rw [←Configuration.setPeerCmd_source,Configuration.setPeerCmdSource_factor]
  rcases protocol with protocol | protocol
  all_goals cases psk : attrs.presharedKey
  all_goals simp [setPeerCmdWith,peerCommandAcquiredWith,pubkey,protocol,
    (masks flags).1,valid,WG.andM,branch,AmbientM.branch,pubkeyLookup,getDev,device,
    missing,peerGetMaybeZero,blocks_creation,peerPut]

theorem validation_run (attrs : PeerAttrs) (code : Int)
    (refused : validationError attrs=some code) (g : WGWorld) (a : Ambient) :
    ∃ b, ((setPeerCmd attrs).run g).run a=.ok ((code,g),b) := by
  rw [←Configuration.setPeerCmd_source,Configuration.setPeerCmdSource_factor]
  cases pub : attrs.publicKey with
  | none =>
    have same : -EINVAL=code := by simpa [validationError,pub] using refused
    subst code
    simp [setPeerCmdWith,pub,WG.andM,branch,AmbientM.branch,peerPut]
  | some key =>
    by_cases invalid : attrs.flags.getD 0 &&& ~~~WGPEER_F_ALL ≠ 0
    · have same : -EOPNOTSUPP=code := by simpa [validationError,pub,invalid] using refused
      subst code
      cases flag : attrs.flags <;> cases psk : attrs.presharedKey
      all_goals simp only [flag,Option.getD_none,Option.getD_some] at invalid
      all_goals try {simp at invalid}
      all_goals simp [setPeerCmdWith,pub,flag,psk,invalid,WG.andM,branch,AmbientM.branch,peerPut]
    · cases protocol : attrs.protocolVersion with
      | none => simp [validationError,pub,invalid,protocol] at refused
      | some version =>
        by_cases good : version=1
        · simp [validationError,pub,invalid,protocol,good] at refused
        · have same : -EPFNOSUPPORT=code := by
            simpa [validationError,pub,invalid,protocol,good] using refused
          subst code
          cases flag : attrs.flags <;> cases psk : attrs.presharedKey
          all_goals simp only [flag,Option.getD_none,Option.getD_some] at invalid
          all_goals simp [setPeerCmdWith,pub,flag,psk,invalid,protocol,good,WG.andM,branch,AmbientM.branch,peerPut]

end Leanux.Proofs.WG.Config.UpdateOnly
