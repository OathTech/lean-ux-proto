import Leanux.Proofs.WG.Config.ScalarPrefixEffects
import Leanux.Proofs.WG.Config.GetterPeerCommandClaims
import Leanux.Proofs.WG.Queues.JointConfigurationUpdate

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.ScalarPrefix
open Leanux Leanux.WG Noise Std.Do

def pskSource (pid : PeerId) (psk : Option Key) : WG.M Unit := do
  if ← branch .peerSetPsk psk.isSome then
    setPeer pid {(← getPeer pid) with presharedKey := psk.getD []}

def endpointSource (pid : PeerId) (endpoint : Option EndpointAttr) : WG.M Unit := do
  if ← branch .peerHasEndpoint endpoint.isSome then
    let some e := endpoint | invariant "unreachable"
    endpointAttributeUpdate pid e

def scalarPrefix (attrs : PeerAttrs) (psk : Option Key) (pid : PeerId) : WG.M Unit := do
  pskSource pid psk
  endpointSource pid attrs.endpoint

def remainder (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (pid : PeerId) : WG.M Int := do
  if ← branch .peerReplaceAips (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0) then
    removeByPeer pid
  peerConfigTailSource attrs peer pid

theorem source (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) :
    peerConfigUpdateSource attrs peer flags psk pid = (do
      if ← branch .peerRemoveMe (flags &&& WGPEER_F_REMOVE_ME != 0) then
        peerRemove peer
        peerPut peer
        _ ← branch .peerZeroPsk attrs.presharedKey.isSome
        pure 0
      else
        scalarPrefix attrs psk pid
        remainder attrs peer flags pid) := by
  cases ep : attrs.endpoint <;>
    simp only [peerConfigUpdateSource,scalarPrefix,pskSource,endpointSource,remainder,
      endpointAttributeUpdate,ep,bind_assoc,pure_bind,Queues.RxCredits.bind_if_source]

theorem psk_exact (pid : PeerId) (psk : Option Key) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (sock : NlSock) (fixtures : FixtureDevices) :
    Ensures (pskSource pid psk)
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun _ g => g.dev = some (keyedDevice d pid p psk) ∧ readbackFrame g sock fixtures) := by
  intro g ambient result final after pre run
  cases psk <;>
    simp [pskSource,branch,AmbientM.branch,getPeer,getDev,pre.1,resident,setPeer,modifyDev] at run
  all_goals rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
  · exact ⟨pre.1,pre.2⟩
  · exact ⟨rfl,pre.2⟩

theorem endpoint_exact (pid : PeerId) (endpoint : Option EndpointAttr) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (sock : NlSock) (fixtures : FixtureDevices) :
    Ensures (endpointSource pid endpoint)
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun _ g => ∃ reset, g.dev = some (match endpoint with
        | none => d | some a => endpointAttributeStores d pid p a reset) ∧
        readbackFrame g sock fixtures) := by
  cases endpoint with
  | none =>
    intro g ambient result final after pre run
    simp [endpointSource,branch,AmbientM.branch] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    exact ⟨none,pre⟩
  | some a =>
    have factor : endpointSource pid (some a) =
        (do _ ← branch .peerHasEndpoint true; endpointAttributeUpdate pid a) := by
      funext g ambient
      simp [endpointSource,branch,AmbientM.branch]
    rw [factor]
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
      (branch_state_spec (fun g => g.dev = some d ∧ readbackFrame g sock fixtures) _ true)) ?_
    intro ignored g ambient result final after pre run
    exact endpointAttribute_exact pid a d p resident sock fixtures g ambient result final after pre.2 run

theorem prefix_exact (attrs : PeerAttrs) (psk : Option Key) (pid : PeerId)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (sock : NlSock) (fixtures : FixtureDevices) :
    Ensures (scalarPrefix attrs psk pid)
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun _ g => ∃ reset, g.dev = some (effectDevice d pid p psk attrs.endpoint reset) ∧
        readbackFrame g sock fixtures) := by
  exact ensures_bind (pskSource pid psk) (fun _ => endpointSource pid attrs.endpoint)
    (psk_exact pid psk d p resident sock fixtures)
    (fun _ => by
      cases ep : attrs.endpoint <;>
        simpa only [effectDevice,ep] using
          (endpoint_exact pid attrs.endpoint (keyedDevice d pid p psk) (keyedPeer p psk)
            (keyed_resident d pid p psk resident) sock fixtures))

theorem update_run (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) (keep : flags &&& WGPEER_F_REMOVE_ME = 0)
    (g : WGWorld) (ambient : Ambient) :
    ((peerConfigUpdateSource attrs peer flags psk pid).run g).run ambient =
      (((scalarPrefix attrs psk pid).run g).run
        (CounterWindow.record ambient .peerRemoveMe false) >>= fun ((_,middle),next) =>
        ((remainder attrs peer flags pid).run middle).run next) := by
  rw [source]
  have no : (flags &&& WGPEER_F_REMOVE_ME != 0) = false := by simp [keep]
  simp only [no]
  rfl

def inspection (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) (g : WGWorld) (ambient : Ambient) : Inspection :=
  if flags &&& WGPEER_F_REMOVE_ME != 0 then
    ⟨Campaign2.observeResult (((peerConfigUpdateSource attrs peer flags psk pid).run g).run ambient),none⟩
  else
    match ((scalarPrefix attrs psk pid).run g).run (CounterWindow.record ambient .peerRemoveMe false) with
    | .error stop => ⟨.error stop,none⟩
    | .ok ((_,middle),next) =>
      ⟨Campaign2.observeResult (((remainder attrs peer flags pid).run middle).run next),
        some (Campaign2.snapshot middle next)⟩

def inspect (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) : WG.M Inspection := fun g ambient =>
  .ok ((inspection attrs peer flags psk pid g ambient,g),ambient)

theorem inspection_outcome (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) (g : WGWorld) (ambient : Ambient) :
    (inspection attrs peer flags psk pid g ambient).outcome =
      Campaign2.observeResult (((peerConfigUpdateSource attrs peer flags psk pid).run g).run ambient) := by
  by_cases keep : flags &&& WGPEER_F_REMOVE_ME = 0
  · rw [update_run attrs peer flags psk pid keep]
    unfold inspection
    simp only [keep,bne_self_eq_false,Bool.false_eq_true,ite_false]
    cases run : ((scalarPrefix attrs psk pid).run g).run
      (CounterWindow.record ambient .peerRemoveMe false) with
    | error stop => rfl
    | ok output => rcases output with ⟨⟨value,middle⟩,next⟩; rfl
  · have remove : (flags &&& WGPEER_F_REMOVE_ME != 0) = true := by simp [keep]
    simp only [inspection,remove,ite_true]

theorem inspection_facts (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) (keep : flags &&& WGPEER_F_REMOVE_ME = 0)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (g : WGWorld) (ambient : Ambient) (device : g.dev=some d) :
    Facts attrs psk pid d p (Campaign2.snapshot g ambient)
      (inspection attrs peer flags psk pid g ambient) := by
  unfold inspection
  simp only [keep,bne_self_eq_false,Bool.false_eq_true,ite_false]
  cases run : ((scalarPrefix attrs psk pid).run g).run
    (CounterWindow.record ambient .peerRemoveMe false) with
  | error stop =>
    constructor
    · intro completed same; cases same
    · intro _; exact ⟨stop,rfl⟩
  | ok output =>
    obtain ⟨⟨value,middle⟩,next⟩ := output
    have effect := prefix_exact attrs psk pid d p resident g.nlSock7 g.fixtureNetDevices
      g _ value middle next ⟨device,rfl,rfl⟩ run
    refine ⟨?_,(fun h=>by cases h)⟩
    intro completed same
    cases same
    exact effect

end Leanux.Proofs.WG.Config.ScalarPrefix
