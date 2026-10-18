import Leanux.Proofs.WG.Index.IncomingCallerModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders
namespace Incoming

theorem core_sender {α : Type} (action : WG.M α)
    (frame : SameView senderFields action)
    (tables : Ensures action TablesSafeWG (fun _ => TablesSafeWG)) :
    Ensures action Reached.Core (fun _ => Reached.Core) := by
  intro g a result out b pre run
  have state := responseIndex_sender_frame action frame g a result out b
    (fun d device => (pre d device).2) run
  have table := tables g a result out b (fun d device => (pre d device).1) run
  exact fun d device => ⟨table d device,state d device⟩

theorem endpointStores_sender (d : Device) (pid : PeerId) (p : Peer)
    (endpoint : Endpoint) (reset : Option UInt64) (resident : d.peers[pid]?=some p) :
    senderDeviceCell (Config.endpointStores d pid p endpoint reset)=senderDeviceCell d := by
  unfold Config.endpointStores
  split
  · rfl
  · cases reset with
    | none => exact senderFields_peerWrite d pid p _ resident rfl
    | some ts =>
      let written := {p with endpoint:=some endpoint}
      let updated := {written with dstCache:={written.dstCache with resetTs:=ts}}
      exact (senderFields_peerWrite (Config.withPeer d pid written)
        pid written updated (by simp [Config.withPeer]) rfl).trans
        (senderFields_peerWrite d pid p written resident rfl)

theorem endpoint_sender (pid : PeerId) (endpoint : Endpoint)
    (valid : endpoint.family=AF_INET ∨ endpoint.family=AF_INET6) :
    SameView senderFields (setPeerEndpoint pid endpoint) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result out b run
  cases device : g.dev with
  | none =>
    simp [setPeerEndpoint,requireNotPending,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [setPeerEndpoint,requireNotPending,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨reset,effect,_,_⟩ := Config.setPeerEndpoint_exact pid endpoint d p resident
        valid g.nlSock7 g.fixtureNetDevices g a result out b ⟨device,rfl,rfl⟩ run
      simp only [senderFields,effect,device,Option.map_some]
      exact congrArg some (endpointStores_sender d pid p endpoint reset resident)

theorem endpointFromSkb_sender (pid : PeerId) (src : SkbSource) :
    SameView senderFields (setPeerEndpointFromSkb pid src) := by
  intro initial
  apply (ensures_iff _ _ _).mp
  let P := fun g => senderFields g=initial
  unfold setPeerEndpointFromSkb
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (Roaming.endpointFromSkb_exact src P)) ?_
  intro endpoint g a result out b pre run
  obtain ⟨kept,rfl,_⟩ := pre
  have valid : (Roaming.sourceEndpoint src).family=AF_INET ∨
      (Roaming.sourceEndpoint src).family=AF_INET6 := by
    unfold Roaming.sourceEndpoint
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  have continuation : Ensures (do
      if ← branch .epFromSkbOk (some (Roaming.sourceEndpoint src)).isSome then
        setPeerEndpoint pid (Roaming.sourceEndpoint src)) P (fun _ => P) := by
    refine ensures_bind _ _
      ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch .epFromSkbOk true) P)) ?_
    intro ok
    cases ok with
    | false => intro _ _ _ _ _ hi run; cases run; exact hi
    | true => exact (ensures_iff _ _ _).mpr (endpoint_sender pid _ valid initial)
  exact continuation g a result out b kept run

theorem handshakeComplete_sender (pid : PeerId) (site : HiddenSite) :
    SameView senderFields (timersHandshakeComplete pid site) := by
  intro initial
  apply (ensures_iff _ _ _).mp
  let P := fun g => senderFields g=initial
  have updateFactor (f : Peer → Peer) :
      modifyPeer pid f = (do let p ← getPeer pid; setPeer pid (f p)) := rfl
  have factor : timersHandshakeComplete pid site = (do
      delTimer pid .retransmitHandshake
      modifyPeer pid (fun p => {p with timerHandshakeAttempts:=0,sentLastminuteHandshake:=false})
      let now ← hidden site
      modifyPeer pid (fun p => {p with walltimeLastHandshake:=now})) := by
    simp only [timersHandshakeComplete,updateFactor,bind_assoc]
  rw [factor]
  change Ensures _ P (fun _ => P)
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (sender_delTimer pid .retransmitHandshake initial)) ?_
  intro _
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (sender_modifyPeer pid (fun p => {p with timerHandshakeAttempts:=0,sentLastminuteHandshake:=false}) (fun _ => rfl) initial)) ?_
  intro _
  refine ensures_bind _ _
    ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.hidden site) P)) ?_
  intro now
  exact (ensures_iff _ _ _).mpr (sender_modifyPeer pid (fun p => {p with walltimeLastHandshake:=now}) (fun _ => rfl) initial)


end Incoming
end Leanux.Proofs.WG.Index
