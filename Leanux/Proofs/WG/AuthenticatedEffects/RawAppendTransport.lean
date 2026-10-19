import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendTransportSocket

/-! The real per-packet transport sender, with raw observations only at its
native socket append. Unsupported address families and failed sockets retain
their original result without an invented append event. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes TransmitSecurity

def transport (pid : PeerId) (packet : RunWitness DataPacket) : PrefixM Event Bool := do
  let peer ← captureObserved (liftPrefix (liftWG (getPeer pid)))
  let family := (peer.value.endpoint.map (·.family)).getD 0
  let ret ← do
    if ← liftPrefix (liftWG (branch .sendSkbInet (family == AF_INET))) then
      liftWGObserver (socket (transportArgs pid packet peer true))
    else if ← liftPrefix (liftWG (branch .sendSkbInet6 (family == AF_INET6))) then
      liftWGObserver (socket (transportArgs pid packet peer false))
    else pure (-EAFNOSUPPORT)
  let sent := ret == 0
  if ← liftPrefix (liftWG (branch .sendSkbOk sent)) then
    liftPrefix (liftWG (do
      let p ← getPeer pid
      setPeer pid {p with txBytes := p.txBytes + packet.value.bytes.length}))
  pure sent

theorem access_projects (action : MixedM α) (native : WG.M α)
    (erases : ErasesStatePrefix action native) :
    ProjectsPrefix completion? id (Completion.access action) (liftPrefix (liftWG native)) := by
  intro w history
  have result := Completion.access_erases erases w history
  have quiet := access_quiet action w history
  change ((liftWG native).run w,history.filterMap completion?) =
    ((runPrefix (Completion.access action) w history).1.map (fun (value,v) => (value,v)),
      (runPrefix (Completion.access action) w history).2.filterMap completion?)
  rw [result,quiet]
  cases (liftWG native).run w <;> rfl

private theorem capture_projects {g : PrefixM Completion.Event α} {t : PrefixM Event α}
    (h : ProjectsPrefix completion? id g t) :
    ProjectsPrefix completion? id (captureObserved g) (captureObserved t) := by
  intro w history
  rw [runPrefix_captureObserved,runPrefix_captureObserved,h w history]
  cases runPrefix g w history with
  | mk result events => cases result <;> rfl

theorem transport_projects (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket) :
    ProjectsPrefix completion? id (Completion.send pid skb packet) (transport pid packet) := by
  unfold Completion.send transport
  apply projectsPrefix_bind completion? id id
    (capture_projects (access_projects _ _ (getPeerMixed_erases pid)))
  intro peer
  repeat' first
    | (maintenance_head Completion.socket; exact transport_socket_projects _ _ _ _ _)
    | (maintenance_head Completion.access; exact access_projects _ _ (modifyPeerKeysPrefix_erases _ _))
    | (maintenance_head liftPrefix; exact projectsPrefix_lift completion? _)
    | (maintenance_head Pure.pure; exact projectsPrefix_pure completion? id _)
    | (maintenance_head Bind.bind; apply projectsPrefix_bind completion? id id)
    | (maintenance_head ite; apply projectsPrefix_ite completion? _ id)
    | (maintenance_intro; try dsimp only [id])
    | maintenance_reduce
    | (split; all_goals try simp_all only []; all_goals try subst_vars)

end Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
