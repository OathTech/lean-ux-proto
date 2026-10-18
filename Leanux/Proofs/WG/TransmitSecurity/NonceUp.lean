import Leanux.Proofs.WG.TransmitSecurity.NonceControlFrames

/-! Raising the interface can stage packets and keepalives. These callbacks
therefore remain observed through both the WireGuard and fixture wrappers. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def openObserved : WGPrefix Allocation Int := do
  let dev ← liftWGPrefix getDev
  _ ← liftWGPrefix (branch .openHasInet dev.inet4Dev)
  _ ← liftWGPrefix (branch .openHasInet6 dev.inet6Dev)
  let d ← liftWGPrefix getDev
  let ret ← liftWGPrefix (socketInit d.incomingPort)
  if ← liftWGPrefix (branch .openSocketError (ret < 0)) then return ret
  for pid in d.peerList do
    _ ← liftWGPrefix (branch .openPeersIter true)
    stagingObserved pid
    if ← liftWGPrefix (branch .openKeepalive ((← liftWGPrefix (getPeer pid)).persistentKeepaliveInterval != 0)) then
      keepaliveObserved pid
  _ ← liftWGPrefix (branch .openPeersIter false)
  return 0

def upObserved : WGPrefix Allocation Int := do
  liftWGPrefix (modifyDev fun d => {d with running := true})
  let ret ← openObserved
  if ret < 0 then liftWGPrefix (modifyDev fun d => {d with running := false})
  pure ret

def envUpObserved : PrefixM Allocation Int := do
  let some d := (← liftPrefix getWG).dev | return -ENODEV
  if d.running then return 0
  let ret ← liftWGObserver upObserved
  liftPrefix (skipCut allocCuts)
  if ret == 0 then
    liftPrefix Net.Fib.rtCacheFlush
    liftPrefix (Net.Fib.netdevUp WG0_IFINDEX)
  if ret == 0 then liftPrefix (modifyEnv fun w => {w with routesPending := true})
  pure ret

macro "nonce_up_erasure" : tactic => `(tactic| first
  | maintenance_intro
  | maintenance_erases_join
  | maintenance_erases_join_use
  | maintenance_reduce
  | maintenance_reduce_match
  | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
  | (maintenance_head stagingObserved; exact stagingObserved_erases _)
  | (maintenance_head keepaliveObserved; exact keepaliveObserved_erases _)
  | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
  | (maintenance_head Bind.bind; apply erasesStatePrefix_bind)
  | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
  | (maintenance_head ite; apply erasesStatePrefix_ite)
  | (with_reducible split))

theorem openObserved_erases : ErasesStatePrefix openObserved wgOpen := by
  unfold openObserved wgOpen
  repeat' nonce_up_erasure

theorem upObserved_erases : ErasesStatePrefix upObserved wgUp := by
  unfold upObserved wgUp
  repeat' first
    | (maintenance_head openObserved; exact openObserved_erases)
    | nonce_up_erasure

theorem envUpObserved_erases : ErasesPrefix envUpObserved Env.wgUp := by
  unfold envUpObserved Env.wgUp
  repeat' first
    | (maintenance_head upObserved; exact liftWGObserver_erases upObserved_erases)
    | nonce_deferred_erasure

macro "nonce_up_safe" : tactic => `(tactic| first
  | unfold StatePrefixPreserves
  | maintenance_join_let
  | maintenance_join_use
  | maintenance_reduce
  | maintenance_reduce_match
  | (nonce_source_head stagingObserved; exact stagingObserved_safe _)
  | (nonce_source_head keepaliveObserved; exact keepaliveObserved_safe _)
  | (nonce_source_head socketInit; exact Frames.lift_frame (Frames.socket_init _))
  | (nonce_source_head getPeer; exact Frames.lift_frame (Frames.peer_read _))
  | (nonce_source_head getDev; exact Frames.lift_frame Frames.device_read)
  | (nonce_source_head modifyDev; exact Frames.lift_frame (Frames.update _ (fun _ => rfl)))
  | (nonce_source_head branch; exact Frames.lift_frame (Frames.ambient _))
  | (nonce_source_head Pure.pure; exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.nodup) (fun _ _ _ hi => hi))
  | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
  | (nonce_source_head ForIn.forIn
     apply StatePrefixEnsures.forInInvariant _ _ _ (fun _ h w _ => Inv (view w) h) List.Nodup
       (fun _ _ _ _ hi => hi.nodup))
  | maintenance_intro
  | (with_reducible split))

theorem openObserved_safe : StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup openObserved := by
  unfold openObserved
  repeat' nonce_up_safe

theorem upObserved_safe : StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup upObserved := by
  unfold upObserved
  repeat' first
    | (nonce_source_head openObserved; exact openObserved_safe)
    | nonce_up_safe

theorem envUpObserved_safe : PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup envUpObserved := by
  have route {α : Type} (a : Net.M α) :
      PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (liftPrefix (monadLift a : Leanux.M α)) :=
    Frames.stored (fun s => productRouting_spec a (fun t => t = s))
  have edit (f : EnvWorld → EnvWorld) :
      PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (liftPrefix (modifyEnv f)) :=
    Frames.product_lift (fun _ => by unfold modifyEnv; apply hoare_modify; exact fun _ hi => hi)
  unfold envUpObserved
  repeat' first
    | (nonce_product_head liftWGObserver; exact upObserved_safe.liftWGObserver)
    | (scheduler_preserve_at modifyEnv; exact edit _)
    | (scheduler_preserve_at liftM; exact route _)
    | (scheduler_preserve_at skipCut; exact Frames.product_ambient _)
    | nonce_deferred_step

end Leanux.Proofs.WG.TransmitSecurity.Nonce
