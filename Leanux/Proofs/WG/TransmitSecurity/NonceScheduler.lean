import Leanux.Proofs.WG.TransmitSecurity.NonceWorkers

/-! One nonce journal through the native source scheduler, including the
record-driven encryption completion preceding a TX activation. -/
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def cryptAheadObserved (pid : PeerId) : PrefixM Allocation Unit := do
  if (← liftPrefix getAmbient).hidden.isNone then return
  let some item := (← liftPrefix (liftWG (getPeer pid))).txQueue.all.head? | return
  let some id := item.head? | liftPrefix (invariant "an empty ring item")
  if (← liftPrefix (liftWG (getTxSkb id))).state != .uncrypted then return
  let next ← liftPrefix peekHiddenSite
  unless next == some HiddenSite.modTimerArm.info.id || next == some HiddenSite.timerJiffiesTraversal.info.id do return
  let some enc := (← liftPrefix getAmbient).suspended.find? (·.worker == .encryptWorker)
    | liftPrefix (throw (.hidden "the tx worker's head is uncrypted and no encrypt activation is suspended, but the next record is the traversal timer's caller read or arm (site 426 or 100)"))
  liftPrefix (liftWG (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]}))
  let r ← encryptIterObserved
  liftPrefix (liftWG (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase pid}))
  match r with
  | .continued =>
    liftPrefix (modifyAmbient fun s => {s with suspended := s.suspended.map fun x =>
      if x == enc then {x with iterations := x.iterations + 1} else x})
  | .ended => liftPrefix (throw (.hidden "the encrypt activation's queue is empty, but the next record is the traversal timer's caller read or arm (site 426 or 100)"))
  | .yielded => liftPrefix (invariant "the encrypt activation yielded on a record that is not a resched")

theorem cryptAheadObserved_erases (pid : PeerId) :
    ErasesPrefix (cryptAheadObserved pid) (Env.cryptAhead pid) := by
  unfold cryptAheadObserved Env.cryptAhead
  repeat' first
    | with_reducible exact encryptIterObserved_erases
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | (split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem cryptAheadObserved_safe (pid : PeerId) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (cryptAheadObserved pid) := by
  unfold cryptAheadObserved
  repeat' first
    | (nonce_product_head encryptIterObserved; exact encryptIterObserved_safe)
    | (nonce_product_head liftPrefix; first
       | with_reducible exact Frames.product_frame (Frames.peer_read _)
       | with_reducible exact Frames.product_frame (Frames.packet_read _)
       | with_reducible exact Frames.product_frame (Frames.update _ (fun _ => rfl)))
    | (nonce_product_head liftPrefix; first | exact Frames.product_ambient _ | with_reducible exact Frames.product_stop _)
    | exact PrefixPreserves.pure (fun _ _ hi => hi.nodup) _
    | apply PrefixPreserves.bind
    | (split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

def iterationObserved (a : Activation) : PrefixM Allocation IterResult := do
  match a.worker with
  | .encryptWorker => encryptIterObserved
  | .txWorker =>
    let some pid := a.pid | liftPrefix (invariant "a tx activation without its peer")
    cryptAheadObserved pid
    txIterObserved pid
  | .decryptWorker => decryptIterObserved
  | .receiveWorker => receiveIterObserved
  | w => liftPrefix (invariant s!"{w.symbol} is not a draining worker")

theorem iterationObserved_erases (a : Activation) :
    ErasesPrefix (iterationObserved a) (Env.Activation.iter a) := by
  unfold iterationObserved Env.Activation.iter
  repeat' first
    | with_reducible exact encryptIterObserved_erases
    | with_reducible exact decryptIterObserved_erases
    | exact receiveIterObserved_erases
    | with_reducible exact txIterObserved_erases _
    | with_reducible exact cryptAheadObserved_erases _
    | exact erasesPrefix_lift _
    | apply erasesPrefix_bind
    | (split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem iterationObserved_safe (a : Activation) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (iterationObserved a) := by
  unfold iterationObserved
  repeat' first
    | (nonce_product_head encryptIterObserved; exact encryptIterObserved_safe)
    | (nonce_product_head decryptIterObserved; exact decryptIterObserved_safe)
    | (nonce_product_head receiveIterObserved; exact receiveIterObserved_safe)
    | (nonce_product_head txIterObserved; exact txIterObserved_safe _)
    | (nonce_product_head cryptAheadObserved; exact cryptAheadObserved_safe _)
    | (nonce_product_head liftPrefix; first | exact Frames.product_ambient _ | with_reducible exact Frames.product_stop _)
    | apply PrefixPreserves.bind
    | (split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

def scheduleObserved (stack : Option Worker := none) : PrefixM Allocation Unit :=
  SourceScheduler.schedule iterationObserved softirqObserved stack

theorem scheduleObserved_erases (stack : Option Worker) :
    ErasesPrefix (scheduleObserved stack) (Env.schedule stack) :=
  SourceScheduler.schedule_erases _ _ iterationObserved_erases softirqObserved_erases stack

theorem scheduleObserved_safe (stack : Option Worker) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (scheduleObserved stack) :=
  SourceScheduler.schedule_preserves (fun _ _ hi => hi.nodup) Frames.product_store
    (fun _ => Frames.product_frame (Frames.update _ (fun _ => rfl)))
    _ _ iterationObserved_safe softirqObserved_safe stack

end Leanux.Proofs.WG.TransmitSecurity.Nonce
