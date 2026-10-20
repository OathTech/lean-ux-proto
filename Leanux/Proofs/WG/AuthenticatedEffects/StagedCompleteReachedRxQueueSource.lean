import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRxAccessCanonical

/-! Receive admission cuts retain the original packet read, saved peer queue, installation and device-ring continuation, including cuts before a later refusal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RxQueueAccess
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def front (skb : SkbId) : WG.M (Option (PeerId × Peer)) := do
  setRxSkb skb fun p=>{p with state:=.uncrypted}
  let packet ← getRxSkb skb
  let peer ← getPeer packet.peer
  if ← branch .enqueuePeerQueueFull (peer.rxQueue.count≥MAX_QUEUED_PACKETS) then return none
  pure (some (packet.peer,peer))

def installFinish (skb : SkbId) : Option (PeerId × Peer) → WG.M Bool
  | none=>pure false
  | some (pid,p)=>do
      setPeer pid {p with rxQueue:=p.rxQueue.enqueue skb}
      pure true

def install (skb : SkbId) : WG.M Bool := front skb >>= installFinish skb

def tail (skb : SkbId) (ready : Bool) : WG.M Int := do
  if !ready then return -ENOSPC
  let d ← getDev
  let cpu ← cpumaskNextOnlineFrom d.decryptLastCpu
  modifyDev fun d=>{d with decryptLastCpu:=cpu}
  if ← branch .enqueueRingFull d.decryptQueue.full then return -EPIPE
  queueDeviceWork .decryptWorker
  modifyDev fun d=>{d with decryptQueue:=d.decryptQueue.produce skb}
  pure 0

noncomputable def frontShape (skb : SkbId) : RxAccess.Shape (front skb) := by
  simp only [front,getPeer,getDev,branch,invariant]
  repeat' rx_access_source_step

noncomputable def tailShape (skb : SkbId) (ready : Bool) : Access.Shape (tail skb ready) := by
  simp only [tail,getDev,cpumaskNextOnlineFrom,branch,invariant]
  repeat' access_source_step

theorem source (skb : SkbId) : enqueuePerDeviceAndPeerRx skb=(install skb >>= tail skb) := by
  simp only [enqueuePerDeviceAndPeerRx,install,front,bind_assoc]
  repeat' first
    | rfl
    | apply RxWorkers.bind_congr
    | maintenance_intro
    | split
    | dsimp (config := {failIfUnchanged := true}) only [installFinish,tail]
    | simp (config := {failIfUnchanged := true}) only [pure_bind]
    | simp (config := {failIfUnchanged := true}) only [bind_assoc]

theorem written_install
    (prepared : ((front skb).run w).run a=.ok ((some (pid,p),u),c))
    (written : ((setPeer pid {p with rxQueue:=p.rxQueue.enqueue skb}).run u).run c=.ok (((),v),b)) :
    ((install skb).run w).run a=.ok ((true,v),b) := by
  unfold install
  rw [MaterialOrigin.bind_ok_ambient]
  refine ⟨_,_,_,prepared,?_⟩
  change (((setPeer pid {p with rxQueue:=p.rxQueue.enqueue skb} >>= fun _=>pure true).run u).run c)=_
  rw [MaterialOrigin.bind_ok_ambient]
  exact ⟨(),v,b,written,rfl⟩

inductive Point (skb : SkbId) : WGWorld → Ambient → WGWorld → Ambient → Prop where
  | front (point : RxAccess.Point (frontShape skb) w a v b) : Point skb w a v b
  | written (prepared : ((front skb).run w).run a=.ok ((some (pid,p),u),c))
      (written : ((setPeer pid {p with rxQueue:=p.rxQueue.enqueue skb}).run u).run c=.ok (((),v),b)) : Point skb w a v b
  | afterInstall (installed : ((install skb).run w).run a=.ok ((ready,u),c))
      (point : Access.Point (tailShape skb ready) u c v b) : Point skb w a v b
  | returned (performed : ((enqueuePerDeviceAndPeerRx skb).run w).run a=.ok ((value,v),b)) : Point skb w a v b

theorem Point.remaining (point : Point skb w a v b) :
    ∃remaining : WG.M Int,((enqueuePerDeviceAndPeerRx skb).run w).run a=(remaining.run v).run b := by
  cases point with
  | front point=>
      obtain ⟨rest,same⟩:=point.remaining
      refine ⟨rest >>= fun value=>installFinish skb value >>= tail skb,?_⟩
      rw [source]
      simp only [install,bind_assoc,StateT.run_bind,same]
  | written prepared written=>
      refine ⟨tail skb true,?_⟩
      rw [source]
      simp only [StateT.run_bind,written_install prepared written]
      rfl
  | afterInstall installed point=>
      obtain ⟨rest,same⟩:=point.remaining
      refine ⟨rest,?_⟩
      rw [source]
      simp only [StateT.run_bind,installed]
      exact same
  | returned performed=>exact ⟨pure _,performed⟩

theorem Point.observed_remaining {E : Type} {w : World}
    (point : Point skb w.wg w.ambient v b) (h : List E) :
    ∃remaining : PrefixM E Int,runPrefix (liftWGObserver (liftWGPrefix (enqueuePerDeviceAndPeerRx skb))) w h=
      runPrefix remaining {w with wg:=v,ambient:=b} h := by
  obtain ⟨rest,same⟩:=point.remaining
  refine ⟨liftWGObserver (liftWGPrefix rest),?_⟩
  simp only [liftWGObserver_run,runWGPrefix_lift,same]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RxQueueAccess
