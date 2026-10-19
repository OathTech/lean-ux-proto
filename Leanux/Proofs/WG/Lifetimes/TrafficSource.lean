import Leanux.Proofs.WG.Lifetimes.BatchItemSource
import Leanux.Proofs.WG.Queues.RxTrafficAppends
import Leanux.Proofs.WG.Queues.PollSource

/-! Actual traffic callers with explicit receive, scheduling, and drain
observers. Their source guards and fixture actions remain unchanged. -/
namespace Leanux.Proofs.WG.Lifetimes.TrafficSource
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged
open Queues RxJoint.PollSource

def injectWith {E : Type} (receive : List UInt8 → SkbSource → PrefixM E Unit)
    (crypt : PrefixM E Unit) (drained : String → List Bool → PrefixM E Unit)
    (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) : PrefixM E Int := do
  if (← liftPrefix getRouting).foreignCreator then
    if (← liftPrefix getEnv).netnsCHolders.isEmpty then liftPrefix (unsupported "wg_inject after wg_netns_close (no socket in the creating namespace)")
    if dest == 1 then liftPrefix (unsupported "wg_inject to wg0's address from the creating namespace (unroutable)")
  let some d := (← liftPrefix getWG).dev | liftPrefix (unsupported "a datagram to a port other than wg0's (no wg0)")
  if !d.running || port != d.incomingPort then liftPrefix (unsupported "a datagram to a port other than wg0's")
  for pid in d.peerList do liftPrefix (liftWG (requireNotPending pid "receiving while a handshake is queued"))
  liftPrefix fixtureSend
  let src ← liftPrefix (senderSource family dest tos ll)
  if family == 4 then
    match ← liftPrefix (Net.Fib.inSocketNs (Net.routeOutput4 0 src.daddr)) with
    | .error _ => liftPrefix (invariant "wg_inject: the injector's datagram has no route")
    | .ok r =>
      if r.dev != LO_IFINDEX || r.src != src.saddr then
        liftPrefix (invariant "wg_inject: the route disagrees with the sender source")
      liftPrefix (Net.Fib.inSocketNs (Net.neighbourClassify LO_IFINDEX))
  runWorkerPrefix .netRx (receive msg src)
  crypt
  let d ← liftPrefix (liftWG getDev)
  drained "the datagram queued"
    [!d.handshakeQueue.empty, !d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty]
  return msg.length

def afterBatchWith {E : Type} (crypt send sendOne : PrefixM E Unit)
    (schedule : Option Worker → PrefixM E Unit)
    (drained : String → List Bool → PrefixM E Unit) : PrefixM E Unit := do
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  if (← liftPrefix getAmbient).hidden.isNone then
    crypt
    send
    return
  for _ in [0:(← liftPrefix recordBudget)] do
    schedule none
    if (← liftPrefix peekNextSite) == some (HiddenSite.sectionStart .sendWorker).info.id && !(← liftPrefix (liftWG getDev)).sendWorkQueue.isEmpty then
      sendOne
    else break
  let d ← liftPrefix (liftWG getDev)
  drained "the batch queued"
    [!d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty, !d.sendWorkQueue.isEmpty,
     !d.handshakeQueue.empty, d.handshakeQueueLen != 0]
  liftPrefix deliverSent

def floodWith {E : Type} (receive : List UInt8 → SkbSource → PrefixM E Unit)
    (poll after : PrefixM E Unit) (drained : String → List Bool → PrefixM E Unit)
    (count port family : Nat) (messages : List (List UInt8)) : PrefixM E Int := do
  let some d := (← liftPrefix getWG).dev | liftPrefix (unsupported "a flood to a port other than wg0's (no wg0)")
  if !d.running || port != d.incomingPort then liftPrefix (unsupported "a flood to a port other than wg0's")
  for pid in d.peerList do liftPrefix (liftWG (requireNotPending pid "a flood while a handshake is queued"))
  let invalid : List UInt8 := [1] ++ List.replicate 115 0 ++ List.replicate 16 0xff ++ List.replicate 16 0
  let src ← liftPrefix (senderSource family 0)
  for msg in messages ++ List.replicate count invalid do
    if family == 4 then
      match ← liftPrefix (Net.routeOutput4 0 src.daddr) with
      | .error _ => liftPrefix (invariant "wg_flood: the datagram to wg0's port has no route")
      | .ok r =>
        if r.dev != LO_IFINDEX || r.src != src.saddr then
          liftPrefix (invariant "wg_flood: the route disagrees with the sender source")
        liftPrefix (Net.neighbourClassify LO_IFINDEX)
    liftPrefix fixtureSend
    runWorkerPrefix .netRx do
      receive msg src
      poll
  after
  let d ← liftPrefix (liftWG getDev)
  drained "the flood queued" [!d.handshakeQueue.empty, d.handshakeQueueLen != 0]
  return 0

def batchWith {E : Type} (one : Device → List Int → BatchItem → PrefixM E (ForInStep (List Int)))
    (after : PrefixM E Unit) (items : List BatchItem) : PrefixM E Int := do
  let some d := (← liftPrefix getWG).dev | liftPrefix (unsupported "a batch without wg0")
  if !d.running then liftPrefix (unsupported "a batch with wg0 down")
  for pid in d.peerList do liftPrefix (liftWG (requireNotPending pid "a batch while a handshake is queued"))
  let cqes ← forIn items ([] : List Int) (fun item cqes => one d cqes item)
  liftPrefix (modifyAmbient fun w => {w with extraOut := [("cqes", Lean.toJson cqes)]})
  after
  return items.length

theorem inject_factor (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    RxHistory.inject family port msg tos ll dest =
      injectWith (fun msg src => RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src)))
        RxHistory.runCryptWorkers (fun what flags => RxHistory.mixed (requireDrainedPrefix what flags))
        family port msg tos ll dest := rfl

theorem afterBatch_factor : RxHistory.afterBatch =
    afterBatchWith RxHistory.runCryptWorkers RxHistory.runSendWorkers
      (RxHistory.audit runOneSendWorkerAudit) (fun stack => RxHistory.schedule stack)
      (fun what flags => RxHistory.mixed (requireDrainedPrefix what flags)) := rfl

theorem flood_factor (count port family : Nat) (messages : List (List UInt8)) :
    RxHistory.flood count port family messages =
      floodWith (fun msg src => RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src)))
        RxHistory.pollScheduledInline RxHistory.afterBatch
        (fun what flags => RxHistory.mixed (requireDrainedPrefix what flags)) count port family messages := rfl

theorem batch_factor (items : List BatchItem) : RxHistory.batch items =
    batchWith RxHistory.batchItem RxHistory.afterBatch items := rfl

theorem inject_projects {E F : Type} (ρ : E → Option F)
    (receive : List UInt8 → SkbSource → PrefixM E Unit) (receive' : List UInt8 → SkbSource → PrefixM F Unit)
    (crypt : PrefixM E Unit) (crypt' : PrefixM F Unit)
    (drained : String → List Bool → PrefixM E Unit) (drained' : String → List Bool → PrefixM F Unit)
    (hr : ∀ msg src, ProjectsPrefix ρ id (receive msg src) (receive' msg src))
    (hc : ProjectsPrefix ρ id crypt crypt')
    (hd : ∀ what flags, ProjectsPrefix ρ id (drained what flags) (drained' what flags))
    (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ProjectsPrefix ρ id (injectWith receive crypt drained family port msg tos ll dest)
      (injectWith receive' crypt' drained' family port msg tos ll dest) := by
  unfold injectWith
  repeat' first
    | (poll_source_head receive; exact hr _ _)
    | (poll_source_head crypt; exact hc)
    | (poll_source_head drained; exact hd _ _)
    | (poll_source_head runWorkerPrefix; apply runWorkerPrefix_projects ρ)
    | (poll_source_head liftPrefix; exact projectsPrefix_lift ρ _)
    | (poll_source_head Pure.pure; first | exact projectsPrefix_pure ρ id _ | exact projectsPrefix_pure ρ (projectStep id) _)
    | (poll_source_head Bind.bind; first | apply projectsPrefix_bind ρ id id | apply projectsPrefix_bind ρ id (projectStep id))
    | (poll_source_head ForIn.forIn; first | apply projectsPrefix_forIn ρ id | apply projectsPrefix_range ρ id)
    | (poll_source_head ite; apply projectsPrefix_ite)
    | maintenance_intro
    | dsimp only [id]
    | split

theorem afterBatch_projects {E F : Type} (ρ : E → Option F)
    (crypt send sendOne : PrefixM E Unit) (crypt' send' sendOne' : PrefixM F Unit)
    (schedule : Option Worker → PrefixM E Unit) (schedule' : Option Worker → PrefixM F Unit)
    (drained : String → List Bool → PrefixM E Unit) (drained' : String → List Bool → PrefixM F Unit)
    (hc : ProjectsPrefix ρ id crypt crypt') (hs : ProjectsPrefix ρ id send send')
    (ho : ProjectsPrefix ρ id sendOne sendOne')
    (hsch : ∀ stack, ProjectsPrefix ρ id (schedule stack) (schedule' stack))
    (hd : ∀ what flags, ProjectsPrefix ρ id (drained what flags) (drained' what flags)) :
    ProjectsPrefix ρ id (afterBatchWith crypt send sendOne schedule drained)
      (afterBatchWith crypt' send' sendOne' schedule' drained') := by
  unfold afterBatchWith
  repeat' first
    | (poll_source_head crypt; exact hc)
    | (poll_source_head send; exact hs)
    | (poll_source_head sendOne; exact ho)
    | (poll_source_head schedule; exact hsch _)
    | (poll_source_head drained; exact hd _ _)
    | (poll_source_head runWorkerPrefix; apply runWorkerPrefix_projects ρ)
    | (poll_source_head liftPrefix; exact projectsPrefix_lift ρ _)
    | (poll_source_head Pure.pure; first | exact projectsPrefix_pure ρ id _ | exact projectsPrefix_pure ρ (projectStep id) _)
    | (poll_source_head Bind.bind; first | apply projectsPrefix_bind ρ id id | apply projectsPrefix_bind ρ id (projectStep id))
    | (poll_source_head ForIn.forIn; first | apply projectsPrefix_forIn ρ id | apply projectsPrefix_range ρ id)
    | (poll_source_head ite; apply projectsPrefix_ite)
    | maintenance_intro
    | dsimp only [id]
    | split

theorem flood_projects {E F : Type} (ρ : E → Option F)
    (receive : List UInt8 → SkbSource → PrefixM E Unit) (receive' : List UInt8 → SkbSource → PrefixM F Unit)
    (poll after : PrefixM E Unit) (poll' after' : PrefixM F Unit)
    (drained : String → List Bool → PrefixM E Unit) (drained' : String → List Bool → PrefixM F Unit)
    (hr : ∀ msg src, ProjectsPrefix ρ id (receive msg src) (receive' msg src))
    (hp : ProjectsPrefix ρ id poll poll') (ha : ProjectsPrefix ρ id after after')
    (hd : ∀ what flags, ProjectsPrefix ρ id (drained what flags) (drained' what flags))
    (count port family : Nat) (messages : List (List UInt8)) :
    ProjectsPrefix ρ id (floodWith receive poll after drained count port family messages)
      (floodWith receive' poll' after' drained' count port family messages) := by
  unfold floodWith
  repeat' first
    | (poll_source_head receive; exact hr _ _)
    | (poll_source_head poll; exact hp)
    | (poll_source_head after; exact ha)
    | (poll_source_head drained; exact hd _ _)
    | (poll_source_head runWorkerPrefix; apply runWorkerPrefix_projects ρ)
    | (poll_source_head liftPrefix; exact projectsPrefix_lift ρ _)
    | (poll_source_head Pure.pure; first | exact projectsPrefix_pure ρ id _ | exact projectsPrefix_pure ρ (projectStep id) _)
    | (poll_source_head Bind.bind; first | apply projectsPrefix_bind ρ id id | apply projectsPrefix_bind ρ id (projectStep id))
    | (poll_source_head ForIn.forIn; first | apply projectsPrefix_forIn ρ id | apply projectsPrefix_range ρ id)
    | (poll_source_head ite; apply projectsPrefix_ite)
    | maintenance_intro
    | dsimp only [id]
    | split

theorem batch_projects {E F : Type} (ρ : E → Option F)
    (one : Device → List Int → BatchItem → PrefixM E (ForInStep (List Int)))
    (one' : Device → List Int → BatchItem → PrefixM F (ForInStep (List Int)))
    (after : PrefixM E Unit) (after' : PrefixM F Unit)
    (ho : ∀ d cqes item, ProjectsPrefix ρ (projectStep id) (one d cqes item) (one' d cqes item))
    (ha : ProjectsPrefix ρ id after after') (items : List BatchItem) :
    ProjectsPrefix ρ id (batchWith one after items) (batchWith one' after' items) := by
  unfold batchWith
  repeat' first
    | (poll_source_head one; exact ho _ _ _)
    | (poll_source_head after; exact ha)
    | (poll_source_head runWorkerPrefix; apply runWorkerPrefix_projects ρ)
    | (poll_source_head liftPrefix; exact projectsPrefix_lift ρ _)
    | (poll_source_head Pure.pure; first | exact projectsPrefix_pure ρ id _ | exact projectsPrefix_pure ρ (projectStep id) _)
    | (poll_source_head Bind.bind; first | apply projectsPrefix_bind ρ id id | apply projectsPrefix_bind ρ id (projectStep id))
    | (poll_source_head ForIn.forIn; first | apply projectsPrefix_forIn ρ id | apply projectsPrefix_range ρ id)
    | (poll_source_head ite; apply projectsPrefix_ite)
    | maintenance_intro
    | dsimp only [id]
    | split

theorem inject_appends {E : Type}
    (receive : List UInt8 → SkbSource → PrefixM E Unit) (crypt : PrefixM E Unit)
    (drained : String → List Bool → PrefixM E Unit)
    (hr : ∀ msg src, Appends (receive msg src)) (hc : Appends crypt)
    (hd : ∀ what flags, Appends (drained what flags))
    (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Appends (injectWith receive crypt drained family port msg tos ll dest) := by
  unfold injectWith
  repeat' first
    | (poll_source_head receive; exact hr _ _)
    | (poll_source_head crypt; exact hc)
    | (poll_source_head drained; exact hd _ _)
    | (poll_source_head runWorkerPrefix
       apply (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.runWorker_appends))
    | (poll_source_head liftPrefix; exact Appends.lift _)
    | (poll_source_head Pure.pure; exact Appends.pure _)
    | (poll_source_head Bind.bind; apply Appends.bind)
    | (poll_source_head ForIn.forIn; first | apply Appends.forIn | apply Appends.range)
    | (poll_source_head ite; apply Appends.ite)
    | maintenance_intro
    | dsimp only
    | split

theorem afterBatch_appends {E : Type} (crypt send sendOne : PrefixM E Unit)
    (schedule : Option Worker → PrefixM E Unit) (drained : String → List Bool → PrefixM E Unit)
    (hc : Appends crypt) (hs : Appends send) (ho : Appends sendOne)
    (hsch : ∀ stack, Appends (schedule stack)) (hd : ∀ what flags, Appends (drained what flags)) :
    Appends (afterBatchWith crypt send sendOne schedule drained) := by
  unfold afterBatchWith
  repeat' first
    | (poll_source_head crypt; exact hc)
    | (poll_source_head send; exact hs)
    | (poll_source_head sendOne; exact ho)
    | (poll_source_head schedule; exact hsch _)
    | (poll_source_head drained; exact hd _ _)
    | (poll_source_head runWorkerPrefix
       apply (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.runWorker_appends))
    | (poll_source_head liftPrefix; exact Appends.lift _)
    | (poll_source_head Pure.pure; exact Appends.pure _)
    | (poll_source_head Bind.bind; apply Appends.bind)
    | (poll_source_head ForIn.forIn; first | apply Appends.forIn | apply Appends.range)
    | (poll_source_head ite; apply Appends.ite)
    | maintenance_intro
    | dsimp only
    | split

theorem flood_appends {E : Type}
    (receive : List UInt8 → SkbSource → PrefixM E Unit) (poll after : PrefixM E Unit)
    (drained : String → List Bool → PrefixM E Unit)
    (hr : ∀ msg src, Appends (receive msg src)) (hp : Appends poll) (ha : Appends after)
    (hd : ∀ what flags, Appends (drained what flags))
    (count port family : Nat) (messages : List (List UInt8)) :
    Appends (floodWith receive poll after drained count port family messages) := by
  unfold floodWith
  repeat' first
    | (poll_source_head receive; exact hr _ _)
    | (poll_source_head poll; exact hp)
    | (poll_source_head after; exact ha)
    | (poll_source_head drained; exact hd _ _)
    | (poll_source_head runWorkerPrefix
       apply (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.runWorker_appends))
    | (poll_source_head liftPrefix; exact Appends.lift _)
    | (poll_source_head Pure.pure; exact Appends.pure _)
    | (poll_source_head Bind.bind; apply Appends.bind)
    | (poll_source_head ForIn.forIn; first | apply Appends.forIn | apply Appends.range)
    | (poll_source_head ite; apply Appends.ite)
    | maintenance_intro
    | dsimp only
    | split

theorem batch_appends {E : Type}
    (one : Device → List Int → BatchItem → PrefixM E (ForInStep (List Int))) (after : PrefixM E Unit)
    (ho : ∀ d cqes item, Appends (one d cqes item)) (ha : Appends after) (items : List BatchItem) :
    Appends (batchWith one after items) := by
  unfold batchWith
  repeat' first
    | (poll_source_head one; exact ho _ _ _)
    | (poll_source_head after; exact ha)
    | (poll_source_head runWorkerPrefix
       apply (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.runWorker_appends))
    | (poll_source_head liftPrefix; exact Appends.lift _)
    | (poll_source_head Pure.pure; exact Appends.pure _)
    | (poll_source_head Bind.bind; apply Appends.bind)
    | (poll_source_head ForIn.forIn; first | apply Appends.forIn | apply Appends.range)
    | (poll_source_head ite; apply Appends.ite)
    | maintenance_intro
    | dsimp only
    | split

end Leanux.Proofs.WG.Lifetimes.TrafficSource
