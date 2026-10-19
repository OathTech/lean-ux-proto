import Leanux.Proofs.WG.RetirementSecurity.OccurrenceControls
import Leanux.Proofs.WG.Queues.TxLiveTraffic

/-! Existing concrete traffic source factors transport initialized-boundary
physical TX ownership through native ingress, batch, flood and deferred work. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceTraffic
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open Queues.RxCredits OccurrenceStack

abbrev Inv (_ : List RxHistory.Event) (w : World) := Ready [] [] w.wg

theorem wg_store {w v : World} (same : wgStoreView v.wg = wgStoreView w.wg)
    (before : Ready [] [] w.wg) : Ready [] [] v.wg := ready_store same before

theorem product_store {w v : World} (same : productStoreView v=productStoreView w)
    (before : Ready [] [] w.wg) : Ready [] [] v.wg :=
  wg_store (congrArg (fun s : ProductStore43=>s.2.2.2) same) before

theorem observed {E α : Type} (g : PrefixM E α) (a : Leanux.M α)
    (appends : Appends g) (erases : ErasesPrefix g a)
    (keeps : Preserves (fun w : World=>Ready [] [] w.wg) a) :
    PrefixPreserves (fun _ w=>Ready [] [] w.wg) (fun _=>True) g :=
  (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.OccurrenceNapi.«0».Leanux.Proofs.WG.RetirementSecurity.OccurrenceNapi.observed)
    [] [] g a appends erases keeps

theorem native {E α : Type} (g : PrefixM E α) (a : Leanux.M α)
    (erases : ErasesPrefix g a)
    (keeps : PrefixPreserves (fun _ w=>Ready [] [] w.wg) (fun _=>True) g) :
    Preserves (fun w : World=>Ready [] [] w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  have actual := (erases w []).trans run
  have post := (keeps w [] before).choose_spec.2.2
  rw [actual] at post
  exact post

theorem receive_observed (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves Inv (fun _=>True) (RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src))) :=
  observed _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases (wgReceivePrefix_erases msg src)))
    (PublicationPoll.native_product (Ready [] []) _
      (RxPollOccurrences.join (ReceiveIngressCall.erases (.udp msg src)) (ReceiveIngressCall.allocation (.udp msg src))
        (ReceiveOccurrences.receive msg src)))

theorem transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    PrefixPreserves (fun _ w=>Ready [] [] w.wg) (fun _=>True)
      (RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu))) :=
  observed _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases (wgXmitPrefix_erases family addr packets mtu)))
    (OccurrenceStack.transmit family addr packets mtu)

theorem multicast (family addr : Nat) :
    PrefixPreserves (fun _ w=>Ready [] [] w.wg) (fun _=>True)
      (RxHistory.audit (xmitMulticastLoopAudit family addr)) := by
  apply observed _ _ (Appends.focus _ _ _)
    (RxHistory.audit_erases (xmitMulticastLoopAudit_erases family addr))
  have frame := (pinned_const _private.Leanux.Proofs.WG.Queues.BatchAccount.«0».Leanux.Proofs.WG.Queues.RxCredits.BatchAccount.multicast_store) family addr
  exact OccurrenceControls.product_store frame

theorem batch_item (d : Device) (cqes : List Int) (item : BatchItem) :
    PrefixPreserves (fun _ w=>Ready [] [] w.wg) (fun _=>True) (RxHistory.batchItem d cqes item) := by
  rw [rxBatchItem_factor]
  exact batchItemWith_preserves (fun _ _ _=>True.intro) (fun _ _ _ eq hi=>wg_store eq hi)
    _ _ _ _ receive_observed (OccurrenceNapi.inline_observed [] []) multicast transmit d cqes item

theorem batch_loop (d : Device) (items : List BatchItem) (cqes : List Int) :
    PrefixPreserves (fun _ w=>Ready [] [] w.wg) (fun _=>True) (BatchAccount.loop d items cqes) := by
  unfold BatchAccount.loop
  apply PrefixPreserves.forIn
  · exact fun _ _ _=>True.intro
  · intro item qs
    exact batch_item d qs item

theorem receive_section (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves (fun _ w=>Ready [] [] w.wg) (fun _=>True) (FloodSection.action msg src) := by
  unfold FloodSection.action AdmissionCaller.receive
  apply runWorkerPrefix_preserves (fun _ _ _=>True.intro) (fun _ _ _ eq hi=>product_store eq hi)
  exact PrefixPreserves.bind (receive_observed msg src) (fun _=>(OccurrenceNapi.inline_observed [] []))

theorem flood_route (family : Nat) (src : SkbSource) :
    PrefixPreserves (fun _ w=>Ready [] [] w.wg) (fun _=>True) (FloodLoop.route family src) := by
  have safe : ∀ h w,(fun (_ : List RxHistory.Event) (w : World)=>Ready [] [] w.wg) h w→True := fun _ _ _=>True.intro
  have store : ∀ (h : List RxHistory.Event) w v,productStoreView v=productStoreView w→Ready [] [] w.wg→Ready [] [] v.wg := fun _ _ _ eq hi=>product_store eq hi
  unfold FloodLoop.route
  repeat' traffic_preserve_source safe using store

theorem flood_one (family : Nat) (src : SkbSource) (msg : List UInt8) :
    PrefixPreserves (fun _ w=>Ready [] [] w.wg) (fun _=>True) (FloodLoop.one family src msg) :=
  PrefixPreserves.bind (flood_route family src) (fun _=>receive_section msg src)

theorem flood_loop (family : Nat) (src : SkbSource) (messages : List (List UInt8)) :
    PrefixPreserves (fun _ w=>Ready [] [] w.wg) (fun _=>True) (FloodLoop.loop family src messages) := by
  induction messages with
  | nil=>exact PrefixPreserves.pure (fun _ _ _=>True.intro) _
  | cons msg messages ih=>
    rw [FloodLoop.loop_cons]
    exact PrefixPreserves.bind (flood_one family src msg) (fun _=>ih)

theorem inject_front (family port tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves (fun _ w=>Ready [] [] w.wg) (fun _=>True)
      (InjectAccount.front family port tos ll dest) :=
  InjectAccount.front_preserves (fun _ _ _=>True.intro) (fun _ _ _ eq hi=>product_store eq hi)

theorem drained_observed (what : String) (flags : List Bool) :
    PrefixPreserves Inv (fun _=>True)
      (RxHistory.mixed (requireDrainedPrefix what flags)) :=
  observed _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (requireDrainedPrefix_erases what flags)) (OccurrenceDeferred.drained what flags)

theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves Inv (fun _=>True) (RxHistory.inject family port msg tos ll dest) := by
  rw [TrafficSource.inject_factor]
  exact TrafficSource.inject_preserves (I:=Inv)
    (fun _ _ _=>True.intro) (fun _ _ _ eq hi=>product_store eq hi) _ _ _
    receive_observed OccurrenceDeferred.crypt drained_observed family port msg tos ll dest

theorem afterBatch : PrefixPreserves Inv (fun _=>True) RxHistory.afterBatch := by
  rw [TrafficSource.afterBatch_factor]
  exact TrafficSource.afterBatch_preserves (I:=Inv)
    (fun _ _ _=>True.intro) (fun _ _ _ eq hi=>product_store eq hi) _ _ _ _ _
    OccurrenceDeferred.crypt OccurrenceDeferred.send OccurrenceDeferred.atoms.sendOne OccurrenceDeferred.schedule_observed drained_observed

theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    PrefixPreserves Inv (fun _=>True) (RxHistory.flood count port family messages) := by
  rw [TrafficSource.flood_factor]
  exact TrafficSource.flood_preserves (I:=Inv)
    (fun _ _ _=>True.intro) (fun _ _ _ eq hi=>product_store eq hi) _ _ _ _
    receive_observed (OccurrenceNapi.inline_observed [] []) afterBatch drained_observed count port family messages

theorem batch (items : List BatchItem) :
    PrefixPreserves Inv (fun _=>True) (RxHistory.batch items) := by
  rw [TrafficSource.batch_factor]
  exact TrafficSource.batch_preserves (I:=Inv)
    (fun _ _ _=>True.intro) (fun _ _ _ eq hi=>product_store eq hi) _ _ batch_item afterBatch items

theorem inject_native (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Preserves (fun w : World=>Ready [] [] w.wg) (Env.inject family port msg tos ll dest) :=
  native _ _ (RxHistory.inject_erases family port msg tos ll dest) (inject family port msg tos ll dest)

theorem afterBatch_native : Preserves (fun w : World=>Ready [] [] w.wg) Env.afterBatch :=
  native _ _ RxHistory.afterBatch_erases afterBatch

theorem flood_native (count port family : Nat) (messages : List (List UInt8)) :
    Preserves (fun w : World=>Ready [] [] w.wg) (Env.flood count port family messages) :=
  native _ _ (RxHistory.flood_erases count port family messages) (flood count port family messages)

theorem batch_native (items : List BatchItem) :
    Preserves (fun w : World=>Ready [] [] w.wg) (Env.batch items) :=
  native _ _ (RxHistory.batch_erases items) (batch items)


end Leanux.Proofs.WG.RetirementSecurity.OccurrenceTraffic
