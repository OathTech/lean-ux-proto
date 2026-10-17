import Leanux.Proofs.WG.Queues.TxLiveIngress
import Leanux.Proofs.WG.Queues.InjectAccount
import Leanux.Proofs.WG.Queues.BatchAccount
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation

/-! Concrete traffic source sections preserve the live TX frontier through
actual ingress, inline NAPI and outbound batch items. The enclosing crypt and
post-batch waits are separate calls; no whole-caller frame is assumed here. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveTraffic
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open LiveFrontier RxCredits

theorem wg_store {w v : World} (same : wgStoreView v.wg=wgStoreView w.wg)
    (hi : Ready w.wg) : Ready v.wg :=
  ready_fields hi (congrArg (fun s : WGStoreView=>s.dev.map (fun d=>(d.nextSkb,d.encryptQueue))) same)

theorem product_store {w v : World} (same : productStoreView v=productStoreView w)
    (hi : Ready w.wg) : Ready v.wg :=
  wg_store (congrArg (fun s : ProductStore43=>s.2.2.2) same) hi

theorem observed {E α : Type} (g : PrefixM E α) (a : Leanux.M α)
    (appends : Appends g) (erases : ErasesPrefix g a)
    (keeps : Preserves (fun w : World=>Ready w.wg) a) :
    PrefixPreserves (fun _ w=>Ready w.wg) (fun _=>True) g :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveNapi.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveNapi.observed)
    g a appends erases keeps

theorem native {E α : Type} (g : PrefixM E α) (a : Leanux.M α)
    (erases : ErasesPrefix g a)
    (keeps : PrefixPreserves (fun _ w=>Ready w.wg) (fun _=>True) g) :
    Preserves (fun w : World=>Ready w.wg) a :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveStack.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.native_of_source)
    g a erases keeps

theorem transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    PrefixPreserves (fun _ w=>Ready w.wg) (fun _=>True)
      (RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu))) :=
  observed _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases (wgXmitPrefix_erases family addr packets mtu)))
    (PublicationPoll.native_product Ready _ (LiveFrontier.transmit family addr packets mtu))

theorem multicast (family addr : Nat) :
    PrefixPreserves (fun _ w=>Ready w.wg) (fun _=>True)
      (RxHistory.audit (xmitMulticastLoopAudit family addr)) := by
  apply observed _ _ (Appends.focus _ _ _)
    (RxHistory.audit_erases (xmitMulticastLoopAudit_erases family addr))
  have frame := (pinned_const _private.Leanux.Proofs.WG.Queues.BatchAccount.«0».Leanux.Proofs.WG.Queues.RxCredits.BatchAccount.multicast_store) family addr
  exact frame.wp (fun s : ProductStore43=>Ready {dev:=s.2.2.2.dev})

theorem batch_item (d : Device) (cqes : List Int) (item : BatchItem) :
    PrefixPreserves (fun _ w=>Ready w.wg) (fun _=>True) (RxHistory.batchItem d cqes item) := by
  rw [rxBatchItem_factor]
  exact batchItemWith_preserves (fun _ _ _=>True.intro) (fun _ _ _ eq hi=>wg_store eq hi)
    _ _ _ _ LiveIngress.receive_observed LiveNapi.inline_observed multicast transmit d cqes item

theorem batch_loop (d : Device) (items : List BatchItem) (cqes : List Int) :
    PrefixPreserves (fun _ w=>Ready w.wg) (fun _=>True) (BatchAccount.loop d items cqes) := by
  unfold BatchAccount.loop
  apply PrefixPreserves.forIn
  · exact fun _ _ _=>True.intro
  · intro item qs
    exact batch_item d qs item

theorem receive_section (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves (fun _ w=>Ready w.wg) (fun _=>True) (FloodSection.action msg src) := by
  unfold FloodSection.action AdmissionCaller.receive
  apply runWorkerPrefix_preserves (fun _ _ _=>True.intro) (fun _ _ _ eq hi=>product_store eq hi)
  exact PrefixPreserves.bind (LiveIngress.receive_observed msg src) (fun _=>LiveNapi.inline_observed)

theorem flood_route (family : Nat) (src : SkbSource) :
    PrefixPreserves (fun _ w=>Ready w.wg) (fun _=>True) (FloodLoop.route family src) := by
  have safe : ∀ h w,(fun (_ : List RxHistory.Event) (w : World)=>Ready w.wg) h w→True := fun _ _ _=>True.intro
  have store : ∀ (h : List RxHistory.Event) w v,productStoreView v=productStoreView w→Ready w.wg→Ready v.wg := fun _ _ _ eq hi=>product_store eq hi
  unfold FloodLoop.route
  repeat' traffic_preserve_source safe using store

theorem flood_one (family : Nat) (src : SkbSource) (msg : List UInt8) :
    PrefixPreserves (fun _ w=>Ready w.wg) (fun _=>True) (FloodLoop.one family src msg) :=
  PrefixPreserves.bind (flood_route family src) (fun _=>receive_section msg src)

theorem flood_loop (family : Nat) (src : SkbSource) (messages : List (List UInt8)) :
    PrefixPreserves (fun _ w=>Ready w.wg) (fun _=>True) (FloodLoop.loop family src messages) := by
  induction messages with
  | nil=>exact PrefixPreserves.pure (fun _ _ _=>True.intro) _
  | cons msg messages ih=>
    rw [FloodLoop.loop_cons]
    exact PrefixPreserves.bind (flood_one family src msg) (fun _=>ih)

theorem inject_front (family port tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves (fun _ w=>Ready w.wg) (fun _=>True)
      (InjectAccount.front family port tos ll dest) :=
  InjectAccount.front_preserves (fun _ _ _=>True.intro) (fun _ _ _ eq hi=>product_store eq hi)

end Leanux.Proofs.WG.Queues.TxDisposition.LiveTraffic
