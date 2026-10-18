import Leanux.Proofs.WG.Index.ReachedTrafficAuxSource
import Leanux.Proofs.WG.Index.ReceiveIngressCoreSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReachedTraffic
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem front_core {α β : Type} (loans : Reservations)
    (front : RxHistory.Obs α) (tail : α→RxHistory.Obs β)
    (store : ∀ w h x v k,runPrefix front w h=(.ok (x,v),k)→productStoreView v=productStoreView w)
    (present : ∀ w h x v k,runPrefix front w h=(.ok (x,v),k)→v.wg.dev.isSome=true)
    (history : ∀ w h,(runPrefix front w h).2=h)
    (keeps : ∀x,PrefixPreserves (Reached.AnyAux loans) OwnerChecks.Safe (tail x))
    {cs : Ledger} {w v : World} {h k : List RxHistory.Event} {result : β}
    (pre : Reached.Entry cs loans h w)
    (run : runPrefix (front >>= tail) w h=(.ok (result,v),k)) : Reached.Core v.wg := by
  obtain ⟨x,u,j,start,finish⟩ := DecryptIteration.bind_normal run
  have same : j=h := by simpa only [start] using history w h
  subst j
  have atCut := Reached.entry_to_aux (Reached.entry_store (store w h x u h start) pre)
    (present w h x u h start)
  have post := (keeps x u h ⟨cs,atCut⟩).choose_spec.2.2
  rw [finish] at post
  obtain ⟨_,post⟩ := post
  exact post.2.2

theorem inject_core (loans : Reservations) (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat)
    {cs : Ledger} {w v : World} {h k : List RxHistory.Event} {result : Int}
    (pre : Reached.Entry cs loans h w)
    (run : runPrefix (RxHistory.inject family port msg tos ll dest) w h=(.ok (result,v),k)) :
    Reached.Core v.wg := by
  rw [InjectAccount.source_factor] at run
  apply front_core loans _ _
    (fun _ _ _ _ _=>InjectAccount.front_store)
    (fun _ _ _ _ _=>InjectAccount.front_present)
    (InjectAccount.front_history (family:=family) (port:=port) (tos:=tos) (ll:=ll) (dest:=dest))
    _ pre run
  intro src
  exact (runWorkerPrefix_preserves (any_safe loans) (any_product_store loans) .netRx
    (ReceiveIngressCore.receive_any loans msg src)).bind (fun _=>inject_finish loans msg)

theorem flood_loop (loans : Reservations) (family : Nat) (src : SkbSource)
    (messages : List (List UInt8)) :
    PrefixPreserves (Reached.AnyAux loans) OwnerChecks.Safe (FloodLoop.loop family src messages) := by
  have one (msg : List UInt8) :
      PrefixPreserves (Reached.AnyAux loans) OwnerChecks.Safe (FloodLoop.one family src msg) := by
    unfold FloodLoop.one
    apply PrefixPreserves.bind
    · unfold FloodLoop.route
      repeat' traffic_preserve_source (any_safe loans) using (any_product_store loans)
    · intro _
      unfold FloodSection.action
      exact runWorkerPrefix_preserves (any_safe loans) (any_product_store loans) .netRx
        ((ReceiveIngressCore.receive_any loans msg src).bind (fun _=>any_fixed loans _
          (fun cs before=>inline_aux cs loans before)))
  induction messages with
  | nil=>exact PrefixPreserves.pure (any_safe loans) _
  | cons msg rest ih=>
    rw [FloodLoop.loop_cons]
    exact (one msg).bind (fun _=>ih)

theorem flood_core (loans : Reservations) (count port family : Nat)
    (messages : List (List UInt8))
    {cs : Ledger} {w v : World} {h k : List RxHistory.Event} {result : Int}
    (pre : Reached.Entry cs loans h w)
    (run : runPrefix (RxHistory.flood count port family messages) w h=(.ok (result,v),k)) :
    Reached.Core v.wg := by
  rw [FloodAccount.source_factor] at run
  apply front_core loans _ _
    (fun _ _ _ _ _=>FloodAccount.front_store)
    (fun _ _ _ _ _=>FloodAccount.front_present)
    (FloodAccount.front_history (family:=family) (port:=port)) _ pre run
  intro src
  exact (flood_loop loans family src _).bind (fun _=>flood_finish loans)

theorem batch_item (loans : Reservations) (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    PrefixPreserves (Reached.AnyAux loans) OwnerChecks.Safe (RxHistory.batchItem d cqes item) := by
  rw [AdmissionSection.batchItem_source]
  exact batchItemWith_preserves (any_safe loans) (any_wg_store loans) _ _ _ _
    (ReceiveIngressCore.receive_any loans) (any_fixed loans _ (fun cs before=>inline_aux cs loans before))
    (fun family addr=>any_fixed loans _ (fun cs before=>multicast_aux cs loans before family addr))
    (fun family addr packets mtu=>any_fixed loans _
      (fun cs before=>transmit_aux cs loans before family addr packets mtu)) d cqes item

theorem batch_core (loans : Reservations) (items : List Env.BatchItem)
    {cs : Ledger} {w v : World} {h k : List RxHistory.Event} {result : Int}
    (pre : Reached.Entry cs loans h w)
    (run : runPrefix (RxHistory.batch items) w h=(.ok (result,v),k)) :
    Reached.Core v.wg := by
  rw [BatchAccount.source_factor] at run
  apply front_core loans _ _
    (fun _ _ _ _ _=>BatchAccount.front_store)
    (fun _ _ _ _ _=>BatchAccount.front_present)
    BatchAccount.front_history _ pre run
  intro d
  apply PrefixPreserves.bind
  · unfold BatchAccount.loop
    exact PrefixPreserves.forIn _ _ _ (any_safe loans) (fun item cqes=>batch_item loans d cqes item)
  · intro cqes
    exact batch_finish loans items cqes

theorem traffic_entry {α : Type} (action : RxHistory.Obs α)
    (owner : OwnerChecks.Preserves action)
    (normal : ∀cs w h,Reached.Entry cs [] h w→∀result v k,
      runPrefix action w h=(.ok (result,v),k)→∃next,Reached.Entry next [] k v) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe action := by
  intro w h pre
  obtain ⟨cs,pre⟩ := pre
  obtain ⟨suffix,history,safe,_⟩ := owner w h pre.1.2
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix action w h).1 with
  | error stop=>trivial
  | ok out=>exact normal cs w h pre out.1 out.2 _ (Prod.ext run rfl)

theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.inject family port msg tos ll dest) := by
  apply traffic_entry _ (OwnerTraffic.inject family port msg tos ll dest)
  intro cs w h pre result v k run
  obtain ⟨_,_,account,_,_⟩ := HolderTrafficEntry.inject_normal pre.1 run
  exact ⟨[],account,inject_core [] family port msg tos ll dest pre run⟩

theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.flood count port family messages) := by
  apply traffic_entry _ (OwnerTraffic.flood count port family messages)
  intro cs w h pre result v k run
  obtain ⟨next,_,account⟩ := HolderTrafficEntry.flood_normal pre.1 run
  exact ⟨next,account,flood_core [] count port family messages pre run⟩

theorem batch (items : List Env.BatchItem) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.batch items) := by
  apply traffic_entry _ (OwnerTraffic.batch items)
  intro cs w h pre result v k run
  obtain ⟨next,_,account⟩ := HolderTrafficEntry.batch_normal items pre.1 run
  exact ⟨next,account,batch_core [] items pre run⟩

end Leanux.Proofs.WG.Index.ReachedTraffic
