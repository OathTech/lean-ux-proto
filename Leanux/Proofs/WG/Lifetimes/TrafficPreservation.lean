import Leanux.Proofs.WG.Lifetimes.TrafficSource
import Leanux.Proofs.WG.Queues.PollPreservation
import Leanux.Proofs.Framing.EnvOperations

/-! Invariants pass through the actual traffic wrappers. Their product
callbacks remain arbitrary; raw source leaves use existing store frames. -/
namespace Leanux.Proofs.WG.Lifetimes.TrafficSource
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues RxJoint.PollSource

variable {E : Type} {I : List E → World → Prop} {S : List E → Prop}

private theorem raw (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (a : Leanux.M α) (frame : SameProductStore a) : PrefixPreserves I S (liftPrefix a) :=
  viewLiftPrefix_preserves productStoreView safe store frame

macro "traffic_preserve_source " safe:term:max " using " store:term:max : tactic => `(tactic| first
  | (traffic_head runWorkerPrefix; apply runWorkerPrefix_preserves $safe $store)
  | (traffic_head getWG; exact raw $safe $store _ (fun initial => productGetWG_spec (fun s => s = initial)))
  | (traffic_head getDev; exact raw $safe $store _ (liftWG_sameProductStore _ getDev_sameWGStore))
  | (traffic_head getEnv
     exact raw $safe $store _ (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v hr; cases hr; rfl))
  | (traffic_head getRouting
     exact raw $safe $store _ (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v hr; cases hr; rfl))
  | (traffic_head requireNotPending; exact raw $safe $store _ (liftWG_sameProductStore _ (SameView.pure _ _)))
  | (traffic_head senderSource; exact raw $safe $store _ (senderSource_sameKernel _ _ _ _))
  | (traffic_head deliverSent; exact raw $safe $store _ deliverSent_sameKernel)
  | (traffic_head peekNextSite; exact raw $safe $store _ peekNextSite_sameKernel)
  | (traffic_head modifyWG; exact raw $safe $store _ (fun initial => productModifyWG_spec (fun s => s = initial) _ (fun _ => rfl)))
  | (traffic_head liftM; exact raw $safe $store _ (fun initial => productRouting_spec _ (fun s => s = initial)))
  | (traffic_head Net.Fib.inSocketNs; exact raw $safe $store _ (fun initial => productRouting_spec _ (fun s => s = initial)))
  | (traffic_head liftPrefix
     apply raw $safe $store
     simp only [getAmbient,recordBudget,modifyAmbient,fixtureSend,invariant,unsupported]
     intro initial
     exact productAmbient_spec _ _ (fun _ _ hi => hi))
  | (poll_preserve_head Pure.pure; exact PrefixPreserves.pure $safe _)
  | (poll_preserve_head Bind.bind; apply PrefixPreserves.bind)
  | (poll_preserve_head ForIn.forIn; first | apply PrefixPreserves.forIn | apply PrefixPreserves.range)
  | (poll_preserve_head ite; apply PrefixPreserves.ite)
  | exact $safe
  | maintenance_intro
  | dsimp only
  | split)

theorem inject_preserves
    (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (receive : List UInt8 → SkbSource → PrefixM E Unit) (crypt : PrefixM E Unit)
    (drained : String → List Bool → PrefixM E Unit)
    (hr : ∀ msg src, PrefixPreserves I S (receive msg src)) (hc : PrefixPreserves I S crypt)
    (hd : ∀ what flags, PrefixPreserves I S (drained what flags))
    (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves I S (injectWith receive crypt drained family port msg tos ll dest) := by
  unfold injectWith
  repeat' first
    | (poll_preserve_head receive; exact hr _ _)
    | (poll_preserve_head crypt; exact hc)
    | (poll_preserve_head drained; exact hd _ _)
    | traffic_preserve_source safe using store

theorem afterBatch_preserves
    (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (crypt send sendOne : PrefixM E Unit) (schedule : Option Worker → PrefixM E Unit)
    (drained : String → List Bool → PrefixM E Unit)
    (hc : PrefixPreserves I S crypt) (hs : PrefixPreserves I S send) (ho : PrefixPreserves I S sendOne)
    (hsch : ∀ stack, PrefixPreserves I S (schedule stack))
    (hd : ∀ what flags, PrefixPreserves I S (drained what flags)) :
    PrefixPreserves I S (afterBatchWith crypt send sendOne schedule drained) := by
  unfold afterBatchWith
  repeat' first
    | (poll_preserve_head crypt; exact hc)
    | (poll_preserve_head send; exact hs)
    | (poll_preserve_head sendOne; exact ho)
    | (poll_preserve_head schedule; exact hsch _)
    | (poll_preserve_head drained; exact hd _ _)
    | traffic_preserve_source safe using store

theorem flood_preserves
    (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (receive : List UInt8 → SkbSource → PrefixM E Unit) (poll after : PrefixM E Unit)
    (drained : String → List Bool → PrefixM E Unit)
    (hr : ∀ msg src, PrefixPreserves I S (receive msg src))
    (hp : PrefixPreserves I S poll) (ha : PrefixPreserves I S after)
    (hd : ∀ what flags, PrefixPreserves I S (drained what flags))
    (count port family : Nat) (messages : List (List UInt8)) :
    PrefixPreserves I S (floodWith receive poll after drained count port family messages) := by
  unfold floodWith
  repeat' first
    | (poll_preserve_head receive; exact hr _ _)
    | (poll_preserve_head poll; exact hp)
    | (poll_preserve_head after; exact ha)
    | (poll_preserve_head drained; exact hd _ _)
    | traffic_preserve_source safe using store

theorem batch_preserves
    (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (one : Device → List Int → BatchItem → PrefixM E (ForInStep (List Int))) (after : PrefixM E Unit)
    (ho : ∀ d cqes item, PrefixPreserves I S (one d cqes item)) (ha : PrefixPreserves I S after)
    (items : List BatchItem) : PrefixPreserves I S (batchWith one after items) := by
  unfold batchWith
  repeat' first
    | (poll_preserve_head one; exact ho _ _ _)
    | (poll_preserve_head after; exact ha)
    | traffic_preserve_source safe using store

end Leanux.Proofs.WG.Lifetimes.TrafficSource
