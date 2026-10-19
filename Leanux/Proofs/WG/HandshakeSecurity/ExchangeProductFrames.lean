import Leanux.Proofs.WG.HandshakeSecurity.ExchangeData

/-! Product-state transport of the exchange ledger. Native frame obligations
inspect only the optional nonzero handshake tags of the WireGuard projection. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

abbrev ProductInv (h : List Event) (w : World) : Prop := StateInv h w.wg
abbrev ProductPreserves (g : PrefixM Event α) : Prop := PrefixPreserves ProductInv Safe g

theorem product_lift (action : Leanux.M α)
    (keeps : ∀ h, Framing.Preserves (ProductInv h) action) : ProductPreserves (liftPrefix action) :=
  (PrefixEnsures.lift action (fun _ _ hi => hi.safe)
    (fun h w value v hi run => (hoare_iff_run _ _ _).mp (keeps h) w value v hi run)).preserves

theorem product_native (action : WG.M α)
    (keeps : ∀ h, Framing.Preserves (StateInv h) action) :
    ProductPreserves (liftPrefix (liftWG action)) :=
  product_lift _ (fun h => PublicationPoll.native_product _ _ (keeps h))

theorem product_state {action : WGPrefix Event α} (keeps : Preserves action) :
    ProductPreserves (liftWGObserver action) := keeps.liftWGObserver

theorem product_ambient (action : AmbientM α) :
    ProductPreserves (liftPrefix (monadLift action : Leanux.M α)) :=
  product_lift _ (fun _ => productAmbient_spec action _ (fun _ _ hi => hi))

theorem product_pure (value : α) : ProductPreserves (Pure.pure value) :=
  PrefixPreserves.pure (fun _ _ hi => hi.safe) value

theorem product_stable (h : List Event) (w v : World)
    (same : productStoreView v = productStoreView w) (hi : ProductInv h w) : ProductInv h v := by
  apply retained hi
  have tags := congrArg (fun s : ProductStore43 => fun pid : PeerId =>
    (s.2.2.2.dev.bind fun d => d.peers[pid]?).map Peer.handshakeState) same
  intro pid tag found _
  exact (congrFun tags pid).symm.trans found

theorem product_store (action : Leanux.M α) (same : SameProductStore action) :
    ProductPreserves (liftPrefix action) := by
  apply product_lift
  intro h
  apply (hoare_iff_run _ _ _).mpr
  intro w value v hi run
  exact product_stable h w v ((ProjectedAction.iff_run _ _ _).mp same w value v run) hi

theorem product_frame (action : Leanux.M α)
    (retention : ∀ w value v, action.run w = .ok (value,v) → Retains w.wg v.wg) :
    ProductPreserves (liftPrefix action) := by
  apply product_lift
  intro h
  apply (hoare_iff_run _ _ _).mpr
  intro w value v hi run
  exact retained hi (retention w value v run)

theorem frame_product (h : List Event) (action : Leanux.M α)
    (retention : ∀ w value v, action.run w = .ok (value,v) → Retains w.wg v.wg) :
    Framing.Preserves (ProductInv h) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w value v hi run
  exact retained hi (retention w value v run)

theorem skb_frame (h : List Event) (action : SkbM α) :
    Framing.Preserves (StateInv h) (liftSkb action) := by
  apply frame_tag h _
  intro initial
  apply hoare_liftSkb
  intro w d store before device
  change (fun pid : PeerId => (some d |>.bind fun dev => dev.peers[pid]?).map Peer.handshakeState) = initial
  funext pid
  simpa only [handshakeTagAt,device] using congrFun before pid

theorem product_stop (stop : Stop) : ProductPreserves (liftPrefix (throw stop : Leanux.M α)) := by
  apply product_lift
  intro h
  apply (hoare_iff_run _ _ _).mpr
  intro w value v hi run
  cases run

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
