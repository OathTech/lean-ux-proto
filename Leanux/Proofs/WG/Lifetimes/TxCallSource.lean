import Leanux.Proofs.WG.Queues.JointNetlink

/-! The direct transmit syscall arm shares its actual socket, routing and errno
control flow. Only the multicast and native-TX observers are parameters. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Configuration

/-- The original SENDER_FD wrapper and complete transmit body. Callbacks range
over arbitrary product observers with the selected event type. -/
def syscallXmitWith {E : Type}
    (multicast : Nat → Nat → PrefixM E Unit)
    (xmit : Nat → Nat → List Packet → Nat → PrefixM E Int)
    (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) : PrefixM E Int :=
  socketCallOnWith (fun {_} a => liftPrefix a) SENDER_FD do
    -- W9: the sender's `sendto` routes on the fixture's tables
    -- (`World.route4/6`): into wg0 by the default route the guest adds after
    -- a successful wg_up (and removes with a down, a deletion or
    -- `wg_delroute`), else `-ENETUNREACH`; a local destination never
    -- reaches wg0
    let r ← match ← liftPrefix (Net.routeLookup family 0 addr) with
      | .error err => return err
      | .ok r => pure r
    if r.dev != WG0_IFINDEX then liftPrefix (unsupported "a transmit to a local address (not into wg0)")
    -- W4: an MTU change below the family's floor took its routes down with
    -- its IP device, and the fixture re-adds them only at the next wg_up
    if let some d := (← liftPrefix getWG).dev then
      if (family == 4 && !d.inet4Dev) || (family == 6 && !d.inet6Dev) then
        liftPrefix (unsupported "a transmit after an MTU change took the family's routes into wg0 down")
    -- udp_sendmsg returns the datagram's length once the device took it
    liftPrefix Env.fixtureSend
    let opts := { opts with routeMtu := opts.routeMtu <|> (if r.mtu != 0 then some r.mtu else none) }
    match ← liftPrefix (Env.xmitPackets family addr payload opts) with
    | .error e => return e   -- refused by the sender's IP layer before any output
    | .ok (pkts, mtu) =>
      multicast family addr
      if family == 4 then liftPrefix (Net.neighbourClassify WG0_IFINDEX)
      let ret ← xmit family addr pkts mtu
      return if ret == 0 then payload.length else ret

theorem dispatchAudit_xmit_factor (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    dispatchAudit (.wgXmit family addr payload opts) =
      syscallXmitWith xmitMulticastLoopAudit
        (fun family addr pkts mtu => auditFocus (liftWGObserver (wgXmitPrefix family addr pkts mtu)))
        family addr payload opts := rfl

theorem rxDispatch_xmit_factor (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    Queues.RxHistory.syscallDispatch (.wgXmit family addr payload opts) =
      Queues.RxHistory.audit (syscallXmitWith xmitMulticastLoopAudit
        (fun family addr pkts mtu => auditFocus (liftWGObserver (wgXmitPrefix family addr pkts mtu)))
        family addr payload opts) := rfl

/-- Exact same-result projection of the whole syscall arm, including FD
acquisition/payment and route errors, for arbitrary incoming histories. -/
theorem syscallXmitWith_projects {E F : Type} (ρ : E → Option F)
    (multicast : Nat → Nat → PrefixM E Unit) (multicast' : Nat → Nat → PrefixM F Unit)
    (xmit : Nat → Nat → List Packet → Nat → PrefixM E Int)
    (xmit' : Nat → Nat → List Packet → Nat → PrefixM F Int)
    (hm : ∀ family addr, ProjectsPrefix ρ id (multicast family addr) (multicast' family addr))
    (hx : ∀ family addr pkts mtu, ProjectsPrefix ρ id
      (xmit family addr pkts mtu) (xmit' family addr pkts mtu))
    (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    ProjectsPrefix ρ id (syscallXmitWith multicast xmit family addr payload opts)
      (syscallXmitWith multicast' xmit' family addr payload opts) := by
  unfold syscallXmitWith
  apply socketCallOnWith_projects ρ
  repeat' first
    | with_reducible exact hm _ _
    | with_reducible exact hx _ _ _ _
    | exact projectsPrefix_lift ρ _
    | exact projectsPrefix_pure ρ id _
    | apply projectsPrefix_bind ρ id id
    | apply projectsPrefix_ite
    | maintenance_intro
    | dsimp only [id]
    | split

/-- Only actual callback contracts and stability under the existing WG store
projection are required. Descriptor updates and failed prefixes stay concrete. -/
theorem syscallXmitWith_preserves {E : Type} {I : List E → World → Prop} {S : List E → Prop}
    (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, wgStoreView v.wg = wgStoreView w.wg → I h w → I h v)
    (multicast : Nat → Nat → PrefixM E Unit)
    (xmit : Nat → Nat → List Packet → Nat → PrefixM E Int)
    (hm : ∀ family addr, PrefixPreserves I S (multicast family addr))
    (hx : ∀ family addr pkts mtu, PrefixPreserves I S (xmit family addr pkts mtu))
    (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    PrefixPreserves I S (syscallXmitWith multicast xmit family addr payload opts) := by
  have frame {α : Type} (a : Leanux.M α) (ha : SameProductStore a) :
      PrefixPreserves I S (liftPrefix a) :=
    viewLiftPrefix_preserves (fun w : World => wgStoreView w.wg) safe store
      (ha.of_factor (fun s : ProductStore43 => s.2.2.2) _ (fun _ => rfl))
  have ambient {α : Type} (a : AmbientM α) :
      PrefixPreserves I S (liftPrefix (MonadLift.monadLift a : Leanux.M α)) :=
    viewLiftPrefix_preserves (fun w : World => wgStoreView w.wg) safe store
      (fun initial => productAmbient_spec a (fun w => wgStoreView w.wg = initial) (fun _ _ hi => hi))
  have routing {α : Type} (a : Net.M α) :
      PrefixPreserves I S (liftPrefix (liftWG (liftRouting a))) :=
    frame _ (liftWG_sameProductStore _ (liftRouting_sameWGStore a))
  have fs {α : Type} (a : FS.M α) : PrefixPreserves I S (liftPrefix (liftFS a)) :=
    viewLiftPrefix_preserves (fun w : World => wgStoreView w.wg) safe store
      (fun initial => productFS_spec a (fun w => wgStoreView w.wg = initial) (fun _ _ _ _ hi => hi))
  unfold syscallXmitWith socketCallOnWith
  repeat' first
    | with_reducible exact hm _ _
    | with_reducible exact hx _ _ _ _
    | (traffic_head liftFS; exact fs _)
    | (traffic_head routeLookup; exact routing _)
    | (traffic_head neighbourClassify; exact routing _)
    | (traffic_head getWG; exact frame _ (fun state => productGetWG_spec (fun s => s = state)))
    | (traffic_head xmitPackets; exact frame _ (xmitPackets_sameKernel _ _ _ _))
    | (traffic_head fixtureSend; unfold Env.fixtureSend; exact ambient _)
    | (traffic_head unsupported; exact ambient (AmbientM.unsupported _))
    | with_reducible exact PrefixPreserves.pure safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | maintenance_intro
    | dsimp only
    | split

theorem syscallXmitWith_appends {E : Type}
    (multicast : Nat → Nat → PrefixM E Unit)
    (xmit : Nat → Nat → List Packet → Nat → PrefixM E Int)
    (hm : ∀ family addr, Appends (multicast family addr))
    (hx : ∀ family addr pkts mtu, Appends (xmit family addr pkts mtu))
    (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    Appends (syscallXmitWith multicast xmit family addr payload opts) := by
  have callback {α : Type} (a : PrefixM E α) (ha : Appends a) :
      PrefixPreserves (fun _ _ => True) (fun _ => True) a := by
    intro w h _
    obtain ⟨suffix,hs⟩ := ha w h
    refine ⟨suffix,hs,True.intro,?_⟩
    cases (runPrefix a w h).1 <;> trivial
  have checked := syscallXmitWith_preserves (I := fun _ _ => True) (S := fun _ => True)
    (fun _ _ hi => hi) (fun _ _ _ _ hi => hi) multicast xmit
    (fun family addr => callback _ (hm family addr))
    (fun family addr pkts mtu => callback _ (hx family addr pkts mtu)) family addr payload opts
  intro w h
  obtain ⟨suffix,hs,_,_⟩ := checked w h True.intro
  exact ⟨suffix,hs⟩

end Leanux.Proofs.WG.Lifetimes
