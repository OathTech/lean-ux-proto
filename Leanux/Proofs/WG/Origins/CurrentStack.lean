import Leanux.Proofs.WG.Origins.CurrentTraffic
import Leanux.Proofs.WG.Origins.CurrentHistory
import Leanux.Proofs.Framing.Stack

/-! Current configured identity through the actual transmit entry and stack
reply paths. Contracts concern normal native or product endpoints; all route,
packet-shape, allocation and final-release Stops remain the source's outcomes. -/
namespace Leanux.Proofs.WG.CurrentStack
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues ConfiguredHandshake CurrentLifecycle CurrentTraffic

private theorem lookupDst_view (family addr : Nat) :
    SameView ConfiguredIdentity.view (lookupDst family addr) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w ambient result v ambient' rfl hr
  change (wgStoreView v).dev.map ConfiguredIdentity.state =
    (wgStoreView w).dev.map ConfiguredIdentity.state
  cases result with
  | none => change wgStoreView v = wgStoreView w at borrowed; rw [borrowed]
  | some pid =>
    obtain ⟨d,p,hd,hp,_,hv⟩ := borrowed
    simp only [hv,hd,Option.map_some]
    exact congrArg some (ConfiguredIdentity.state_peer_same d pid p
      {p with refcount := p.refcount + 1} hp rfl)

private theorem xmitTrim_view (pid : PeerId) :
    SameView ConfiguredIdentity.view (xmitTrim pid) := by
  intro initial
  change Preserves (fun w => ConfiguredIdentity.view w = initial) _
  unfold xmitTrim
  simp (config := {zeta := false}) only [branch,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply list_view_spec ConfiguredIdentity.view (fun s => s = initial)
       intro i b
       change Preserves (fun w => ConfiguredIdentity.view w = initial) _)
    | configured_step initial

private theorem xmitSplice_view (pid : PeerId) (packets : List Packet) :
    SameView ConfiguredIdentity.view (xmitSplice pid packets) := by
  intro initial
  change Preserves (fun w => ConfiguredIdentity.view w = initial) _
  unfold xmitSplice
  repeat' configured_step initial

theorem wgXmit_preserves (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (wgXmit family addr packets mtu) := by
  rw [wgXmitSource_eq]
  unfold wgXmitSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant,skipCutSites,envOk]
  repeat' first
    | (rx_retention_head lookupDst
       exact current_preserves _ (lookupDst_view _ _)
         (Origins.Retaining.of_view (Origins.Retaining.lookupDst_material _ _)) history)
    | (rx_retention_head xmitTrim
       exact current_preserves _ (xmitTrim_view _)
         (Origins.Retaining.of_view (Origins.Retaining.xmitTrim_material _)) history)
    | (rx_retention_head xmitSplice
       exact current_preserves _ (xmitSplice_view _ _)
         (Origins.Retaining.of_view (Origins.Retaining.xmitSplice_material _ _)) history)
    | (rx_retention_head sendStagedPackets; exact sendStagedPackets_preserves _ history)
    | (rx_retention_head loopbackSend
       exact current_preserves _
         (ConfiguredIdentity.sameWG (project := id) (loopbackSend_kernel _ _))
         (Origins.Retaining.of_view (Origins.sameView_of_sameWG (project := id)
           (loopbackSend_kernel _ _))) history)
    | (allocation_release_lift_from Net.M
       exact hoare_liftRouting _ (Inv history) (fun _ _ hi => hi))
    | current_traffic_step history

private theorem store_preserves {α : Type} (a : Leanux.M α)
    (frame : SameProductStore a) (history : List SessionOrigin.Receipt) :
    Preserves (fun w : World => Inv history w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w value v hi hr
  have store := (ProjectedAction.iff_run _ _ _).mp frame w value v hr
  have dev : v.wg.dev = w.wg.dev :=
    congrArg (fun s : ProductStore43 => s.2.2.2.dev) store
  constructor
  · intro state hs
    exact hi.1 state (by simpa only [ConfiguredIdentity.view,dev] using hs)
  · intro d hd slot key hk valid
    exact hi.2 d (dev.symm.trans hd) slot key hk valid

private theorem routing_product {α : Type} (a : Net.M α)
    (history : List SessionOrigin.Receipt) :
    Preserves (fun w : World => Inv history w.wg) (monadLift a : Leanux.M α) :=
  CurrentHistory.native_product (liftRouting a)
    (fun h => hoare_liftRouting a (Inv h) (fun _ _ hi => hi)) history

private theorem stopped_bind {α : Type} (a : Leanux.M Unit)
    (stopped : ∀ w, ∃ e, a.run w = .error e) (next : Unit → Leanux.M α)
    (P : World → Prop) : Preserves P (a >>= next) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w value v _ hr
  obtain ⟨e,he⟩ := stopped w
  simp only [StateT.run_bind,he] at hr
  cases hr

macro "current_stack_step " history:term : tactic => `(tactic| first
  | (env_bind_head Env.Stack.excluded
     exact stopped_bind _ (stackExcluded_failure _) _ _)
  | (env_bind_head invariant
     exact stopped_bind _ (fun _ => ⟨_,rfl⟩) _ _)
  | (env_bind_head unsupported
     exact stopped_bind _ (fun _ => ⟨_,rfl⟩) _ _)
  | (allocation_release_lift_from Net.M; exact routing_product _ $history)
  | (allocation_release_lift_from AmbientM
     exact productAmbient_spec _ _ (fun _ _ hi => hi))
  | (allocation_release_lift_from WG.M
     apply CurrentHistory.native_product
     intro nativeHistory
     simp only [monadLift_self]
     repeat' first
       | (rx_retention_head wgXmit; exact wgXmit_preserves _ _ _ _ nativeHistory)
       | current_traffic_step nativeHistory)
  | (rx_retention_head getWG; unfold getWG)
  | (rx_retention_head modifyEnv; unfold modifyEnv)
  | (rx_retention_head modify; apply hoare_modify; intro w hi; exact hi)
  | (rx_retention_head Env.Stack.excluded; unfold Env.Stack.excluded unsupported)
  | (rx_retention_head invariant; unfold invariant)
  | (rx_retention_head unsupported; unfold unsupported)
  | (rx_retention_head discard
     apply discard_view_spec id (fun w : World => Inv $history w.wg)
     change Preserves (fun w : World => Inv $history w.wg) _)
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run _ _ _).mpr
     intro w result v hi hr
     cases hr)
  | rx_retention_step)

theorem reply4_preserves (dst : Nat) (bytes : List UInt8)
    (history : List SessionOrigin.Receipt) :
    Preserves (fun w : World => Inv history w.wg) (Env.Stack.reply4 dst bytes) := by
  unfold Env.Stack.reply4
  simp (config := {zeta := false}) only [skipCut]
  repeat' current_stack_step history

theorem receive4_preserves (bytes : List UInt8) (history : List SessionOrigin.Receipt) :
    Preserves (fun w : World => Inv history w.wg) (Env.Stack.receive4 bytes) := by
  unfold Env.Stack.receive4
  repeat' first
    | (rx_retention_head Env.Stack.reply4; exact reply4_preserves _ _ history)
    | current_stack_step history

theorem receive6_preserves (bytes : List UInt8) (history : List SessionOrigin.Receipt) :
    Preserves (fun w : World => Inv history w.wg) (Env.Stack.receive6 bytes) :=
  store_preserves _ (stackReceive6_sameKernel bytes) history

theorem receive_preserves (bytes : List UInt8) (history : List SessionOrigin.Receipt) :
    Preserves (fun w : World => Inv history w.wg) (Env.Stack.receive bytes) := by
  unfold Env.Stack.receive
  repeat' first
    | (rx_retention_head Env.Stack.receive4; exact receive4_preserves _ history)
    | (rx_retention_head Env.Stack.receive6; exact receive6_preserves _ history)
    | current_stack_step history

theorem deliverInner_preserves (bytes : List UInt8) (history : List SessionOrigin.Receipt) :
    Preserves (fun w : World => Inv history w.wg) (Env.deliverInner bytes) :=
  receive_preserves bytes history

theorem stackForM_preserves (packets : List (List UInt8)) (history : List SessionOrigin.Receipt) :
    Preserves (fun w : World => Inv history w.wg) (packets.forM Env.deliverInner) := by
  induction packets with
  | nil => exact preserves_pure _
  | cons p ps ih =>
    simp only [List.forM_eq_forM,List.forM_cons]
    exact preserves_bind (deliverInner_preserves p history) (fun _ => ih)

end Leanux.Proofs.WG.CurrentStack
