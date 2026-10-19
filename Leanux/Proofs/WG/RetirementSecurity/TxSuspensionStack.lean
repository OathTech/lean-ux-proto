import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionPoll

/-! Actual GRO stack delivery preserves suspended TX actors, including the
routed reply that re-enters original transmit. All ambient source effects have
individual frames; the fixed-actor service theorem is composed separately. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem route_input (src dst : Nat) : Keeps (Net.routeInput4 src dst) := by
  suspension_source [Net.routeInput4] using [table_lookup,inet_lookup]

theorem environment_modify (f : EnvWorld→EnvWorld) : SameView suspended (modifyEnv f) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run
  rfl

theorem world_wg : SameView suspended (getWG : Leanux.M WGWorld) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run
  rfl

theorem stack_reply (dst : Nat) (bytes : List UInt8) : SameView suspended (Env.Stack.reply4 dst bytes) := by
  intro initial
  let P:=fun w=>suspended w=initial
  have cut (sites : List HiddenSite) : Preserves P (skipCut sites : Leanux.M Unit) :=
    product_ambient (cut_ambient sites) initial
  have routing (src dst : Nat) : Preserves P (monadLift (Net.routeOutput4 src dst) : Leanux.M (Except Int Route)) :=
    product (route_output_call src dst) initial
  have neighbour (dev : Nat) : Preserves P (monadLift (Net.neighbourClassify dev) : Leanux.M Unit) :=
    product (neighbour_call dev) initial
  have send (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
      Preserves P (monadLift (wgXmit family addr packets mtu) : Leanux.M Int) := product (transmit family addr packets mtu) initial
  have read:Preserves P (monadLift getDev : Leanux.M Device) := product device initial
  have stopped {α : Type} (why : String) : Preserves P (Leanux.unsupported why : Leanux.M α) :=
    product_unsupported why initial
  change Preserves P _
  routing_tx_source [Env.Stack.reply4] using [cut,routing,neighbour,send,read,stopped]
  all_goals first
    | (rx_stack_lift_source Net.routeOutput4; exact routing _ _)
    | (rx_stack_lift_source Net.neighbourClassify; exact neighbour _)
    | (rx_stack_lift_source wgXmit; exact send _ _ _ _)
    | (rx_stack_lift_source getDev; exact read)

theorem stack_receive4 (bytes : List UInt8) : SameView suspended (Env.Stack.receive4 bytes) := by
  intro initial
  let P:=fun w=>suspended w=initial
  have route (src dst : Nat) : Preserves P (monadLift (Net.routeInput4 src dst) : Leanux.M Net.InputVerdict) :=
    product (routing_call (route_input src dst)) initial
  have read:Preserves P getWG := world_wg initial
  have write (f : EnvWorld→EnvWorld) : Preserves P (modifyEnv f) := environment_modify f initial
  have reply (dst : Nat) (packet : List UInt8) : Preserves P (Env.Stack.reply4 dst packet) := stack_reply dst packet initial
  have stopped {α : Type} (why : String) : Preserves P (Leanux.unsupported why : Leanux.M α) :=
    product_unsupported why initial
  have failed {α : Type} (why : String) : Preserves P (Leanux.invariant why : Leanux.M α) :=
    product_invariant why initial
  change Preserves P _
  routing_tx_source [Env.Stack.receive4,Env.Stack.excluded] using [route,read,write,reply,stopped,failed]
  all_goals (rx_stack_lift_source Net.routeInput4; exact route _ _)

theorem stack_receive6 (bytes : List UInt8) : SameView suspended (Env.Stack.receive6 bytes) := by
  intro initial
  let P:=fun w=>suspended w=initial
  have read:Preserves P getWG := world_wg initial
  have write (f : EnvWorld→EnvWorld) : Preserves P (modifyEnv f) := environment_modify f initial
  have stopped {α : Type} (why : String) : Preserves P (Leanux.unsupported why : Leanux.M α) :=
    product_unsupported why initial
  have failed {α : Type} (why : String) : Preserves P (Leanux.invariant why : Leanux.M α) :=
    product_invariant why initial
  change Preserves P _
  routing_tx_source [Env.Stack.receive6,Env.Stack.excluded] using [read,write,stopped,failed]

theorem stack_receive (bytes : List UInt8) : SameView suspended (Env.Stack.receive bytes) := by
  intro initial
  let P:=fun w=>suspended w=initial
  have v4:Preserves P (Env.Stack.receive4 bytes) := stack_receive4 bytes initial
  have v6:Preserves P (Env.Stack.receive6 bytes) := stack_receive6 bytes initial
  have failed {α : Type} (why : String) : Preserves P (Leanux.invariant why : Leanux.M α) :=
    product_invariant why initial
  change Preserves P _
  routing_tx_source [Env.Stack.receive] using [v4,v6,failed]

theorem stack_deliver (packets : List (List UInt8)) : SameView suspended (packets.forM Env.deliverInner) := by
  induction packets with
  | nil=>exact SameView.pure _ _
  | cons bytes rest ih=>
    simp only [List.forM_eq_forM,List.forM_cons,Env.deliverInner]
    exact (stack_receive bytes).bind (fun _=>ih)

theorem stack_poll (pid budget : Nat) :
    SameView suspended (rxPoll pid budget (fun packets=>packets.forM Env.deliverInner)) :=
  rx_poll pid budget _ stack_deliver

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension
