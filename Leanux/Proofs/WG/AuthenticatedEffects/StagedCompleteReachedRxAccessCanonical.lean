import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteIngressFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRxAccessFrames

/-! Literal RX getter and setter calls use packet-store adapter points. Other leaves are atomic world accesses or Ambient computations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RxAccess
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

open Lean Meta Elab Tactic in
elab "rx_access_head " expected:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Shape do throwError "not an RX access shape"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  let name ← realizeGlobalConstNoOverloadWithInfo expected
  unless action.getAppFn.constName? == some name do throwError "different native source head"

macro "rx_access_source_step" : tactic => `(tactic| first
  | (rx_access_head setRxSkb; apply Shape.skb; exact CompleteDecrypt.set_rx _ _)
  | (rx_access_head getRxSkb; apply Shape.skb; exact CompletePollNative.get_rx _)
  | exact Shape.access (.pure _)
  | exact Shape.access .read
  | exact Shape.access (.ambient _)
  | (rx_access_head modifyDev; apply Shape.access; apply Access.Shape.write; apply ReceiveFrames.device <;> intro d <;> rfl)
  | apply Shape.bind
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RxAccess
