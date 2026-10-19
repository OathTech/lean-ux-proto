import Leanux.Proofs.WG.Index.ReceiveCompletionRulesSource
import Leanux.Proofs.WG.Lifetimes.DeviceXmit
import Leanux.Proofs.Framing.EnvOperations

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.TransmitAmbientRules
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Lifetimes Leanux.Proofs.WG.Index.ReceiveCompletion.Rules
theorem forIn_rule (P : WGWorld→Ambient→Prop) {α β : Type}
    (xs : List α) (initial : β) (step : α→β→WG.M (ForInStep β))
    (each : ∀x b,Keeps P (step x b)) : Keeps P (forIn xs initial step) := by
  induction xs generalizing initial with
  | nil=>exact pure_rule P _
  | cons x xs ih=>
    rw [List.forIn_cons]
    apply bind_rule P _ _ (each x initial)
    intro out
    cases out with
    | done b=>exact pure_rule P b
    | yield b=>exact ih b
theorem ite_rule (P : WGWorld→Ambient→Prop) {α : Type} (p : Prop) [Decidable p]
    (yes no : WG.M α) (hy : Keeps P yes) (hn : Keeps P no) :
    Keeps P (if p then yes else no) := by split <;> assumption
theorem wgXmit_rule (P : WGWorld→Ambient→Prop) (family addr : Nat)
    (packets : List Packet) (mtu : Nat)
    (branches : ∀site value,Keeps P (branch site value : WG.M Bool))
    (lookup : Keeps P (lookupDst family addr))
    (trim : ∀pid,Keeps P (xmitTrim pid))
    (splice : ∀pid packets,Keeps P (xmitSplice pid packets))
    (stage : ∀pid,Keeps P (sendStagedPackets pid))
    (pay : ∀peer,Keeps P (peerPut peer))
    (loopback : ∀sites raised,Keeps P (loopbackSend sites raised))
    (route : ∀src dst,Keeps P (monadLift (Net.routeOutput4 src dst) : WG.M (Except Int Route)))
    (address : ∀dev addr,Keeps P (monadLift (Net.Fib.inetDevAddrType dev addr) : WG.M Net.Fib.RouteType))
    (neighbor : ∀dev,Keeps P (monadLift (Net.neighbourClassify dev) : WG.M Unit))
    (cut : ∀sites,Keeps P (skipCutSites sites : WG.M (List Nat)))
    (env : ∀site,Keeps P (envOk site : WG.M Bool))
    (errors : Keeps P (modifyDev fun d=>{d with txErrors:=d.txErrors+1})) :
    Keeps P (wgXmit family addr packets mtu) := by
  rw [wgXmitSource_eq]
  env_operation_source [wgXmitSource,WG.andM]
    using [branches,lookup,trim,splice,stage,pay,loopback,route,address,neighbor,cut,env,
      errors,getPeer_rule,invariant_rule,pure_rule,bind_rule,forIn_rule,ite_rule]
end Leanux.Proofs.WG.Index.TransmitAmbientRules
