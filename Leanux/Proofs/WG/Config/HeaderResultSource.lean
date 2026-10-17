import Leanux.Proofs.WG.Config.HeaderPutSource
import Leanux.Proofs.WG.Config.HeaderCutModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

theorem cursorHeaderPrefix_normal (d : Device) (ctx : DumpCtx) (prev : Nat) (skb : NlSkb) :
    Noise.Product.Ensures (cursorHeaderPrefix d ctx prev skb) (fun _ => True)
      (fun out _ => out = (2 + if prev != 0 && prev != d.deviceUpdateGen then 16 else 0,
        if ctx.nextPeer.isNone then deviceFixedAttrs d else [],cursorHeaderSkb d ctx skb)) := by
  rw [cursorHeaderPrefix_factored]
  cases first : ctx.nextPeer.isNone <;> cases identity : d.staticIdentity.hasIdentity
  all_goals simp only [cursorHeaderFactored,cursorHeaderDevice,bind_assoc]
  all_goals repeat first
    | (apply cursorHeaderPut_continue)
    | (apply cursorHeaderBranch_continue)
    | (simp only [first,identity,Bool.false_eq_true,ite_false,ite_true,bind_assoc])
  all_goals intro ambient out after _ run
  all_goals cases run
  all_goals simp [cursorHeaderSkb,deviceFixedAttrs,first,identity]

end Leanux.Proofs.WG.Config
