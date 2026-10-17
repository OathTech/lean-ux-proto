import Leanux.Proofs.WG.Config.HeaderResultSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

theorem cursorHeader_normal (d : Device) (ctx : DumpCtx) (prev : Nat)
    (skb : NlSkb) (finish : Nat → List (String × Json) → NlSkb → WG.M DumpCall)
    (P : WGWorld → Prop) (Q : DumpCall → WGWorld → Prop)
    (tail : Ensures (finish (2 + if prev != 0 && prev != d.deviceUpdateGen then 16 else 0)
      (if ctx.nextPeer.isNone then deviceFixedAttrs d else []) (cursorHeaderSkb d ctx skb)) P Q) :
    Ensures (socketDumpHeaderSource d ctx prev skb finish) P Q := by
  intro g ambient result final after pre run
  rw [cursorHeader_source] at run
  change (((StateT.lift (cursorHeaderPrefix d ctx prev skb) >>= fun (flags,attrs,out) =>
    finish flags attrs out).run g).run ambient) = Except.ok ((result,final),after) at run
  simp only [StateT.run_bind,StateT.run_lift,bind_assoc,pure_bind] at run
  cases outcome : (cursorHeaderPrefix d ctx prev skb).run ambient with
  | error err => rw [outcome] at run; cases run
  | ok value =>
    rcases value with ⟨header,remaining⟩
    have valueEq := cursorHeaderPrefix_normal d ctx prev skb ambient header remaining trivial outcome
    subst header
    have okBind {α β : Type} (x : α) (f : α → Except Stop β) :
        (Except.ok x >>= f) = f x := rfl
    exact tail g remaining result final after pre (by simpa only [outcome,okBind] using run)

end Leanux.Proofs.WG.Config
