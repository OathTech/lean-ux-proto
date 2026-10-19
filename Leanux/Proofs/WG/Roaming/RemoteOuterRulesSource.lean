import Leanux.Proofs.WG.Queues.JointNetlink

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteOuterRules
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration

theorem socket {E : Type} (I : List E → World → Prop) (S : List E → Prop)
    (safe : ∀ h w, I h w → S h)
    (files : ∀ {α : Type} (action : FS.M α), PrefixPreserves I S (liftPrefix (liftFS action)))
    (fd : Nat) (body : PrefixM E Int) (hb : PrefixPreserves I S body) :
    PrefixPreserves I S (socketCallOnWith (fun {_} a => liftPrefix a) fd body) := by
  unfold socketCallOnWith
  apply PrefixPreserves.bind (files (fdget fd))
  intro f
  apply PrefixPreserves.ite
  · intro _; exact PrefixPreserves.pure safe _
  · intro _
    exact hb.bind (fun ret => (files (fdput f)).bind (fun _ => PrefixPreserves.pure safe ret))

theorem netlink {E : Type} (I : List E → World → Prop) (S : List E → Prop)
    (safe : ∀ h w, I h w → S h)
    (files : ∀ {α : Type} (action : FS.M α), PrefixPreserves I S (liftPrefix (liftFS action)))
    (ambient : ∀ {α : Type} (action : AmbientM α), PrefixPreserves I S (liftPrefix (liftAmbient action)))
    (body : PrefixM E Int) (hb : PrefixPreserves I S body) :
    PrefixPreserves I S (netlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold netlinkRequestWith
  apply PrefixPreserves.bind (socket I S safe files _ _
    ((ambient (AmbientM.skipCut allocCuts)).bind
      (fun _ => hb.bind (fun ret => (ambient (AmbientM.skipCut allocCuts)).bind
        (fun _ => PrefixPreserves.pure safe ret)))))
  intro ret
  exact (socket I S safe files _ _ (PrefixPreserves.pure safe 0)).bind
    (fun _ => PrefixPreserves.pure safe ret)
end Leanux.Proofs.WG.Roaming.RemoteOuterRules
