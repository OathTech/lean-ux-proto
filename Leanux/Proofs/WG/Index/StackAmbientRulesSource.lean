import Leanux.Proofs.WG.Noise.PendingStackSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.StackAmbientRules
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.Lifetimes Leanux.Proofs.WG.Noise

theorem lift_rule (P : World→Prop) {α : Type} (action : Leanux.M α)
    (keep : Preserves P action) :
    PrefixPreserves (fun (_ : List Empty)=>P) (fun _=>True) (liftPrefix action) :=
  PrefixEnsures.lift action (fun _ _ _=>True.intro)
    (fun _ w value after pre run=>(hoare_iff_run _ _ _).mp keep w value after pre run)

theorem reply4_rule (P : World→Prop)
    (send : ∀family addr packets mtu,Preserves P (liftWG (wgXmit family addr packets mtu)))
    (cut : ∀sites,Preserves P (skipCut sites : Leanux.M Unit))
    (route : ∀src dst,Preserves P (liftWG (liftRouting (Net.routeOutput4 src dst))))
    (dev : Preserves P (liftWG getDev))
    (neighbor : ∀pid,Preserves P (liftWG (liftRouting (Net.neighbourClassify pid))))
    (dst : Nat) (bytes : List UInt8) :
    PrefixPreserves (fun (_ : List Empty)=>P) (fun _=>True)
      (reply4With PendingStack.transmit dst bytes) := by
  have safe : ∀(_ : List Empty) w,P w→True := fun _ _ _=>True.intro
  have sent family addr packets mtu :
      PrefixPreserves (fun (_ : List Empty)=>P) (fun _=>True)
        (PendingStack.transmit family addr packets mtu) :=
    lift_rule P _ (send family addr packets mtu)
  have cuts sites := lift_rule P _ (cut sites)
  have routes src dst := lift_rule P _ (route src dst)
  have device := lift_rule P _ dev
  have neighbors pid := lift_rule P _ (neighbor pid)
  unfold reply4With
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | with_reducible exact sent _ _ _ _
    | with_reducible exact cuts _
    | with_reducible exact routes _ _
    | with_reducible exact device
    | with_reducible exact neighbors _
    | with_reducible exact PrefixPreserves.lift_failure_bind safe (unsupported _) (fun _=>⟨_,rfl⟩) _
    | with_reducible exact PrefixPreserves.pure safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | maintenance_intro
    | dsimp only
    | split

theorem receive4_rule (P : World→Prop)
    (reply : Nat→List UInt8→PrefixM Empty Unit)
    (replies : ∀dst bytes,PrefixPreserves (fun (_ : List Empty)=>P) (fun _=>True) (reply dst bytes))
    (route : ∀src dst,Preserves P (liftWG (liftRouting (Net.routeInput4 src dst))))
    (read : Preserves P (getWG : Leanux.M WGWorld))
    (write : ∀f,Preserves P (modifyEnv f : Leanux.M Unit))
    (pkt : List UInt8) :
    PrefixPreserves (fun (_ : List Empty)=>P) (fun _=>True) (receive4With reply pkt) := by
  have safe : ∀(_ : List Empty) w,P w→True := fun _ _ _=>True.intro
  have routes src dst := lift_rule P _ (route src dst)
  have reads := lift_rule P _ read
  have writes f := lift_rule P _ (write f)
  unfold receive4With
  repeat' first
    | with_reducible exact replies _ _
    | with_reducible exact routes _ _
    | with_reducible exact reads
    | with_reducible exact writes _
    | with_reducible exact PrefixPreserves.lift_failure_bind safe (Stack.excluded _) (stackExcluded_failure _) _
    | with_reducible exact PrefixPreserves.lift_failure_bind safe (invariant _) (fun _=>⟨_,rfl⟩) _
    | with_reducible exact PrefixPreserves.lift_failure_bind safe (unsupported _) (fun _=>⟨_,rfl⟩) _
    | with_reducible exact PrefixPreserves.pure safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | maintenance_intro
    | dsimp only
    | split

theorem stack_rule (P : World→Prop) (bytes : List UInt8)
    (send : ∀family addr packets mtu,Preserves P (liftWG (wgXmit family addr packets mtu)))
    (cut : ∀sites,Preserves P (skipCut sites : Leanux.M Unit))
    (output : ∀src dst,Preserves P (liftWG (liftRouting (Net.routeOutput4 src dst))))
    (dev : Preserves P (liftWG getDev))
    (neighbor : ∀pid,Preserves P (liftWG (liftRouting (Net.neighbourClassify pid))))
    (input : ∀src dst,Preserves P (liftWG (liftRouting (Net.routeInput4 src dst))))
    (read : Preserves P (getWG : Leanux.M WGWorld))
    (write : ∀f,Preserves P (modifyEnv f : Leanux.M Unit))
    (ipv6 : ∀pkt,Preserves P (Stack.receive6 pkt)) :
    PrefixPreserves (fun (_ : List Empty)=>P) (fun _=>True) (PendingStack.stackSource bytes) := by
  unfold PendingStack.stackSource stackReceiveWith
  dsimp only
  split
  · exact receive4_rule P _ (reply4_rule P send cut output dev neighbor) input read write bytes
  · split
    · exact lift_rule P _ (ipv6 bytes)
    · apply PrefixEnsures.lift (Q:=fun _ (_ : List Empty)=>P) _ (fun _ _ _=>True.intro)
      intro h w value after pre run
      cases run
end Leanux.Proofs.WG.Index.StackAmbientRules
