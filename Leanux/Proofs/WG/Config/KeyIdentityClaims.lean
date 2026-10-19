import Leanux.Proofs.WG.Config.KeyIdentityEffects
import Leanux.Proofs.WG.Config.KeyStageEntryClaims
import Leanux.Proofs.WG.Config.RequestMetadataClaims

/-! Final identity after arbitrary later peer attributes on the same normal request. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise TimerDiscipline
namespace KeyStage
theorem certificate_final_identity (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (result : RequestOrder.Inspection)
    (certificate : RequestOrder.Certificate attrs initial result)
    (pre : OwnerConfiguration.ProjectedEntry cs loans initial)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (r : RequestOrder.Receipt) (member : r∈result.receipts) (kind : r.kind=.keyStage) :
    ∃ before after, r.before.wg.device=some before ∧ final.wg.device=some after ∧
      IdentityEffect attrs before after.staticIdentity := by
  obtain ⟨_,_,_,before,after,device,post,effect⟩:=
    certificate_initial_effects cs loans attrs initial result certificate pre r member kind
  have same:=RequestOrder.certificate_key_final_metadata attrs initial result certificate
    ret final normal r member kind
  unfold getterMetadataObservation at same
  rw [post] at same
  cases present : final.wg.device with
  | none => simp only [present,Option.map_some,Option.map_none] at same; cases same
  | some out =>
    simp only [present,Option.map_some,Option.some.injEq,Prod.mk.injEq] at same
    refine ⟨before,out,device,rfl,?_⟩
    have identity : after.staticIdentity=out.staticIdentity :=
      congrArg (fun header : SendConfiguration=>header.2.2.2.2.1) same.1
    rw [←identity]
    exact effect_identity attrs before after effect


/-- The requested private bytes are stored unchanged only at the exact unchanged-key guard;
otherwise the actual installed private key is clamped. Later peer commands preserve it. -/
theorem certificate_final_private (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (result : RequestOrder.Inspection)
    (certificate : RequestOrder.Certificate attrs initial result)
    (pre : OwnerConfiguration.ProjectedEntry cs loans initial)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (r : RequestOrder.Receipt) (member : r∈result.receipts) (kind : r.kind=.keyStage)
    (key : Key) (given : attrs.privateKey=some key) :
    ∃ before after, r.before.wg.device=some before ∧ final.wg.device=some after ∧
      after.staticIdentity.staticPrivate=
        if before.staticIdentity.staticPrivate=key then key else clamp key := by
  obtain ⟨before,after,device,present,effect⟩:=
    certificate_final_identity cs loans attrs initial result certificate pre ret final normal r member kind
  exact ⟨before,after,device,present,identityEffect_private attrs before _ effect key given⟩

end KeyStage
end Leanux.Proofs.WG.Config

