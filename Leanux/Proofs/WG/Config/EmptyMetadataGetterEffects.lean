import Leanux.Proofs.WG.Config.EmptyMetadataGetterModel
import Leanux.Proofs.WG.Config.MultiPeerGetterClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG TimerDiscipline

theorem sendConfiguration_dump_congr (d out : Device)
    (same : sendConfiguration out = sendConfiguration d) :
    deviceFixedAttrs out = deviceFixedAttrs d ∧
    devicePrefixSpace out = devicePrefixSpace d ∧
    byIndex out = byIndex d ∧
    (∀ sock, socketReadbackFinal sock out = socketReadbackFinal sock d) := by
  simp only [sendConfiguration, Prod.mk.injEq] at same
  obtain ⟨name,index,port,mark,identity,generation⟩ := same
  simp [deviceFixedAttrs,devicePrefixSpace,byIndex,socketReadbackFinal,
    name,index,port,mark,identity,generation]

theorem sendConfiguration_selector_congr (d out : Device)
    (same : sendConfiguration out = sendConfiguration d)
    (s : Campaign2.Snapshot) :
    ClaimView.selectsDevice s out ↔ ClaimView.selectsDevice s d := by
  simp only [sendConfiguration,Prod.mk.injEq] at same
  simp only [ClaimView.selectsDevice,same.1,same.2.1]


end Leanux.Proofs.WG.Config

