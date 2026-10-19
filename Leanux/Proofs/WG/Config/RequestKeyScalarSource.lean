import Leanux.Proofs.WG.Config.RequestKeyEntriesSource
import Leanux.Proofs.WG.Config.RequestKeyScalarFrames
import Leanux.Proofs.WG.Config.GetterScalarSource

/-! Concrete pre-key contracts retain serialized scalar values through actual queued replacement and port handling. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterScalar
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do
open Leanux.Proofs.WG.Configuration Leanux.Proofs.Logged RequestOrder

theorem prefix_contracts (initial : Campaign2.Snapshot) (attrs : DeviceAttrs) :
    EntryTransport.Contracts (Retained (observation initial)) (Keeps initial) attrs where
  projected _ _ pre := pre
  generation _ := preserves_bind
    ((ensures_iff _ _ _).mp (of_frame _ _
      (modify_device (fun d=>{d with deviceUpdateGen:=d.deviceUpdateGen+1}) (fun _=>rfl))))
    (fun _=>preserves_pure _)
  fwmark := (ensures_iff _ _ _).mp (of_frame _ _
    (modify_device (fun d=>{d with fwmark:=attrs.fwmark.getD 0}) (fun _=>rfl)))
  clear pid := preserves_bind ((ensures_iff _ _ _).mp (of_frame _ _ (clear_source pid)))
    (fun _=>preserves_pure _)
  port port := (ensures_iff _ _ _).mp (of_frame _ _ (GetterScalar.port port))
  replacement := preserves_bind ((ensures_iff _ _ _).mp (remove_all (observation initial)))
    (fun _=>preserves_pure _)
end Leanux.Proofs.WG.Config.GetterScalar
