import Leanux.Proofs.WG.Config.RequestReadbackBridge
import Leanux.Proofs.WG.Config.RequestOrderInspectionSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG
theorem readback_matches_returns (attrs : DeviceAttrs) (d : Device)
    (initial : Campaign2.Snapshot) (inspected : Inspection)
    (outcome : Campaign2.Outcome (Int × Except Int Lean.Json))
    (matched : ReadbackMatches attrs d initial inspected outcome)
    (ret : Int) (middle : Campaign2.Snapshot) (normal : inspected.outcome=.ok (ret,middle))
    (post : Except Int Lean.Json→Campaign2.Snapshot→Prop)
    (getter : Campaign2.Returns (wgGetDevice (byIndex d)) (fun s=>s=middle) post) :
    ∃ dump final,outcome=.ok ((ret,dump),final) ∧ post dump final := by
  obtain ⟨w,ambient,rfl,rfl,rfl⟩:=matched
  have original := (inspection_outcome attrs w ambient).symm.trans normal
  cases setRun : ((wgSetDevice attrs).run w).run ambient with
  | error stop =>
    simp only [Campaign2.observeResult,setRun,Except.map] at original
    cases original
  | ok result =>
    obtain ⟨⟨value,current⟩,next⟩:=result
    simp only [Campaign2.observeResult,setRun,Except.map] at original
    cases original
    obtain ⟨dump,final,after,getRun,effects⟩:=getter current next rfl
    refine ⟨dump,Campaign2.snapshot final after,?_,effects⟩
    change Campaign2.observeResult
      ((((wgSetDevice attrs).run w).run ambient >>= fun ((ret,middle),next)=>
        ((wgGetDevice (byIndex d)).run middle).run next >>= fun ((dump,out),rest)=>
          Except.ok (((ret,dump),out),rest)))=_
    rw [setRun]
    change Campaign2.observeResult
      ((((wgGetDevice (byIndex d)).run current).run next >>= fun ((dump,out),rest)=>
        Except.ok (((ret,dump),out),rest)))=_
    rw [getRun]
    rfl
end Leanux.Proofs.WG.Config.RequestOrder

