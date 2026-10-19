import Leanux.Proofs.WG.Config.RequestOrderInspectionBridge

/-! Actual request inspection satisfies the projected certificate on every outcome. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration

theorem inspection_outcome (attrs : DeviceAttrs) (w : WGWorld) (ambient : Ambient) :
    (inspection attrs w ambient).outcome =
      Campaign2.observeResult (((wgSetDevice attrs).run w).run ambient) :=
  congrArg Campaign2.observeResult (observe_erases attrs w ambient [])

theorem inspection_facts (attrs : DeviceAttrs) (w : WGWorld) (ambient : Ambient) :
    InspectionFacts attrs (Campaign2.snapshot w ambient) (inspection attrs w ambient) := by
  obtain ⟨_,_,valid,_⟩ := observe_valid attrs w ambient [] (by simp [ValidHistory])
  obtain ⟨added,history,path,normal⟩ := observe_conforms attrs w ambient []
  have history' : (inspection attrs w ambient).receipts = added := by
    simpa only [inspection,List.nil_append] using history
  have rawHistory : (runWGPrefix (observe attrs) w ambient []).2 = added := by
    simpa only [List.nil_append] using history
  refine ⟨⟨w,ambient,rfl,rfl⟩,valid,?_,?_⟩
  · simpa only [history'] using path
  · cases run : (runWGPrefix (observe attrs) w ambient []).1 with
    | error stop => simp only [inspection,Campaign2.observeResult,run,Except.map]
    | ok out =>
      rcases out with ⟨⟨ret,v⟩,after⟩
      have point : (requestLanguage attrs).normal ret added := by
        simpa only [Finished,run] using normal
      simpa only [inspection,Campaign2.observeResult,run,Except.map,rawHistory] using point

theorem inspection_prelude (attrs : DeviceAttrs) (w : WGWorld) (ambient : Ambient) :
    PreludeFacts attrs (Campaign2.snapshot w ambient) (inspection attrs w ambient) := by
  obtain ⟨added,history,safe,post⟩ := observe_prelude attrs w ambient w ambient [] ⟨rfl,rfl⟩
  refine ⟨safe,?_⟩
  cases run : (runWGPrefix (observe attrs) w ambient []).1 with
  | error stop => simp only [inspection,Campaign2.observeResult,run,Except.map]
  | ok out =>
    rcases out with ⟨⟨ret,v⟩,after⟩
    have nativeRun := run
    simp only [runWGPrefix,runStatePrefix] at nativeRun
    have normal : PreludePost attrs w ambient (inspection attrs w ambient).receipts v := by
      simpa only [inspection,runWGPrefix,runStatePrefix,nativeRun] using post
    simp only [inspection,Campaign2.observeResult,run,Except.map]
    intro empty
    rcases normal with ⟨_,rfl⟩ | ⟨r,rest,shape,_⟩
    · rfl
    · have bad : ([] : List Receipt) = r :: rest := empty.symm.trans shape
      cases bad

theorem inspection_certificate (attrs : DeviceAttrs) (w : WGWorld) (ambient : Ambient) :
    Certificate attrs (Campaign2.snapshot w ambient) (inspection attrs w ambient) :=
  ⟨inspection_facts attrs w ambient,inspection_prelude attrs w ambient⟩

end Leanux.Proofs.WG.Config.RequestOrder
