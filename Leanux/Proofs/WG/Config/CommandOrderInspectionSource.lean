import Leanux.Proofs.WG.Config.CommandOrderInspectionBridge

/-! All-outcome agreement and same-run order/routing extraction. Stops retain completed receipts but expose no final state. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.CommandOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.AllowedIps Configuration Noise
open Leanux.Proofs.Framing Lifetimes Std.Do
open AllowedOrder

theorem inspection_outcome (attrs : PeerAttrs) (w : WGWorld) (ambient : Ambient) :
    (inspection attrs w ambient).outcome =
      Campaign2.observeResult (((setPeerCmd attrs).run w).run ambient) :=
  congrArg Campaign2.observeResult (setPeerCmdObserved_erases attrs w ambient [])

theorem inspection_facts (attrs : PeerAttrs) (w : WGWorld) (ambient : Ambient) :
    Facts attrs (Campaign2.snapshot w ambient) (inspection attrs w ambient) := by
  obtain ⟨suffix,eq,safe,post⟩:=command_spec attrs [] w ambient [] rfl
  obtain ⟨events,history,path⟩:=safe
  have known : (inspection attrs w ambient).completions=events := by
    simpa only [inspection,runWGPrefix,runStatePrefix,List.nil_append] using history
  refine ⟨⟨w,ambient,rfl,rfl⟩,by simpa only [known] using path,?_⟩
  cases outcome : (runPrefix (StateT.run (setPeerCmdObserved attrs) w) ambient []).1 with
  | error stop=>
    simp only [inspection,runWGPrefix,runStatePrefix,Campaign2.observeResult,outcome,Except.map]
  | ok value=>
    obtain ⟨⟨ret,v⟩,after⟩:=value
    simp only [outcome] at post
    obtain ⟨events,history,finished⟩:=post
    have same : (inspection attrs w ambient).completions=events := by
      simpa only [inspection,runWGPrefix,runStatePrefix,List.nil_append] using history
    simpa only [inspection,runWGPrefix,runStatePrefix,Campaign2.observeResult,outcome,Except.map] using
      (show Finished attrs (attrs.flags.getD 0) (inspection attrs w ambient).completions ret by
        simpa only [same] using finished)

theorem inspection_routed (tables : FlatTable×FlatTable) (attrs : PeerAttrs)
    (shape : PeerAddressShape attrs) (w : WGWorld) (ambient : Ambient)
    (target : RoutedView ((Campaign2.snapshot w ambient).wg.device.map routingState) tables) :
    RoutedFacts tables (inspection attrs w ambient) := by
  have start : CompletionState tables [] w := ⟨.nil,target⟩
  obtain ⟨suffix,eq,safe,post⟩:=setPeerCmdObserved_spec tables attrs shape w ambient [] start
  refine ⟨safe,?_⟩
  cases outcome : (runPrefix (StateT.run (setPeerCmdObserved attrs) w) ambient []).1 with
  | error stop=>
    simp only [inspection,runWGPrefix,runStatePrefix,Campaign2.observeResult,outcome,Except.map]
  | ok value=>
    obtain ⟨⟨ret,v⟩,after⟩:=value
    simp only [outcome] at post
    simp only [inspection,runWGPrefix,runStatePrefix,Campaign2.observeResult,outcome,Except.map]
    exact post.2

end Leanux.Proofs.WG.Config.CommandOrder
