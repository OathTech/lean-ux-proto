import Leanux.Proofs.WG.Progress.RxPrimitiveSuffixSource
import Leanux.Proofs.WG.Progress.ClearWorkerRecordFrames
import Leanux.Proofs.WG.Queues.RxPollStampSafety
import Leanux.Proofs.WG.Queues.RxPollDisposition
import Leanux.Proofs.WG.Queues.RxNapiCuts

/-! Ambient-sensitive frames for actual packet capture, ambient administration and the NAPI placement choice. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues

theorem poll_capture_retains (records : List HiddenRecord) (skb : SkbId) :
    PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True) (RxJoint.capture skb) := by
  intro w h hi
  obtain ⟨suffix,append⟩:=RxJoint.capture_appends skb w h
  refine ⟨suffix,append,True.intro,?_⟩
  cases run:(runPrefix (RxJoint.capture skb) w h).1 with
  | error stop=>trivial
  | ok out=>
    obtain ⟨⟨pkt,stamp⟩,v⟩:=out
    have same:=(RxDisposition.capture_selected skb w v h pkt stamp run).1
    change Tail records v.ambient.hidden
    rw [same]
    exact hi

theorem getAmbient_retains (records : List HiddenRecord) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (getAmbient : Leanux.M Ambient) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w value v pre run
  cases run
  exact pre

theorem chooseNapiHere_retains (records : List HiddenRecord) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) chooseNapiHere := by
  apply (hoare_iff_run _ _ _).mpr
  intro w value v pre run
  cases run
  exact pre
end Leanux.Proofs.WG.Progress.RecordSuffix
