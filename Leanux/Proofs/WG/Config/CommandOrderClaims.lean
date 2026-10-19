import Leanux.Proofs.WG.Config.CommandOrderInspectionSource

/-! Arbitrary-attribute whole-command certificates. Effective-mask alternatives are source-derived grammar, not acquisition receipts; exact validation refusals are covered separately by UpdateOnly.original_validation. Routing semantics retain the explicit C1 address-shape and initial routed-view domain. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.CommandOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.AllowedIps Configuration Noise
open Leanux.Proofs.Framing Lifetimes Std.Do
open AllowedOrder

theorem original_command_order (attrs : PeerAttrs) :
    Campaign2.Observes (setPeerCmd attrs) (fun _=>True)
      (fun entry outcome=>∃result:Inspection,result.outcome=outcome ∧ Facts attrs entry result) := by
  intro w ambient _
  exact ⟨inspection attrs w ambient,inspection_outcome attrs w ambient,
    inspection_facts attrs w ambient⟩

theorem original_command_routed_order (tables : FlatTable×FlatTable) (attrs : PeerAttrs)
    (shape : PeerAddressShape attrs) :
    Campaign2.Observes (setPeerCmd attrs)
      (fun s=>RoutedView (s.wg.device.map routingState) tables)
      (fun entry outcome=>∃result:Inspection,result.outcome=outcome ∧
        Facts attrs entry result ∧ RoutedFacts tables result) := by
  intro w ambient target
  exact ⟨inspection attrs w ambient,inspection_outcome attrs w ambient,
    inspection_facts attrs w ambient,inspection_routed tables attrs shape w ambient target⟩

theorem certificate_selected (attrs : PeerAttrs) (entry : Campaign2.Snapshot) (result : Inspection)
    (facts : Facts attrs entry result) (nonempty : result.completions≠[]) :
    ∃pid effective, EffectiveFlags (attrs.flags.getD 0) effective ∧
      UpdatePartial attrs (some pid) effective pid result.completions ∧
      match result.outcome with
      | .error _=>True
      | .ok (ret,_)=>UpdateFinished attrs (some pid) effective pid result.completions ret := by
  cases outcome : result.outcome with
  | error stop=>
    obtain ⟨pid,effective,flags,shape⟩:=
      partial_nonempty attrs (attrs.flags.getD 0) _ facts.2.1 nonempty
    exact ⟨pid,effective,flags,shape,trivial⟩
  | ok value=>
    obtain ⟨ret,final⟩:=value
    have finished : Finished attrs (attrs.flags.getD 0) result.completions ret := by
      simpa only [outcome] using facts.2.2
    obtain ⟨pid,effective,flags,shape⟩:=
      finished_nonempty attrs (attrs.flags.getD 0) _ ret finished nonempty
    exact ⟨pid,effective,flags,shape.partial,shape⟩

theorem certificate_allowed_position (attrs : PeerAttrs) (entry : Campaign2.Snapshot)
    (result : Inspection) (facts : Facts attrs entry result)
    (i : Nat) (e : RoutingCompletion) (pid : PeerId) (ip : AllowedIpAttrs) (ret : Int)
    (selected : (allowedEvents result.completions)[i]?=some e)
    (call : e.call=.allowedIp pid ip ret) :
    (attrs.allowedIps.getD [])[i]?=some (.attrs ip) := by
  have nonempty : result.completions≠[] := by
    intro empty
    simp only [empty,allowedEvents,List.filter_nil,List.getElem?_nil] at selected
    cases selected
  obtain ⟨actual,effective,_,shape,_⟩:=certificate_selected attrs entry result facts nonempty
  have target:=allowed_target shape.allowed_partial e (List.mem_of_getElem? selected) pid ip ret call
  subst actual
  exact shape.allowed_partial.position i e ip ret selected call

theorem certificate_negative_last (attrs : PeerAttrs) (entry : Campaign2.Snapshot)
    (result : Inspection) (facts : Facts attrs entry result)
    (i : Nat) (e : RoutingCompletion) (pid : PeerId) (ip : AllowedIpAttrs) (ret : Int)
    (selected : (allowedEvents result.completions)[i]?=some e)
    (call : e.call=.allowedIp pid ip ret) (negative : ret<0) :
    i+1=(allowedEvents result.completions).length := by
  have nonempty : result.completions≠[] := by
    intro empty
    simp only [empty,allowedEvents,List.filter_nil,List.getElem?_nil] at selected
    cases selected
  obtain ⟨actual,effective,_,shape,_⟩:=certificate_selected attrs entry result facts nonempty
  have target:=allowed_target shape.allowed_partial e (List.mem_of_getElem? selected) pid ip ret call
  subst actual
  exact shape.allowed_partial.negative_last i e ip ret selected call negative

end Leanux.Proofs.WG.Config.CommandOrder
