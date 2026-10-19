import Leanux.Proofs.WG.Config.CommandOrderModel
import Leanux.Proofs.WG.Config.AllowedOrderEffects

/-! Pure consequences of the whole-command completion grammar. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.CommandOrder
open Leanux Leanux.WG Leanux.Proofs.WG.AllowedIps
open AllowedOrder

theorem partial_empty (attrs : PeerAttrs) (requested : UInt32) :
    Partial attrs requested [] := Or.inl rfl

theorem finished_empty (attrs : PeerAttrs) (requested : UInt32) (ret : Int) :
    Finished attrs requested [] ret := Or.inl rfl

theorem empty_segment {P : List RoutingCompletion→Prop}
    (empty : P []) (before : List RoutingCompletion) :
    Segment P before before := ⟨[],by simp,empty⟩

theorem partial_nonempty (attrs : PeerAttrs) (requested : UInt32)
    (events : List RoutingCompletion) (shape : Partial attrs requested events)
    (nonempty : events≠[]) :
    ∃pid effective, EffectiveFlags requested effective ∧
      UpdatePartial attrs (some pid) effective pid events := by
  rcases shape with empty | selected
  · exact False.elim (nonempty empty)
  · exact selected

theorem finished_nonempty (attrs : PeerAttrs) (requested : UInt32)
    (events : List RoutingCompletion) (ret : Int)
    (finished : Finished attrs requested events ret) (nonempty : events≠[]) :
    ∃pid effective, EffectiveFlags requested effective ∧
      UpdateFinished attrs (some pid) effective pid events ret := by
  rcases finished with empty | selected
  · exact False.elim (nonempty empty)
  · exact selected

theorem allowed_target {selected : PeerId} {input : List AllowedIpEntry}
    {events : List RoutingCompletion} (path : AllowedOrder.Partial selected input events)
    (e : RoutingCompletion) (member : e∈events) (pid : PeerId) (ip : AllowedIpAttrs) (ret : Int)
    (call : e.call=.allowedIp pid ip ret) : selected=pid := by
  rcases path with ⟨rest,previous,path⟩ |
    ⟨lastValue,prior,lastIp,rest,previous,last,path,lastCall,negative,rfl⟩
  · obtain ⟨other,value,actual,_⟩:=path.nonnegative e member
    rw [call] at actual
    cases actual
    rfl
  · rcases List.mem_append.mp member with before | final
    · obtain ⟨other,value,actual,_⟩:=path.nonnegative e before
      rw [call] at actual
      cases actual
      rfl
    · have same : e=last := List.mem_singleton.mp final
      subst e
      rw [call] at lastCall
      cases lastCall
      rfl

end Leanux.Proofs.WG.Config.CommandOrder
