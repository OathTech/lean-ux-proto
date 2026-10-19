import Leanux.Proofs.WG.Config.AllowedOrderEffects

/-! A completed negative allowed-IP call determines the normal result of its enclosing update. These are pure grammar consequences. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG Leanux.Proofs.WG.AllowedIps

theorem prefix_negative_impossible {pid : PeerId} {input rest : List AllowedIpEntry}
    {last : Int} {events : List RoutingCompletion} (path : AllowedOrder.Prefix pid input rest last events)
    (e : RoutingCompletion) (member : e∈events) (target : PeerId) (ip : AllowedIpAttrs)
    (ret : Int) (call : e.call=.allowedIp target ip ret) (negative : ret<0) : False := by
  obtain ⟨other,value,actual,nonnegative⟩:=path.nonnegative e member
  rw [call] at actual
  cases actual
  omega

theorem finished_negative_result {pid : PeerId} {input : List AllowedIpEntry}
    {events : List RoutingCompletion} {result : Int}
    (path : AllowedOrder.Finished pid input events result)
    (e : RoutingCompletion) (member : e∈events) (target : PeerId) (ip : AllowedIpAttrs)
    (ret : Int) (call : e.call=.allowedIp target ip ret) (negative : ret<0) : result=ret := by
  rcases path with full | ⟨_,rest,previous,path⟩ |
    ⟨prior,lastIp,rest,previous,last,path,lastCall,_,rfl⟩
  · exact False.elim (prefix_negative_impossible full e member target ip ret call negative)
  · exact False.elim (prefix_negative_impossible path e member target ip ret call negative)
  · rcases List.mem_append.mp member with earlier | final
    · exact False.elim (prefix_negative_impossible path e earlier target ip ret call negative)
    · have same : e=last := List.mem_singleton.mp final
      subst e
      rw [call] at lastCall
      cases lastCall
      rfl

theorem update_negative_result {attrs : PeerAttrs} {peer : Option PeerId} {flags : UInt32}
    {pid : PeerId} {events : List RoutingCompletion} {result : Int}
    (path : AllowedOrder.UpdateFinished attrs peer flags pid events result)
    (e : RoutingCompletion) (member : e∈AllowedOrder.allowedEvents events)
    (target : PeerId) (ip : AllowedIpAttrs) (ret : Int)
    (call : e.call=.allowedIp target ip ret) (negative : ret<0) : result=ret := by
  unfold AllowedOrder.UpdateFinished at path
  split at path
  · rw [path.2.allowedEvents] at member
    cases member
  · obtain ⟨front,tail,replace,finished,rfl⟩:=path
    have shape : AllowedOrder.allowedEvents (front++tail)=tail := by
      change (front++tail).filter AllowedOrder.isAllowed=tail
      rw [List.filter_append]
      rw [show front.filter AllowedOrder.isAllowed=[] from replace.allowedEvents,
        show tail.filter AllowedOrder.isAllowed=tail from finished.partial.allowedEvents]
      rfl
    rw [shape] at member
    exact finished_negative_result finished e member target ip ret call negative

end Leanux.Proofs.WG.Config.RequestOrder
