import Leanux.Proofs.WG.Config.AllowedOrderModel

set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.AllowedOrder
open Leanux Leanux.WG Leanux.Proofs.WG.AllowedIps

theorem Finished.partial {pid input history ret} (point : Finished pid input history ret) :
    Partial pid input history := by
  rcases point with full | ⟨_,rest,previous,path⟩ | negative
  · exact Or.inl ⟨[],ret,full⟩
  · exact Or.inl ⟨.malformed::rest,previous,path⟩
  · exact Or.inr ⟨ret,negative⟩

theorem At.safe {pid input rest before acc history}
    (point : At pid input rest before acc history) : Safe pid input before history := by
  obtain ⟨_,added,equal,path⟩ := point
  exact ⟨added,equal,Or.inl ⟨rest,acc.2,path⟩⟩

theorem Done.safe {pid input before acc history}
    (point : Done pid input before acc history) : Safe pid input before history := by
  obtain ⟨added,equal,done⟩ := point
  refine ⟨added,equal,?_⟩
  cases selected : acc.1 with
  | none => exact Or.inl ⟨[],acc.2,by simpa only [selected] using done⟩
  | some ret => exact (show Finished pid input added ret by simpa only [selected] using done).partial

theorem After.safe {pid input ip rest before ret history}
    (point : After pid input ip rest before ret history) : Safe pid input before history := by
  obtain ⟨prior,previous,e,equal,path,call⟩ := point
  refine ⟨prior++[e],equal,?_⟩
  by_cases negative : ret<0
  · exact Or.inr ⟨ret,prior,ip,rest,previous,e,path,call,negative,rfl⟩
  · exact Or.inl ⟨rest,ret,Prefix.snoc path call (by omega)⟩

theorem After.nonnegative {pid input ip rest before ret history}
    (point : After pid input ip rest before ret history) (good : ¬ret<0) :
    At pid input rest before (none,ret) history := by
  obtain ⟨prior,previous,e,equal,path,call⟩ := point
  exact ⟨rfl,prior++[e],equal,Prefix.snoc path call (by omega)⟩

theorem After.negative {pid input ip rest before ret history}
    (point : After pid input ip rest before ret history) (bad : ret<0) :
    Done pid input before (some ret,ret) history := by
  obtain ⟨prior,previous,e,equal,path,call⟩ := point
  exact ⟨prior++[e],equal,Or.inr (Or.inr ⟨prior,ip,rest,previous,e,path,call,bad,rfl⟩)⟩

theorem UpdateFinished.partial {attrs peer flags pid events ret}
    (point : UpdateFinished attrs peer flags pid events ret) :
    UpdatePartial attrs peer flags pid events := by
  unfold UpdateFinished UpdatePartial at *
  split at point <;> simp only [*]
  · exact Or.inr point.2
  · obtain ⟨front,tail,hf,done,eq⟩:=point
    exact Or.inr ⟨front,tail,hf,done.partial,eq⟩

theorem UpdatePartial.empty (attrs : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (pid : PeerId) : UpdatePartial attrs peer flags pid [] := by
  unfold UpdatePartial
  split <;> exact Or.inl rfl

theorem Prefix.input_split {pid input rest ret events}
    (path : Prefix pid input rest ret events) :
    input=events.map eventInput++rest := by
  induction path with
  | nil=>rfl
  | @snoc ip rest previous history e ret prior call nonnegative ih =>
    rw [List.map_append,List.map_singleton]
    have input : eventInput e=.attrs ip := by simp only [eventInput,call]
    simpa only [input,List.append_assoc,List.singleton_append] using ih

theorem Partial.input_split {pid input events}
    (path : Partial pid input events) :
    ∃rest,input=events.map eventInput++rest := by
  rcases path with ⟨rest,ret,path⟩ | ⟨ret,prior,ip,rest,previous,e,path,call,negative,rfl⟩
  · exact ⟨rest,path.input_split⟩
  · refine ⟨rest,?_⟩
    rw [List.map_append,List.map_singleton]
    have selected : eventInput e=.attrs ip := by simp only [eventInput,call]
    simpa only [selected,List.append_assoc,List.singleton_append] using path.input_split

theorem Partial.position {pid input events} (path : Partial pid input events)
    (i : Nat) (e : RoutingCompletion) (ip : AllowedIpAttrs) (ret : Int)
    (selected : events[i]?=some e) (call : e.call=.allowedIp pid ip ret) :
    input[i]?=some (.attrs ip) := by
  obtain ⟨rest,shape⟩:=path.input_split
  rw[shape,List.getElem?_append_left]
  · simp only [List.getElem?_map,selected,Option.map_some,eventInput,call]
  · simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp selected).1

theorem Prefix.nonnegative {pid input rest ret events}
    (path : Prefix pid input rest ret events) :
    ∀ e∈events,∃ip value,e.call=.allowedIp pid ip value∧0≤value := by
  induction path with
  | nil=>simp
  | @snoc ip rest previous history e ret prior call nonnegative ih =>
    intro x member
    rcases List.mem_append.mp member with earlier | last
    · exact ih x earlier
    · have same : x=e := by simpa using last
      subst x
      exact ⟨ip,ret,call,nonnegative⟩

theorem Partial.negative_last {pid input events} (path : Partial pid input events)
    (i : Nat) (e : RoutingCompletion) (ip : AllowedIpAttrs) (ret : Int)
    (selected : events[i]?=some e) (call : e.call=.allowedIp pid ip ret)
    (negative : ret<0) : i+1=events.length := by
  rcases path with ⟨rest,previous,path⟩ | ⟨value,prior,other,rest,previous,last,path,lastCall,bad,eq⟩
  · obtain ⟨other,value,actual,good⟩:=path.nonnegative e (List.mem_of_getElem? selected)
    rw[call] at actual
    cases actual
    omega
  · subst events
    by_cases earlier : i<prior.length
    · have here : prior[i]?=some e := by simpa only [List.getElem?_append_left earlier] using selected
      obtain ⟨other,value,actual,good⟩:=path.nonnegative e (List.mem_of_getElem? here)
      rw[call] at actual
      cases actual
      omega
    · have bound:=(List.getElem?_eq_some_iff.mp selected).1
      simp only [List.length_append,List.length_singleton] at bound ⊢
      omega

theorem Prefix.allowedEvents {pid input rest ret events}
    (path : Prefix pid input rest ret events) : allowedEvents events=events := by
  induction path with
  | nil=>rfl
  | @snoc ip rest previous history e ret prior call nonnegative ih =>
    change (history++[e]).filter isAllowed=history++[e]
    rw[List.filter_append]
    rw[show history.filter isAllowed=history from ih]
    simp [isAllowed,call]

theorem Partial.allowedEvents {pid input events} (path : Partial pid input events) :
    allowedEvents events=events := by
  rcases path with ⟨rest,ret,path⟩ | ⟨ret,prior,ip,rest,previous,e,path,call,negative,rfl⟩
  · exact path.allowedEvents
  · change (prior++[e]).filter isAllowed=prior++[e]
    rw[List.filter_append]
    rw[show prior.filter isAllowed=prior from path.allowedEvents]
    simp [isAllowed,call]

theorem Removal.allowedEvents {peer events} (path : Removal peer events) :
    allowedEvents events=[] := by
  cases peer with
  | none=>cases path;rfl
  | some pid=>
    obtain ⟨e,call,rfl⟩:=path
    change [e].filter isAllowed=[]
    simp [isAllowed,call]

theorem Front.allowedEvents {replace pid events} (path : Front replace pid events) :
    allowedEvents events=[] := by
  unfold Front at path
  split at path
  · exact path.allowedEvents
  · cases path;rfl

theorem UpdatePartial.allowed_partial {attrs peer flags pid events}
    (path : UpdatePartial attrs peer flags pid events) :
    Partial pid (attrs.allowedIps.getD []) (allowedEvents events) := by
  unfold UpdatePartial at path
  split at path
  · rcases path with rfl | removed
    · exact Or.inl ⟨attrs.allowedIps.getD [],0,.nil⟩
    · rw[removed.allowedEvents]
      exact Or.inl ⟨attrs.allowedIps.getD [],0,.nil⟩
  · rcases path with rfl | ⟨front,tail,start,path,rfl⟩
    · exact Or.inl ⟨attrs.allowedIps.getD [],0,.nil⟩
    · have joined : allowedEvents (front++tail)=tail := by
        change (front++tail).filter isAllowed=tail
        rw[List.filter_append]
        rw[show front.filter isAllowed=[] from start.allowedEvents,
          show tail.filter isAllowed=tail from path.allowedEvents]
        rfl
      rw[joined]
      exact path

end Leanux.Proofs.WG.Config.AllowedOrder
