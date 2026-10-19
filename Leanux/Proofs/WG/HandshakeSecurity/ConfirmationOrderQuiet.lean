import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationOrderPoll
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryReceive
import Leanux.Proofs.WG.TransmitSecurity.NativeAdapter

/-! History-only contracts for native source paths that cannot emit a
confirmation. These compose with the actual poll's conditioned confirmation
contract; no unconditional confirmation premise is introduced. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ConfirmationTransportOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity Driver
variable {E F : Type} {α : Type}

theorem focus_product (record : AuthenticatedEffects.TransportDriver.Replay → E)
    (decode : E → Option ResponderEvent) (encode : F → E) (select : E → Option F)
    (quiet : ∀ event, Unconfirmed decode (encode event)) (action : PrefixM F α) :
    ProductHistorySafe (Safe record decode) (focusPrefix encode select action) := by
  intro w h hi
  let suffix := ((runPrefix action w (h.filterMap select)).2.drop
    (h.filterMap select).length).map encode
  have hs : Safe record decode (h ++ suffix) := hi.quiet (by
    intro event member
    obtain ⟨source,_,rfl⟩ := List.mem_map.mp member
    exact quiet source)
  refine ⟨suffix,rfl,hs,?_⟩
  cases (runPrefix (focusPrefix encode select action) w h).1 with
  | error _ => trivial
  | ok out => rcases out with ⟨_,_⟩; exact hs

theorem focus_state (record : AuthenticatedEffects.TransportDriver.Replay → E)
    (decode : E → Option ResponderEvent) (encode : F → E) (select : E → Option F)
    (quiet : ∀ event, Unconfirmed decode (encode event)) (action : WGPrefix F α) :
    StateHistorySafe (Safe record decode) (focusStatePrefix encode select action) := by
  intro w a h hi
  let suffix := ((runStatePrefix action w a (h.filterMap select)).2.drop
    (h.filterMap select).length).map encode
  have hs : Safe record decode (h ++ suffix) := hi.quiet (by
    intro event member
    obtain ⟨source,_,rfl⟩ := List.mem_map.mp member
    exact quiet source)
  refine ⟨suffix,rfl,hs,?_⟩
  cases (runPrefix ((focusStatePrefix encode select action).run w) a h).1 with
  | error _ => trivial
  | ok out => rcases out with ⟨_,_⟩; exact hs

theorem receipt_product (record : AuthenticatedEffects.TransportDriver.Replay → E)
    (decode : E → Option ResponderEvent) (action : PrefixM E α)
    (make : RunWitness α → E) (quiet : ∀ r, Unconfirmed decode (make r))
    (ha : ProductHistorySafe (Safe record decode) action) :
    ProductHistorySafe (Safe record decode) (receiptObserved action make) := by
  intro w h hi
  obtain ⟨suffix,eq,hs,_⟩ := ha w h hi
  rw [runPrefix_receiptObserved]
  cases run : runPrefix action w h with
  | mk result hist =>
    simp only [run] at eq hs
    cases result with
    | error stop => exact ⟨suffix,eq,hs,trivial⟩
    | ok out =>
      rcases out with ⟨value,v⟩
      have safe := hs.quiet (suffix := [make ⟨value,w,v⟩]) (by simpa using quiet ⟨value,w,v⟩)
      exact ⟨suffix ++ [make ⟨value,w,v⟩],by simp [eq],safe,safe⟩

theorem receipt_state (record : AuthenticatedEffects.TransportDriver.Replay → E)
    (decode : E → Option ResponderEvent) (action : WGPrefix E α)
    (make : WGRunWitness α → E) (quiet : ∀ r, Unconfirmed decode (make r))
    (ha : StateHistorySafe (Safe record decode) action) :
    StateHistorySafe (Safe record decode) (receiptWGObserved action make) := by
  intro w a h hi
  obtain ⟨suffix,eq,hs,_⟩ := ha w a h hi
  have equation := runWGPrefix_receiptWGObserved action make w a h
  unfold runWGPrefix runStatePrefix at equation
  rw [equation]
  cases run : runPrefix (action.run w) a h with
  | mk result hist =>
    simp only [run] at eq hs
    cases result with
    | error stop => exact ⟨suffix,eq,hs,trivial⟩
    | ok out =>
      rcases out with ⟨⟨value,v⟩,b⟩
      have safe := hs.quiet (suffix := [make ⟨value,w,v,a,b⟩]) (by simpa using quiet ⟨value,w,v,a,b⟩)
      exact ⟨suffix ++ [make ⟨value,w,v,a,b⟩],by simp [eq],safe,safe⟩

theorem lower (record : AuthenticatedEffects.TransportDriver.Replay → E)
    (decode : E → Option ResponderEvent) (action : PrefixM E α)
    (ha : ProductHistorySafe (Safe record decode) action) :
    StateHistorySafe (Safe record decode) (NativeAdapter.lower action) := by
  intro w a h hi
  obtain ⟨suffix,eq,hs,_⟩ := ha (NativeAdapter.world w a) h hi
  refine ⟨suffix,eq,hs,?_⟩
  cases (runPrefix ((NativeAdapter.lower action).run w) a h).1 with
  | error _ => trivial
  | ok out => rcases out with ⟨_,_⟩; exact hs

theorem focused_native_receipt (record : AuthenticatedEffects.TransportDriver.Replay → E)
    (decode : E → Option ResponderEvent) (encode : F → E) (select : E → Option F)
    (action : WG.M α) (make : WGRunWitness α → F)
    (quiet : ∀ r, Unconfirmed decode (encode (make r))) :
    StateHistorySafe (Safe record decode)
      (focusStatePrefix encode select (receiptWGObserved (liftWGPrefix action) make)) := by
  have equal : focusStatePrefix encode select (receiptWGObserved (liftWGPrefix action) make) =
      receiptWGObserved (liftWGPrefix action) (fun r => encode (make r)) := by
    funext w a h
    change runWGPrefix (focusStatePrefix encode select _) w a h =
      runWGPrefix (receiptWGObserved (liftWGPrefix action) (fun r => encode (make r))) w a h
    change ((runWGPrefix (receiptWGObserved (liftWGPrefix action) make) w a (h.filterMap select)).1,
      h ++ ((runWGPrefix (receiptWGObserved (liftWGPrefix action) make) w a
        (h.filterMap select)).2.drop (h.filterMap select).length).map encode) = _
    rw [runWGPrefix_receiptWGObserved,runWGPrefix_receiptWGObserved,runWGPrefix_lift,runWGPrefix_lift]
    cases (action.run w).run a with
    | error stop => simp
    | ok out => rcases out with ⟨⟨_,_⟩,_⟩; simp
  rw [equal]
  exact receipt_state record decode _ _ quiet (state_lift record decode action)

theorem selection (record : AuthenticatedEffects.TransportDriver.Replay → E)
    (responder : ResponderEvent → E) (decode : E → Option ResponderEvent)
    (inverse : ∀ event, decode (responder event) = some event) (pid : PeerId) :
    StateHistorySafe (Safe record decode)
      (focusStatePrefix responder decode (Responder.DriverCuts.selection pid)) := by
  apply focused_native_receipt record decode
  intro r peer key receipt found
  rw [inverse] at found
  cases found

theorem session (record : AuthenticatedEffects.TransportDriver.Replay → E)
    (responder : ResponderEvent → E) (decode : E → Option ResponderEvent)
    (inverse : ∀ event, decode (responder event) = some event) (pid : PeerId) :
    StateHistorySafe (Safe record decode)
      (focusStatePrefix responder decode (Responder.DriverCuts.session pid)) := by
  apply focused_native_receipt record decode
  intro r peer key receipt found
  rw [inverse] at found
  cases found

end Leanux.Proofs.WG.HandshakeSecurity.ConfirmationTransportOrder
