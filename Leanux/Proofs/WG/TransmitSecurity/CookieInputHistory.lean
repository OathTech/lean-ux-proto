import Leanux.Proofs.WG.TransmitSecurity.HeaderLength
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptHandshake
import Leanux.Proofs.WG.AuthenticatedEffects.CookieConsumptionContracts
import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsHistory

/-! Cookie input widths are a separate historical obligation from native
socket validity and MAC qualification. Every checked reply below retains the
size fact of its own receiver input; queue initialization is separate. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CookieInput
open Leanux Leanux.WG Leanux.Proofs.Logged
open AuthenticatedEffects AuthenticatedEffects.CausalJournal

def Checked (_pre : List Event) : Event → Prop
  | .cookieSocket receipt => HeaderLength.Valid receipt.input
  | _ => True

def Safe (history : List Event) : Prop :=
  ∀ pre event post, history = pre ++ event :: post → Checked pre event

def Unchecked : Event → Prop
  | .cookieSocket _ => False
  | _ => True

theorem Safe.empty : Safe [] := by
  intro pre event post position
  have sizes := congrArg List.length position
  simp at sizes

theorem Safe.append (hi : Safe h)
    (checked : ∀ pre event post, suffix = pre ++ event :: post → Checked (h ++ pre) event) :
    Safe (h ++ suffix) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    Checked h suffix hi checked

theorem unchecked_checked (event : Event) (quiet : Unchecked event) (pre : List Event) : Checked pre event := by
  cases event <;> first | exact quiet.elim | trivial

theorem Safe.quiet (hi : Safe h) (quiet : ∀ event ∈ suffix, Unchecked event) : Safe (h ++ suffix) := by
  apply hi.append
  intro pre event post position
  apply unchecked_checked event
  apply quiet event
  rw [position]
  simp

theorem Safe.emit (hi : Safe h) (checked : Checked h event) : Safe (h ++ [event]) := by
  apply hi.append
  intro pre entry post position
  cases pre with
  | nil => cases position; simpa only [List.append_nil] using checked
  | cons first rest =>
    have sizes := congrArg List.length position
    simp only [List.length_append,List.length_cons,List.length_nil] at sizes
    omega

theorem quiet_state (encode : F → Event) (decode : Event → Option F)
    (quiet : ∀ event, Unchecked (encode event)) (body : WGPrefix F α) :
    Driver.StateHistorySafe Safe (focusStatePrefix encode decode body) := by
  intro w a h hi
  let suffix := ((runWGPrefix body w a (h.filterMap decode)).2.drop (h.filterMap decode).length).map encode
  have good : Safe (h ++ suffix) := hi.quiet (by
    intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    exact quiet original)
  refine ⟨suffix,rfl,good,?_⟩
  cases (runPrefix (StateT.run (focusStatePrefix encode decode body) w) a h).1 <;> trivial

theorem quiet_product (encode : F → Event) (decode : Event → Option F)
    (quiet : ∀ event, Unchecked (encode event)) (body : PrefixM F α) :
    Driver.ProductHistorySafe Safe (focusPrefix encode decode body) := by
  intro w h hi
  let suffix := ((runPrefix body w (h.filterMap decode)).2.drop (h.filterMap decode).length).map encode
  have good : Safe (h ++ suffix) := hi.quiet (by
    intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    exact quiet original)
  refine ⟨suffix,rfl,good,?_⟩
  cases (runPrefix (focusPrefix encode decode body) w h).1 <;> trivial

theorem emit_quiet (event : Event) (quiet : Unchecked event) :
    Driver.StateHistorySafe Safe (emitStatePrefix event) :=
  StatePrefixEnsures.emit event (fun h _ _ hi => hi.emit (unchecked_checked event quiet h))
    (fun h _ _ hi => hi.emit (unchecked_checked event quiet h))

theorem receipt_quiet (body : WGPrefix Event α) (preserves : Driver.StateHistorySafe Safe body)
    (record : WGRunWitness α → Event) (quiet : ∀ r, Unchecked (record r)) :
    Driver.StateHistorySafe Safe (receiptWGObserved body record) := by
  unfold receiptWGObserved
  exact Driver.History.state_bind preserves.captureWGObserved (fun r =>
    Driver.History.state_bind (emit_quiet (record r) (quiet r)) (fun _ => Driver.History.state_pure _))

theorem state_scope (cause : Cause) (body : WGPrefix Event α)
    (preserves : Driver.StateHistorySafe Safe body) :
    Driver.StateHistorySafe Safe (CausalScope.scope Event.scope cause body) :=
  CausalScope.scope_preserves Event.scope cause body (fun _ _ _ hi => hi)
    (fun event h _ _ hi => hi.emit (unchecked_checked (.scope event) True.intro h)) preserves

theorem state_enter (cause : Cause) :
    Driver.StateHistorySafe Safe (CausalScope.enterState Event.scope cause) :=
  CausalScope.enterState_preserves Event.scope cause (fun _ _ _ hi => hi)
    (fun event h _ _ hi => hi.emit (unchecked_checked (.scope event) True.intro h))

theorem state_leave (token : Nat) :
    Driver.StateHistorySafe Safe (CausalScope.leaveState Event.scope token) :=
  emit_quiet _ True.intro

theorem product_emit (event : Event) (quiet : Unchecked event) :
    Driver.ProductHistorySafe Safe (emitPrefix event) := by
  intro w h hi
  have good := hi.emit (unchecked_checked event quiet h)
  exact ⟨[event],rfl,good,good⟩

theorem product_enter (cause : Cause) :
    Driver.ProductHistorySafe Safe (CausalScope.enterPrefix Event.scope cause) := by
  intro w h hi
  have good := hi.emit (unchecked_checked (.scope (.entered ⟨h.length,cause⟩)) True.intro h)
  exact ⟨[.scope (.entered ⟨h.length,cause⟩)],rfl,good,good⟩

theorem product_leave (token : Nat) :
    Driver.ProductHistorySafe Safe (CausalScope.leavePrefix Event.scope token) :=
  product_emit _ True.intro

theorem product_scope (cause : Cause) (body : CausalScope.Token Cause → PrefixM Event α)
    (preserves : ∀ token, Driver.ProductHistorySafe Safe (body token)) :
    Driver.ProductHistorySafe Safe (CausalScope.prefixScope Event.scope cause body) := by
  intro w h hi
  exact Driver.History.product_bind (product_emit (.scope (.entered ⟨h.length,cause⟩)) True.intro)
    (fun _ => Driver.History.product_bind (preserves ⟨h.length,cause⟩) (fun result =>
      Driver.History.product_bind (product_leave h.length) (fun _ => Driver.History.product_pure result))) w h hi

theorem cookie (mac : HandshakeMac) (msg : Key) (src : SkbSource)
    (valid : HeaderLength.Valid msg) :
    Driver.StateHistorySafe Safe (CookieSocket.observed Event.cookieSocket mac msg src) := by
  intro w a history before
  obtain ⟨suffix,grown,_,members⟩ := CookieSocket.observed_receipts Event.cookieSocket mac msg src w a history
  have after : Safe (history ++ suffix) := by
    apply before.append
    intro pre event post position
    have inside : event ∈ suffix := by rw [position]; simp
    obtain ⟨receipt,rfl,_,_,input,_⟩ := members event inside
    change HeaderLength.Valid receipt.input
    rw [input]
    exact valid
  change (runPrefix ((CookieSocket.observed Event.cookieSocket mac msg src).run w) a history).2 = history ++ suffix at grown
  have safe : Safe (runPrefix ((CookieSocket.observed Event.cookieSocket mac msg src).run w) a history).2 := by
    rw [grown]
    exact after
  refine ⟨suffix,grown,safe,?_⟩
  cases (runPrefix ((CookieSocket.observed Event.cookieSocket mac msg src).run w) a history).1 <;> trivial

end Leanux.Proofs.WG.TransmitSecurity.CookieInput
