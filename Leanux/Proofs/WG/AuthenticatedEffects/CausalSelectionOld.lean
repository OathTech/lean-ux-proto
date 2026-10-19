import Leanux.Proofs.WG.AuthenticatedEffects.CausalSelectionQuiet

/-! The embedded journal's ordinary hooks cannot add timer selections. This
uses the appended history of the actual callback, including its failed prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

def oldTimer? : Journal.Event → Option Unit
  | .timerSelected _ => some ()
  | _ => none

private theorem quiet_of_none (event : Journal.Event) (none : oldTimer? event = Option.none) :
    Quiet (.old event) := by
  cases event <;> first | trivial | cases none

theorem old_history (body : PrefixT Journal.Event State α) (appends : Appends body)
    (frame : HistoryFrame oldTimer? body) :
    PrefixPreserves (fun h (_ : State) => Safe h) Safe (focusPrefix Event.old old? body) := by
  intro w h input
  obtain ⟨suffix,grown⟩ := appends w (h.filterMap old?)
  have retained := frame w (h.filterMap old?)
  rw [grown,List.filterMap_append] at retained
  have absent : suffix.filterMap oldTimer? = [] := by
    simpa using retained
  have quiet : ∀ event ∈ suffix.map Event.old, Quiet event := by
    intro event member
    obtain ⟨original,inSuffix,rfl⟩ := List.mem_map.mp member
    apply quiet_of_none
    cases selected : oldTimer? original with
    | none => rfl
    | some value =>
      have found : value ∈ suffix.filterMap oldTimer? := List.mem_filterMap.mpr ⟨original,inSuffix,selected⟩
      simp [absent] at found
  rw [focusPrefix_suffix Event.old old? body w h _ suffix (Prod.ext rfl grown)]
  have safe := input.quiet quiet
  refine ⟨suffix.map Event.old,rfl,safe,?_⟩
  cases (runPrefix body w (h.filterMap old?)).1 <;> trivial

theorem old_state (body : WGPrefix Journal.Event α) (appends : StateAppends body)
    (frame : StateHistoryFrame oldTimer? body) : Driver.StateHistorySafe Safe (state body) :=
  fun w => old_history (body.run w) (appends w) (frame w)

theorem old_product (body : PrefixM Journal.Event α) (appends : Appends body)
    (frame : HistoryFrame oldTimer? body) : Driver.ProductHistorySafe Safe (product body) :=
  old_history body appends frame

private theorem focus_state (encode : F → Journal.Event) (decode : Journal.Event → Option F)
    (quiet : ∀ event, oldTimer? (encode event) = none) (body : WGPrefix F α) :
    Driver.StateHistorySafe Safe (state (focusStatePrefix encode decode body)) :=
  old_state _ (StateAppends.focus _ _ _) (fun w a h => focusPrefix_other _ _ oldTimer? quiet (body.run w) a h)

private theorem native_appends (action : WG.M α) : StateAppends (liftWGPrefix action : WGPrefix Journal.Event α) :=
  fun _ _ _ => ⟨[],by simp only [List.append_nil]; rfl⟩

theorem selection (pid : PeerId) : Driver.StateHistorySafe Safe (hooks.selection pid) :=
  focus_state Journal.Event.responder Journal.responder? (fun _ => rfl) _

theorem confirmation (pid : PeerId) (kid : KeypairId) :
    Driver.StateHistorySafe Safe (hooks.confirmation pid kid) :=
  focus_state Journal.Event.responder Journal.responder? (fun _ => rfl) _

theorem session (pid : PeerId) : Driver.StateHistorySafe Safe (hooks.session pid) :=
  receipt_quiet _ (focus_state Journal.Event.responder Journal.responder? (fun _ => rfl) _) _ (fun _ => True.intro)

theorem reserve (slot : KeypairId) : Driver.StateHistorySafe Safe (hooks.reserve slot) :=
  old_state _ (StateAppends.receiptWGObserved (StateAppends.focus _ _ _) _)
    (StateHistoryFrame.receiptWGObserved
      (fun w a h => focusPrefix_other _ _ oldTimer? (fun _ => rfl) (Nonce.reserveObserved slot |>.run w) a h)
      _ (fun _ => rfl))

theorem allocate (packets : List DataPacket) : Driver.StateHistorySafe Safe (hooks.allocate packets) :=
  old_state _ (StateAppends.receiptWGObserved (native_appends _) _)
    (StateHistoryFrame.receiptWGObserved (fun _ _ _ => rfl) _ (fun _ => rfl))

theorem front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Driver.StateHistorySafe Safe (hooks.front family addr packets mtu) :=
  old_state _ (StateAppends.receiptWGObserved (native_appends _) _)
    (StateHistoryFrame.receiptWGObserved (fun _ _ _ => rfl) _ (fun _ => rfl))

theorem create (pid : PeerId) (items : List SkbId) : Driver.StateHistorySafe Safe (hooks.create pid items) := by
  apply old_state
  · intro w a h
    exact Appends.focus Journal.Event.disposition Journal.disposition? (Queues.TxDisposition.create pid items)
      (NativeAdapter.world w a) h
  · intro w a h
    exact focusPrefix_other Journal.Event.disposition Journal.disposition? oldTimer? (fun _ => rfl)
      (Queues.TxDisposition.create pid items) (NativeAdapter.world w a) h

theorem prepare : Driver.ProductHistorySafe Safe hooks.prepare :=
  old_product _ (Appends.focus _ _ _)
    (fun w h => focusPrefix_other _ _ oldTimer? (fun _ => rfl) _ w h)

theorem counter (skb : SkbId) (packet : RxPacket) : Driver.ProductHistorySafe Safe (hooks.counterCheck skb packet) :=
  old_product _ (Appends.receiptObserved (Appends.lift _))
    (HistoryFrame.receiptObserved (HistoryFrame.lift oldTimer? _) (fun _ => rfl))

theorem poll : Driver.ProductHistorySafe Safe hooks.poll :=
  old_product _ (Appends.receiptObserved (Appends.focus _ _ _))
    (HistoryFrame.receiptObserved (fun w h => focusPrefix_other _ _ oldTimer? (fun _ => rfl) _ w h) (fun _ => rfl))

theorem encrypt (items : Option (List SkbId)) : Driver.ProductHistorySafe Safe (hooks.encrypt items) :=
  old_product _ (Appends.receiptObserved (Appends.focus _ _ _))
    (HistoryFrame.receiptObserved (fun w h => focusPrefix_other _ _ oldTimer? (fun _ => rfl) _ w h) (fun _ => rfl))

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections
