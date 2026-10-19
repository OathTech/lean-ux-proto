import Leanux.Proofs.WG.Roaming.HandshakeOverlayStepSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeOverlay
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Origins
variable {E F α State : Type}

def receiveStep : PrefixM RxEvent Bool := focusPrefix rxEncode rxDecode step
theorem rx_decode_encode (e : Event) : rxDecode (rxEncode e) = some e := by
  cases e with
  | inl e => simp only [rxDecode,rxEncode,HistoryAdapters.decode_encode,Option.map_some]
  | inr r => rfl

theorem rx_input_old (h : List RxEvent) :
    (h.filterMap rxDecode).filterMap oldEvent =
      (h.filterMap rxEvent).filterMap HistoryAdapters.decode := by
  rw [List.filterMap_filterMap,List.filterMap_filterMap]
  apply congrArg (fun f => h.filterMap f)
  funext e
  cases e with
  | inl e =>
    change ((HistoryAdapters.decode e).map Sum.inl).bind oldEvent = HistoryAdapters.decode e
    cases HistoryAdapters.decode e <;> rfl
  | inr r => rfl

theorem rx_input_attempt (h : List RxEvent) :
    (h.filterMap rxDecode).filterMap attemptEvent = h.filterMap rxAttempt := by
  rw [List.filterMap_filterMap]
  apply congrArg (fun f => h.filterMap f)
  funext e
  cases e with
  | inl e =>
    dsimp only [rxDecode,rxAttempt]
    cases HistoryAdapters.decode e <;> rfl
  | inr r => rfl

theorem rx_output_old (h : List Event) :
    (h.map rxEncode).filterMap rxEvent =
      (h.filterMap oldEvent).map HistoryAdapters.encode := by
  induction h with
  | nil => rfl
  | cons e es ih =>
    cases e <;> simp only [List.map_cons,List.filterMap_cons,rxEncode,rxEvent,oldEvent,ih]

theorem receiveStep_projects :
    ProjectsPrefix rxEvent id receiveStep HistoryAdapters.receiveStep := by
  intro w h
  obtain ⟨suffix,hs⟩ := step_appends w (h.filterMap rxDecode)
  have run : runPrefix step w (h.filterMap rxDecode) =
      ((runPrefix step w (h.filterMap rxDecode)).1,h.filterMap rxDecode ++ suffix) :=
    Prod.ext rfl hs
  have projected := step_old w (h.filterMap rxDecode)
  have oldRun : runPrefix HistoryAdapters.localStep w
      ((h.filterMap rxEvent).filterMap HistoryAdapters.decode) =
      ((runPrefix step w (h.filterMap rxDecode)).1,
        (h.filterMap rxEvent).filterMap HistoryAdapters.decode ++ suffix.filterMap oldEvent) := by
    rw [rx_input_old,run] at projected
    simp only [List.filterMap_append,rx_input_old] at projected
    cases result : (runPrefix step w (h.filterMap rxDecode)).1 <;>
      simpa only [result,Except.map,id_eq] using projected
  change runPrefix (HistoryAdapters.focus HistoryAdapters.localStep) w (h.filterMap rxEvent) = _
  rw [receiveStep,focusPrefix_suffix rxEncode rxDecode step w h _ suffix run]
  unfold HistoryAdapters.focus
  rw [focusPrefix_suffix HistoryAdapters.encode HistoryAdapters.decode HistoryAdapters.localStep
    w (h.filterMap rxEvent) _ (suffix.filterMap oldEvent) oldRun]
  simp only [List.filterMap_append,rx_output_old]
  cases (runPrefix step w (h.filterMap rxDecode)).1 <;> rfl

theorem receiveStep_appends : Appends receiveStep := Appends.focus _ _ _
theorem receiveStep_erases : ErasesPrefix receiveStep (liftWG WG.receiveStep) :=
  focusPrefix_erases _ _ step_erases

theorem receiveStep_valid :
    PrefixPreserves (fun h _ => RxValid h) RxValid receiveStep := by
  have focused := (show PrefixEnsures (fun h _ => Valid h) Valid step
    (fun _ h _ => Valid h) from step_valid).focus rxEncode rxDecode rx_decode_encode
  change PrefixPreserves
    (fun h (_ : World) => HandshakeAttemptAuth.ValidHistory Authenticated (h.filterMap rxAttempt))
    (fun h => HandshakeAttemptAuth.ValidHistory Authenticated (h.filterMap rxAttempt))
    (focusPrefix rxEncode rxDecode step)
  simpa only [Valid,rx_input_attempt,HandshakeAttemptAuth.ValidHistory] using focused.preserves

theorem receiveStep_attempts (w : World) (h : List RxEvent) (prior : RxValid h) :
    ∀ r ∈ (runPrefix receiveStep w h).2.filterMap rxAttempt, Authenticated r := by
  obtain ⟨_,_,valid,_⟩ := receiveStep_valid w h prior
  exact valid



end Leanux.Proofs.WG.Roaming.HandshakeOverlay
