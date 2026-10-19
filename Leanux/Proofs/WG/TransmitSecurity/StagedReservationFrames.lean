import Leanux.Proofs.WG.TransmitSecurity.StagedNoKeyOrigins

/-! Reserving a nonce records its native increment without changing the held
plaintext batch or introducing another staged selection. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects.CausalJournal

theorem focused_history_frame (encode : E → F) (decode : F → Option E)
    (ρ : F → Option G) (action : WGPrefix E α) (appends : StateAppends action)
    (quiet : StateHistoryFrame (ρ ∘ encode) action) :
    StateHistoryFrame ρ (focusStatePrefix encode decode action) := by
  intro w a h
  obtain ⟨suffix,position⟩ := appends w a (h.filterMap decode)
  have frame := quiet w a (h.filterMap decode)
  rw [position,List.filterMap_append] at frame
  have empty : suffix.filterMap (ρ ∘ encode) = [] := by
    have lengths := congrArg List.length frame
    cases found : suffix.filterMap (ρ ∘ encode) with
    | nil => rfl
    | cons x xs => simp only [List.length_append,found,List.length_cons] at lengths; omega
  change (h ++ ((runPrefix (action.run w) a (h.filterMap decode)).2.drop
    (h.filterMap decode).length).map encode).filterMap ρ = _
  rw [position]
  simp only [List.drop_left,List.filterMap_append,List.filterMap_map,empty,List.append_nil]

theorem reserve_epoch (kid : KeypairId) : SameView Packets.epoch (Nonce.reserveNative kid) :=
  SameView.bind (PacketOrigins.epoch_ring (TxRing.getKeypair_frame kid)) (fun key =>
    SameView.bind (key_write_epoch kid _) (fun _ => SameView.pure _ key.sendingCounter))

theorem reserve_staged (kid : KeypairId) : SameView stagedAt (Nonce.reserveNative kid) :=
  SameView.bind (Exact.read_key kid) (fun key =>
    SameView.bind (set_key_staged kid _) (fun _ => SameView.pure _ key.sendingCounter))

theorem reserve_erases (kid : KeypairId) :
    ErasesStatePrefix (state (Journal.reserve kid)) (Nonce.reserveNative kid) :=
  focusStatePrefix_erases _ _ (receiptWGObserved_erases
    (focusStatePrefix_erases _ _ (Nonce.reserveObserved_erases kid)) _)

theorem reserve_observed (kid : KeypairId) :
    StatePrefixPreserves (Held pid peer) Safe (state (Journal.reserve kid)) := by
  have native (h) : Preserves (Inv h) (Nonce.reserveNative kid) :=
    frame (reserve_epoch kid) (Staged.of_view _ (reserve_staged kid))
  apply StateSafe.saved (state_quiet (StateAppends.focus _ _ _) ?_ (reserve_erases kid) native)
    (reserve_erases kid) (reserve_epoch kid) (reserve_staged kid)
  apply focused_history_frame _ _ selection? _
    ((StateAppends.focus _ _ _).receiptWGObserved _)
  exact StateHistoryFrame.receiptWGObserved
    (fun w => focusPrefix_other _ _ _ (fun _ => rfl) ((Nonce.reserveObserved kid).run w)) _ (fun _ => rfl)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
