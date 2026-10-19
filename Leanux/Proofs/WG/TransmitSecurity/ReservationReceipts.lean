import Leanux.Proofs.WG.TransmitSecurity.JournalSource

/-! Native reservation receipts identify the exact resident key allocation
and old sending counter before its increment. Rejection happens afterwards. -/
namespace Leanux.Proofs.WG.TransmitSecurity.ReservationReceipts
open Leanux Leanux.WG Leanux.Proofs.Logged CounterWindow

/-- A completed reservation reads one actual resident key and returns its old
counter while preserving the allocation identity in the updated key cell. -/
theorem native (slot : KeypairId) (r : WGRunWitness Nat)
    (valid : r.Valid (Nonce.reserveNative slot)) :
    ∃ d k, r.before.dev = some d ∧ d.keypairs[slot]? = some k ∧
      r.value = k.sendingCounter ∧
      r.after = store r.before slot {k with sendingCounter := k.sendingCounter + 1} ∧
      r.ambientAfter = r.ambientBefore := by
  rcases r with ⟨value,w,v,a,b⟩
  change ((Nonce.reserveNative slot).run w).run a = .ok ((value,v),b) at valid
  cases device : w.dev with
  | none =>
    simp [Nonce.reserveNative,getKeypair,getDev,device,invariant,AmbientM.invariant] at valid
    cases valid
  | some d =>
    cases key : d.keypairs[slot]? with
    | none =>
      simp [Nonce.reserveNative,getKeypair,getDev,device,key,invariant,AmbientM.invariant] at valid
      cases valid
    | some k =>
      rw [Nonce.reserveNative_run w a d slot k device key] at valid
      cases valid
      exact ⟨d,k,rfl,key,rfl,rfl,rfl⟩

/-- The token used for non-reuse is the key allocation stamp with its reserved
counter, rather than a numeric key slot that can be reused after destruction. -/
def Token (slot : KeypairId) (r : WGRunWitness Nat) (token : Nonce.Allocation) : Prop :=
  r.Valid (Nonce.reserveNative slot) ∧
  ∃ d k, r.before.dev = some d ∧ d.keypairs[slot]? = some k ∧
    token = Nonce.allocation (Nonce.cell k) ∧ token.nonce = r.value

theorem token (slot : KeypairId) (r : WGRunWitness Nat)
    (valid : r.Valid (Nonce.reserveNative slot)) : ∃ token, Token slot r token := by
  obtain ⟨d,k,device,key,value,_,_⟩ := native slot r valid
  refine ⟨Nonce.allocation (Nonce.cell k),valid,d,k,device,key,rfl,?_⟩
  exact value.symm

/-- The focused native observer records the token of the same completed
reservation before its receipt is added to the shared journal. -/
theorem observed (slot : KeypairId) (r : WGRunWitness Nat)
    (valid : r.Valid (Nonce.reserveNative slot)) (h : List Journal.Event) :
    ∃ token, Token slot r token ∧
      runWGPrefix (focusStatePrefix Journal.Event.nonce Journal.nonce? (Nonce.reserveObserved slot))
        r.before r.ambientBefore h =
      (.ok ((r.value,r.after),r.ambientAfter),h ++ [.nonce token]) := by
  obtain ⟨d,k,device,key,value,after,ambient⟩ := native slot r valid
  refine ⟨Nonce.allocation (Nonce.cell k),⟨valid,d,k,device,key,rfl,value.symm⟩,?_⟩
  have localRun := Nonce.reserveObserved_run r.before r.ambientBefore d slot k device key
    (h.filterMap Journal.nonce?)
  have focused := focusPrefix_suffix Journal.Event.nonce Journal.nonce?
    ((Nonce.reserveObserved slot).run r.before) r.ambientBefore h _ [_] localRun
  simpa only [runWGPrefix,runStatePrefix,focusStatePrefix,StateT.run,List.map_cons,List.map_nil,
    value,after,ambient] using focused

end Leanux.Proofs.WG.TransmitSecurity.ReservationReceipts
