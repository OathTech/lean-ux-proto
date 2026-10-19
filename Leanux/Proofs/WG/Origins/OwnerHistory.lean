import Leanux.Proofs.WG.Origins.OwnerCreation
import Leanux.Proofs.WG.Origins.CurrentChecks

/-! Owner bounds accompany the existing session and peer-allocation observers.
The journal and allocation contracts refer to the same actual invocation. These
are propagation rules; they do not assert an initialized whole-program closure. -/
namespace Leanux.Proofs.WG.OwnerHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

/-- Session receipts update current support while the receiving-owner carrier
survives the same native execution. Stop outcomes retain the existing checks. -/
theorem session (pid : PeerId) :
    PrefixPreserves
      (fun h w => CurrentChecks.Inv h w ∧ OwnerBounds.Carrier w.wg)
      CurrentChecks.Safe (Origins.HistoryAdapters.session pid) := by
  intro w h hi
  obtain ⟨suffix, append, safe, post⟩ := CurrentChecks.session pid w h hi.1
  refine ⟨suffix, append, safe, ?_⟩
  cases hr : (runPrefix (Origins.HistoryAdapters.session pid) w h).1 with
  | error e => trivial
  | ok out =>
    rw [hr] at post
    have native := (Origins.HistoryAdapters.session_erases pid w h).symm.trans hr
    rw [liftWG_run] at native
    cases hs : ((beginSession pid).run w.wg).run w.ambient with
    | error e => simp [hs, Except.map] at native
    | ok endpoint =>
      rcases endpoint with ⟨⟨result, v⟩, ambient⟩
      simp only [hs, Except.map, Except.ok.injEq] at native
      cases native
      have carrier := (hoare_iff_run_ambient _ _ _).mp
        (OwnerCreation.beginSession_preserves pid)
        w.wg w.ambient result v ambient ⟨hi.1.2.1.1, hi.2⟩ hs
      exact ⟨post, carrier.2⟩

/-- The lifetime observer supplies its original allocation invariant and safe
partial journal, alongside current identity and the owner carrier. -/
theorem peerCreateMixed (key : Key) (psk : Option Key)
    (history : List SessionOrigin.Receipt) :
    StatePrefixPreserves
      (fun h w _ => AllocationInv h w ∧ CurrentLifecycle.Inv history w ∧ OwnerBounds.Carrier w)
      LifetimeEvent.Safe (Lifetimes.peerCreateMixed key psk) := by
  intro w ambient h hi
  obtain ⟨suffix, append, safe, post⟩ := peerCreateMixed_preserves key psk w ambient h hi.1
  refine ⟨suffix, append, safe, ?_⟩
  cases hr : (runPrefix ((Lifetimes.peerCreateMixed key psk).run w) ambient h).1 with
  | error e => trivial
  | ok out =>
    rcases out with ⟨⟨result, v⟩, finalAmbient⟩
    rw [hr] at post
    have native := (peerCreateMixed_erases key psk w ambient h).symm.trans hr
    exact ⟨post, (hoare_iff_run_ambient _ _ _).mp
      (OwnerCreation.peerCreate_current key psk history)
      w ambient result v finalAmbient hi.2 native⟩

/-- Product callers use the canonical adapter around the unchanged native
allocation observer, retaining the complete product execution endpoints. -/
theorem peerCreateProduct (key : Key) (psk : Option Key)
    (history : List SessionOrigin.Receipt) :
    PrefixPreserves
      (fun h w => AllocationInv h w.wg ∧ CurrentLifecycle.Inv history w.wg ∧
        OwnerBounds.Carrier w.wg)
      LifetimeEvent.Safe (liftWGObserver (Lifetimes.peerCreateMixed key psk)) := by
  exact (peerCreateMixed key psk history).liftWGObserver

end Leanux.Proofs.WG.OwnerHistory
