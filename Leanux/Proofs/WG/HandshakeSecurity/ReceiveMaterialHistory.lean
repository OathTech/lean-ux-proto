import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialConfirmationEntry
import Leanux.Proofs.WG.TransmitSecurity.JournalSource

/-! Positional confirmation certificates identify the earlier decrypting
allocation. The native resident read discharges conditional residency; this
history property is separate from its initialized source transport. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Confirmation
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AuthenticatedEffects Responder TransmitSecurity

def Checked (pre : List Journal.Event) (event : Journal.Event) : Prop :=
  ∀ pid kid r, Journal.responder? event = some (.confirmed pid kid r) →
    r.Valid (receivedWithKeypair pid kid) ∧
    ∀ core, pool r.before kid = some core →
      ∃ earlier counter, pre = earlier ++ [Journal.Event.replay counter] ∧
        counter.packet.peer = pid ∧ counter.packet.keypair = kid ∧ counter.run.value = true ∧
        Replay.Certified (earlier.filterMap Journal.origin?) counter ∧
        Certificate (earlier.filterMap Journal.origin?) counter.skb counter.packet r.before core

def Safe (history : List Journal.Event) : Prop :=
  ∀ pre event post, history = pre ++ event :: post → Checked pre event

theorem Safe.append (before : Safe h)
    (next : ∀ pre event post, suffix = pre ++ event :: post → Checked (h ++ pre) event) :
    Safe (h ++ suffix) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    Checked h suffix before next

theorem Safe.quiet (before : Safe h)
    (quiet : ∀ event ∈ suffix, ∀ pid kid r,
      Journal.responder? event ≠ some (.confirmed pid kid r)) : Safe (h ++ suffix) := by
  apply before.append
  intro pre event post position pid kid r recorded
  exact False.elim (quiet event (by rw [position]; simp) pid kid r recorded)

theorem Safe.empty : Safe [] := by
  intro pre event post position
  have length := congrArg List.length position
  simp only [List.length_nil,List.length_append,List.length_cons] at length
  omega

theorem at_entry (input : Replay.ConfirmationInput Journal.origin? Journal.replay?
      Journal.Event.replay pid kid h w)
    (r : WGRunWitness Bool) (before : r.before = w.wg)
    (valid : r.Valid (receivedWithKeypair pid kid)) :
    Checked h (.responder (.confirmed pid kid r)) := by
  intro actualPid actualKid actual recorded
  have equal : (.confirmed pid kid r : DriverCuts.Event) = .confirmed actualPid actualKid actual :=
    Option.some.inj recorded
  cases equal
  refine ⟨valid,?_⟩
  intro core resident
  simpa only [before] using Replay.confirmation_input_material input (fun _ => rfl)
    (before ▸ resident)

theorem append_confirmation (history : Safe h)
    (input : Replay.ConfirmationInput Journal.origin? Journal.replay?
      Journal.Event.replay pid kid h w)
    (r : WGRunWitness Bool) (before : r.before = w.wg)
    (valid : r.Valid (receivedWithKeypair pid kid)) :
    Safe (h ++ [.responder (.confirmed pid kid r)]) := by
  apply history.append
  intro pre event post position
  cases pre with
  | nil =>
    cases position
    simpa only [List.append_nil] using at_entry input r before valid
  | cons e es =>
    have length := congrArg List.length position
    simp only [List.length_append,List.length_cons,List.length_nil] at length
    omega

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Confirmation
