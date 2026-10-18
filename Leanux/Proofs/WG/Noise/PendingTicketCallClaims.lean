import Leanux.Proofs.WG.Noise.PendingTicketCallFrames
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Original session and confirmation calls act on allocation identities.
These projected contracts supply transition leaves for a whole-run history. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes

def projected (s : Campaign2.Snapshot) : Store PeerId :=
  ⟨s.wg.keypairCounter, fun pid => s.wg.device.bind fun d => pending d pid⟩

def NextBounds (s : Campaign2.Snapshot) : Prop :=
  ∀ d, s.wg.device = some d → NextBound d

/-- Every normal session call either retains pending identities, advances the
allocation frontier, or installs its fresh responder identity. -/
theorem session_step (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (beginSession pid) (fun s => s = entry ∧ NextBounds s)
      (fun _ final => Step (projected entry) none (projected final)) := by
  intro g ambient ok final after pre run
  rcases pre with ⟨rfl,bounds⟩
  cases device : g.dev with
  | none =>
    simp [beginSession,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases peer : d.peers[pid]? with
    | none =>
      simp [beginSession,getPeer,getDev,device,peer,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨out,hout,effect⟩ := beginSession_effect pid d p g.keypairCounter peer
        g ambient ok final after ⟨device,rfl⟩ run
      have step := session_pending pid g.keypairCounter final.keypairCounter d out p ok
        peer (bounds d device) effect
      simpa [projected,Campaign2.snapshot,Campaign2.core,deviceView,device,hout] using step

/-- A resident received key labels the actual successful promotion by its
allocation identity; a false return emits no confirmation. -/
theorem confirmation_step (pid received : Nat) (d : Device) (p : Peer) (k : Keypair)
    (entry : Campaign2.Snapshot) (device : entry.wg.device = some d)
    (peer : d.peers[pid]? = some p) (key : d.keypairs[received]? = some k) :
    Campaign2.Ensures (receivedWithKeypair pid received) (fun s => s = entry)
      (fun ok final => Step (projected entry)
        (if ok then some k.internalId else none) (projected final)) := by
  intro g ambient ok final after pre run
  subst entry
  change g.dev = some d at device
  have step := receivedWithKeypair_step pid received g.keypairCounter d p k peer key
    g ambient ok final after ⟨device,rfl⟩ run
  simpa [projected,Campaign2.snapshot,Campaign2.core,deviceView,view,device] using step

/-- The session call preserves the global history invariant without adding a
confirmation; no claim that the whole driver supplies the invariant is made. -/
theorem session_history (pid : PeerId) (entry : Campaign2.Snapshot) (seen : List Nat)
    (history : Inv (projected entry) seen) :
    Campaign2.Ensures (beginSession pid) (fun s => s = entry ∧ NextBounds s)
      (fun _ final => Inv (projected final) seen) := by
  intro g ambient ok final after pre run
  exact (session_step pid entry g ambient ok final after pre run).preserves history

/-- Actual confirmation extends a supplied valid history with a fresh
allocation stamp exactly when the original helper returns true. -/
theorem confirmation_history (pid received : Nat) (d : Device) (p : Peer) (k : Keypair)
    (entry : Campaign2.Snapshot) (device : entry.wg.device = some d)
    (peer : d.peers[pid]? = some p) (key : d.keypairs[received]? = some k)
    (seen : List Nat) (history : Inv (projected entry) seen) :
    Campaign2.Ensures (receivedWithKeypair pid received) (fun s => s = entry)
      (fun ok final => Inv (projected final)
        (if ok then k.internalId :: seen else seen)) := by
  intro g ambient ok final after pre run
  have next := (confirmation_step pid received d p k entry device peer key
    g ambient ok final after pre run).preserves history
  cases ok <;> exact next

end Leanux.Proofs.WG.Noise.PendingTickets
