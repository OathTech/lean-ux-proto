import Leanux.Proofs.WG.TimerDiscipline.HookJournalModel
import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.WG.Handshake

/-! Native source linkage for projected hook receipts. Validity describes the named hook at its actual entry; it does not certify an arbitrary caller context or global invocation coverage. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookJournal
open Leanux Leanux.WG

def action : Hook → PeerId → WG.M Unit
  | .handshakeInitiated => timersHandshakeInitiated
  | .dataSent => timersDataSent
  | .dataReceived => timersDataReceived
  | .authenticatedSent => timersAnyAuthenticatedPacketSent
  | .authenticatedReceived => timersAnyAuthenticatedPacketReceived
  | .handshakeComplete site => fun pid => timersHandshakeComplete pid site
  | .sessionDerived => timersSessionDerived
  | .traversal => timersTraversal

def Receipt.Valid (r : Receipt) : Prop :=
  ∃ g ambient, r.before = Campaign2.snapshot g ambient ∧
    r.outcome = Campaign2.observeResult (((action r.hook r.pid).run g).run ambient)

def ValidHistory (history : List Receipt) : Prop :=
  ∀ r ∈ history, r.Valid

theorem fresh_valid (hook : Hook) (pid : PeerId) (g : WGWorld) (ambient : Ambient) :
    (⟨hook,pid,Campaign2.snapshot g ambient,
      Campaign2.observeResult (((action hook pid).run g).run ambient)⟩ : Receipt).Valid :=
  ⟨g,ambient,rfl,rfl⟩

theorem ValidHistory.snoc {history : List Receipt} {r : Receipt}
    (prior : ValidHistory history) (valid : r.Valid) : ValidHistory (history ++ [r]) := by
  intro x member
  rcases List.mem_append.mp member with old | added
  · exact prior x old
  · simp only [List.mem_singleton] at added
    subst x
    exact valid

theorem Receipt.Valid.ensures {r : Receipt} (valid : r.Valid)
    {P : Campaign2.Snapshot → Prop} {Q : Unit → Campaign2.Snapshot → Prop}
    (contract : Campaign2.Ensures (action r.hook r.pid) P Q)
    (pre : P r.before) {after : Campaign2.Snapshot}
    (normal : r.outcome = .ok ((),after)) : Q () after := by
  obtain ⟨g,ambient,before,outcome⟩ := valid
  rw [before] at pre
  rw [outcome] at normal
  cases run : ((action r.hook r.pid).run g).run ambient with
  | error stop => simp [Campaign2.observeResult,run,Except.map] at normal
  | ok out =>
    obtain ⟨⟨u,final⟩,inputs⟩ := out
    cases u
    simp only [Campaign2.observeResult,run,Except.map,Except.ok.injEq,Prod.mk.injEq,
      true_and] at normal
    subst after
    exact contract g ambient () final inputs pre run

end Leanux.Proofs.WG.TimerDiscipline.HookJournal
