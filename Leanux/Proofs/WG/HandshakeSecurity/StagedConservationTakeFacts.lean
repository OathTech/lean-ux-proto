import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationTakeSource
import Leanux.Proofs.WG.Origins.SessionMaterial

/-! Exact native queue-to-caller transfer before borrowing. The peer allocation
and device epoch come from the actual read; no reachability assumption supplies
them. Later borrowing can stop without erasing this completed transfer. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Take
open Leanux Leanux.WG Leanux.Proofs.Logged MaterialOrigin

/-- A nonempty native take clears exactly its resident peer queue and returns
that entire original peer record, retaining its allocation and packet order. -/
theorem take_some (pid : PeerId) (w v : WGWorld) (a b : Ambient) (p : Peer)
    (run : ((takePrefix pid).run w).run a = .ok ((some p,v),b)) :
    ∃ d, w.dev = some d ∧ d.peers[pid]? = some p ∧ p.staged.isEmpty = false ∧
      v = {w with dev := some {d with peers := d.peers.insert pid {p with staged := []}}} ∧
      b = CounterWindow.record a .stagedEmpty false := by
  unfold takePrefix at run
  rw [bind_ok_ambient] at run
  obtain ⟨original,u,c,read,tail⟩ := run
  obtain ⟨sameWorld,sameAmbient,d,device,resident⟩ :=
    Leanux.Proofs.WG.Origins.getPeer_return pid w u original a c read
  subst u c
  rw [bind_ok_ambient] at tail
  obtain ⟨empty,u,c,tested,tail⟩ := tail
  have actual : ((branch .stagedEmpty original.staged.isEmpty : WG.M Bool).run w).run a =
      .ok ((original.staged.isEmpty,w),CounterWindow.record a .stagedEmpty original.staged.isEmpty) := rfl
  rw [actual] at tested
  cases tested
  cases empty : original.staged.isEmpty with
  | true => simp [empty] at tail
  | false =>
    simp only [empty,Bool.false_eq_true,ite_false] at tail
    rw [bind_ok_ambient] at tail
    obtain ⟨ignored,u,c,written,tail⟩ := tail
    cases ignored
    have write : u = {w with dev := some {d with peers := d.peers.insert pid {original with staged := []}}} ∧
        c = CounterWindow.record a .stagedEmpty false := by
      simpa [setPeer,modifyDev,device] using written.symm
    rcases write with ⟨rfl,rfl⟩
    simp only [StateT.run_pure,CounterWindow.except_pure,Except.ok.injEq,
      Prod.mk.injEq,Option.some.injEq] at tail
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := tail
    exact ⟨d,device,resident,empty,rfl,rfl⟩

/-- An empty native take leaves the full WireGuard world unchanged. -/
theorem take_none (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (run : ((takePrefix pid).run w).run a = .ok ((none,v),b)) :
    ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧ p.staged.isEmpty = true ∧
      v = w ∧ b = CounterWindow.record a .stagedEmpty true := by
  unfold takePrefix at run
  rw [bind_ok_ambient] at run
  obtain ⟨p,u,c,read,tail⟩ := run
  obtain ⟨sameWorld,sameAmbient,d,device,resident⟩ :=
    Leanux.Proofs.WG.Origins.getPeer_return pid w u p a c read
  subst u c
  rw [bind_ok_ambient] at tail
  obtain ⟨empty,u,c,tested,tail⟩ := tail
  have actual : ((branch .stagedEmpty p.staged.isEmpty : WG.M Bool).run w).run a =
      .ok ((p.staged.isEmpty,w),CounterWindow.record a .stagedEmpty p.staged.isEmpty) := rfl
  rw [actual] at tested
  cases tested
  cases empty : p.staged.isEmpty with
  | true =>
    simp only [empty,ite_true,StateT.run_pure,CounterWindow.except_pure,
      Except.ok.injEq,Prod.mk.injEq] at tail
    obtain ⟨⟨_,rfl⟩,rfl⟩ := tail
    exact ⟨d,p,device,resident,empty,rfl,rfl⟩
  | false =>
    simp only [empty,Bool.false_eq_true,ite_false] at tail
    rw [bind_ok_ambient] at tail
    obtain ⟨ignored,u,c,written,tail⟩ := tail
    simp [StateT.run_pure] at tail

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Take
