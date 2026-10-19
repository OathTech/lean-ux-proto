import Leanux.Proofs.Framing.WGReceiveHeaders
import Leanux.Proofs.WG.CounterWindow.Refinement

/-! Native header acceptance fixes the lengths later used in cookie reply
amplification bounds. Queue lineage and the actual cookie occurrence are
separate obligations; a message type alone does not establish its length. -/
namespace Leanux.Proofs.WG.TransmitSecurity.HeaderLength
open Leanux Leanux.WG Leanux.Proofs.Framing
set_option maxHeartbeats 600000

def Valid (msg : List UInt8) : Prop :=
  (messageType msg = MESSAGE_HANDSHAKE_INITIATION → msg.length = 148) ∧
  (messageType msg = MESSAGE_HANDSHAKE_RESPONSE → msg.length = 92) ∧
  (messageType msg = MESSAGE_HANDSHAKE_COOKIE → msg.length = 64)

/-- A nonzero native header-length result has exact handshake widths. -/
theorem validate (msg : List UInt8) (w v : WGWorld) (a b : Ambient) (n : Nat)
    (run : ((validateHeaderLen msg).run w).run a = .ok ((n,v),b))
    (positive : n ≠ 0) : Valid msg := by
  refine ⟨?_,?_,?_⟩
  all_goals intro kind
  all_goals by_cases short : msg.length < 4
  all_goals simp [validateHeaderLen, WG.andM, StateT.run_bind, branch,
    CounterWindow.branch_run, MESSAGE_DATA, MESSAGE_HANDSHAKE_INITIATION,
    MESSAGE_HANDSHAKE_RESPONSE, MESSAGE_HANDSHAKE_COOKIE, kind, short] at run
  all_goals try exact (positive run.1.1.symm).elim
  all_goals split at run <;> simp_all

private theorem bind_ok {first : Except Stop α} {next : α → Except Stop β}
    {value : β} (run : (first >>= next) = .ok value) :
    ∃ x, first = .ok x ∧ next x = .ok value := by
  cases first with
  | error stop => cases run
  | ok x => exact ⟨x,rfl,run⟩

/-- Successful native header preparation admits only the declared handshake
widths; neither a type tag nor a cookie-MAC receipt substitutes for this check. -/
theorem prepared (msg : List UInt8) (w v : WGWorld) (a b : Ambient)
    (run : ((prepareSkbHeader msg).run w).run a = .ok ((true,v),b)) : Valid msg := by
  unfold prepareSkbHeader at run
  simp only [WG.andM, WG.orM, StateT.run_bind, branch] at run
  by_cases short : msg.length < 4
  · simp [short] at run
  · simp [short] at run
    obtain ⟨⟨⟨n,u⟩,c⟩,same,tail⟩ := bind_ok run
    by_cases zero : n = 0
    · simp [zero] at tail
    · exact validate msg w u _ c n same zero

theorem prepared_spec (msg : List UInt8) :
    Hoare (prepareSkbHeader msg) (fun _ => True)
      (fun accepted _ => accepted = true → Valid msg) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a accepted v b _ run yes
  subst accepted
  exact prepared msg w v a b run

/-- A validated initiation or response is strictly larger than a cookie reply. -/
theorem larger_than_cookie (valid : Valid msg)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨
      messageType msg = MESSAGE_HANDSHAKE_RESPONSE) : 64 < msg.length := by
  rcases kind with initiation | response
  · rw [valid.1 initiation]
    omega
  · rw [valid.2.1 response]
    omega

end Leanux.Proofs.WG.TransmitSecurity.HeaderLength
