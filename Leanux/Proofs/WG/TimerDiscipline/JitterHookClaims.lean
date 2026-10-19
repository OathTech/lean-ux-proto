import Leanux.Proofs.WG.TimerDiscipline.JitterHookSource
import Leanux.Proofs.WG.TimerDiscipline.HookJournalClaims

/-! The two jittered hook families now have their complete normal wheel effects
in either input mode. These are invocation-local claims, with original Stops. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookJournal
open Leanux Leanux.WG

theorem Receipt.Valid.handshakeInitiated {r : Receipt} (valid : r.Valid)
    (kind : r.hook = .handshakeInitiated) (d : Device) (p : Peer)
    (device : r.before.wg.device = some d) (resident : d.peers[r.pid]? = some p)
    {after : Campaign2.Snapshot} (normal : r.outcome = .ok ((),after)) :
    ∃ jitter, jitter < HZ / 3 ∧
      if d.running && !p.isDead then
        peerTimerArmEffect r.before r.pid p .retransmitHandshake (REKEY_TIMEOUT_TICKS+jitter) after.wg
      else after.wg=r.before.wg := by
  apply valid.ensures (P:=fun s=>s=r.before ∧ s.wg.device=some d)
    (Q:=fun _ final=>∃jitter,jitter < HZ/3 ∧
      if d.running && !p.isDead then
        peerTimerArmEffect r.before r.pid p .retransmitHandshake (REKEY_TIMEOUT_TICKS+jitter) final.wg
      else final.wg=r.before.wg) ?_ ⟨rfl,device⟩ normal
  simpa only [kind,action] using handshakeInitiated_effect r.pid d p resident r.before

theorem Receipt.Valid.dataSent {r : Receipt} (valid : r.Valid)
    (kind : r.hook = .dataSent) (d : Device) (p : Peer)
    (device : r.before.wg.device = some d) (resident : d.peers[r.pid]? = some p)
    {after : Campaign2.Snapshot} (normal : r.outcome = .ok ((),after)) :
    if p.timerPending .newHandshake then after.wg=r.before.wg
    else ∃jitter,jitter < HZ/3 ∧
      if d.running && !p.isDead then
        peerTimerArmEffect r.before r.pid p .newHandshake
          (KEEPALIVE_TIMEOUT_TICKS+REKEY_TIMEOUT_TICKS+jitter) after.wg
      else after.wg=r.before.wg := by
  apply valid.ensures (P:=fun s=>s=r.before ∧ s.wg.device=some d)
    (Q:=fun _ final=>if p.timerPending .newHandshake then final.wg=r.before.wg
      else ∃jitter,jitter < HZ/3 ∧
        if d.running && !p.isDead then
          peerTimerArmEffect r.before r.pid p .newHandshake
            (KEEPALIVE_TIMEOUT_TICKS+REKEY_TIMEOUT_TICKS+jitter) final.wg
        else final.wg=r.before.wg) ?_ ⟨rfl,device⟩ normal
  simpa only [kind,action] using dataSent_effect r.pid d p resident r.before

end Leanux.Proofs.WG.TimerDiscipline.HookJournal
