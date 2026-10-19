import Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntryScheduler
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryConfiguration
import Leanux.Proofs.WG.TransmitSecurity.DriverLifecycleHistory

/-! Native timer, configuration and lifecycle actors preserve the replay
entry invariant; only their actual quiet source histories are used. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Keypairs TransmitSecurity HandshakeSecurity

theorem timer_erases (pid : PeerId) (timer : PeerTimer) :
    ErasesStatePrefix (Driver.timerObserved hooks pid timer) (timerCallback pid timer) := by
  apply state_native_result (Driver.timer_projects native_projects pid timer)
    (Driver.timer_projects NativeDriver.nonce_projection pid timer)
  rw [Driver.nonce_timerObserved_eq]
  exact Nonce.timerObserved_erases pid timer

theorem timer (pid : PeerId) (kind : PeerTimer) : StateSafe (Driver.timerObserved hooks pid kind) := by
  apply state_observed _ _ (timer_erases pid kind) _ (EnvFrames.timerCallback_ordinary pid kind)
  change Driver.StateHistorySafe Safe (Driver.timerObserved quietHooks pid kind)
  exact Driver.timer_history (quiet_history Safe).core pid kind

theorem config_erases (attrs : DeviceAttrs) :
    ErasesStatePrefix (Driver.configDevice hooks attrs) (wgSetDevice attrs) := by
  apply state_native_result (Driver.configDevice_projects native_projects attrs)
    (Driver.configDevice_projects NativeDriver.nonce_projection attrs)
  rw [Driver.nonce_configDevice_eq]
  exact Nonce.configDevice_erases attrs

theorem config (attrs : DeviceAttrs) : StateSafe (Driver.configDevice hooks attrs) := by
  apply state_observed _ _ (config_erases attrs) _ (WGConfig.wgSetDevice_ordinary attrs)
  change Driver.StateHistorySafe Safe (Driver.configDevice quietHooks attrs)
  exact Driver.configDevice_history (quiet_history Safe).actors attrs

theorem envUp_erases : ErasesPrefix (Driver.envUpObserved hooks) Env.wgUp := by
  apply product_native_result (Driver.envUp_projects native_projects)
    (Driver.envUp_projects NativeDriver.nonce_projection)
  rw [Driver.nonce_envUpObserved_eq]
  exact Nonce.envUpObserved_erases

theorem envUp : ProductSafe (Driver.envUpObserved hooks) := by
  apply product_observed _ _ envUp_erases _ EnvFrames.wgUp_ordinary
  change Driver.ProductHistorySafe Safe (Driver.envUpObserved quietHooks)
  exact Driver.envUp_history (quiet_history Safe).actors

theorem envDown : ProductSafe (Driver.envDownObserved hooks) := by
  rw [Driver.envDown_lift hooks rfl rfl]
  exact product_native _ EnvFrames.wgDown_ordinary

theorem envDelete : ProductSafe (Driver.envDeleteObserved hooks) := by
  rw [Driver.envDelete_lift hooks rfl rfl rfl]
  exact product_native _ EnvFrames.wgDelete_ordinary

theorem send_worker : ProductSafe (Driver.sendWorkerObserved hooks) := by
  rw [Driver.sendWorker_lift hooks rfl]
  exact product_same _ EnvFrames.runOneSendWorker_sameSnapshot

end Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
