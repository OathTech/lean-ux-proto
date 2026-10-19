import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionScheduler
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionSend
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryWorkers

/-! Packet scheduling and queued sends retain live emission accounting and
earlier delivery certificates on one execution. The history-only surrogate
is used solely for actors that do not invoke its replaced delivery callback. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries.Carrier
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

theorem flushed_send (pid : PeerId) : StateSafe (hooks.flushedSend pid) :=
  state_combine _ (Emissions.flushed_send pid) (quiet_hooks.flushedSend pid)

theorem send_worker : ProductSafe (Driver.sendWorkerObserved hooks) :=
  product_combine _ Emissions.send_worker quiet_hooks.sendWorker

theorem transmit (pid : PeerId) : ProductSafe (hooks.transmit pid) :=
  product_combine _ (Emissions.transmit pid) (quiet_hooks.transmit pid)

theorem schedule (stack : Option Worker) : ProductSafe (Driver.scheduleObserved hooks stack) :=
  product_combine _ (Emissions.schedule stack)
    (Driver.schedule_history (g := quietHooks) quiet_hooks.actors stack)

theorem run_worker (worker : Worker) (body : PrefixM Event Unit) (safe : ProductSafe body) :
    ProductSafe (runWorkerPrefix worker body) := by
  unfold runWorkerPrefix
  repeat' first
    | exact safe
    | (emission_carrier_head liftPrefix
       apply product_native
       exact Emissions.product_ambient _)
    | emission_carrier_product_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries.Carrier
