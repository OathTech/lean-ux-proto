import Leanux.Proofs.WG.RetirementSecurity.TxDestructSource

/-! Actual lifecycle helpers retain suspended records. In particular the
device-unit retirement operation does not clear the suspended list; its absence
at operation boundaries comes from the runner guard, not this cleanup. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem iput (last : Bool) : Keeps (iputReport last : StateT S AmbientM Unit) := by
  apply ambient
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases last <;> cases run <;> rfl

theorem sock_free (sock : Option Nat) : Keeps (sockFree sock) := by
  suspension_source [sockFree] using [branch,iput]

theorem socket_reinit (new4 new6 : Option Nat) : Keeps (socketReinit new4 new6) := by
  suspension_source [socketReinit] using [device,modify_device,branch,invariant,sock_free]

theorem socket_init (port : Nat) : Keeps (socketInit port) := by
  suspension_source [socketInit] using [device,hidden,unsupported,iput,socket_reinit]

theorem reset (pid : PeerId) : Keeps (resetLastSentHandshake pid) := by
  suspension_source [resetLastSentHandshake] using [peer,set_peer,clock]

theorem open_device : Keeps wgOpen := by
  suspension_source [wgOpen] using [device,branch,socket_init,staged,peer,keepalive]

theorem up : Keeps wgUp := by
  suspension_source [wgUp] using [modify_device,open_device]

theorem stop : Keeps wgStop := by
  suspension_source [wgStop,requireNotPending] using
    [device,branch,unsupported,purge,timers_stop,handshake_clear,key_clear,reset,modify_device,socket_reinit]

theorem down : Keeps wgDown := by
  suspension_source [wgDown] using [modify_device,stop]

theorem slept : Keeps mayHaveSlept := by
  suspension_source [mayHaveSlept] using []

theorem gc (work : Bool) : Keeps (gcEntries work) := by
  suspension_source [gcEntries] using [clock_int,branch,unsupported]

theorem limiter_uninit : Keeps ratelimiterUninit := by
  suspension_source [ratelimiterUninit] using [branch,gc,slept,cuts]

theorem retire_device : Keeps retireDeviceUnits := by
  unfold retireDeviceUnits
  repeat' first
    | (suspension_head modifyAmbient; exact modify_ambient _ (fun _=>rfl))
    | suspension_step

theorem destruct : Keeps wgDestruct := by
  suspension_source [wgDestruct] using
    [modify_device,socket_reinit,peer_remove_all,device,unsupported,invariant,slept,limiter_uninit,retire_device]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension
