import Leanux.Proofs.WG.Noise.PendingOuterSource
import Leanux.Proofs.WG.Noise.PendingTrafficSource
import Leanux.Proofs.WG.Noise.PendingDeviceConfigurationSource
import Leanux.Proofs.WG.Lifetimes.DispatchSource
import Leanux.Proofs.WG.Lifetimes.TxCallFocus
import Leanux.Proofs.WG.Noise.PendingEnvironmentSource
import Leanux.Proofs.WG.Noise.PendingDumpSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingSyscalls
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Configuration PendingSession PendingOuter

theorem scalar_native (w v : World) (seen : List Nat)
    (same : envScalarView v = envScalarView w) (hi : NativeInv w.wg seen) :
    NativeInv v.wg seen := by
  have hd := congrArg (fun s : ProductStore43 => s.2.2.2.dev) same
  have hk := congrArg (fun s : ProductStore43 => s.2.2.2.keypairCounter) same
  change v.wg.dev.map envScalarDevice = w.wg.dev.map envScalarDevice at hd
  change v.wg.keypairCounter = w.wg.keypairCounter at hk
  have cfg := congrArg (fun x => x.map ConfiguredIdentity.state) hd
  have slots := congrArg (fun x => x.map Affiliation.state) hd
  have next := congrArg (fun x => fun p => x.bind (fun d => PendingTickets.pending d p)) hd
  simp only [Option.map_map, Function.comp_def, ConfiguredIdentity.state, envScalarDevice] at cfg
  simp only [Option.map_map, Function.comp_def, Affiliation.state, envScalarDevice] at slots
  simp only [Option.bind_map, Function.comp_def, PendingTickets.pending, envScalarDevice] at next
  have cp : ConfiguredIdentity.view v.wg = ConfiguredIdentity.view w.wg := cfg
  have sp : Affiliation.view v.wg = Affiliation.view w.wg := slots
  have pp : PendingTickets.view v.wg = PendingTickets.view w.wg := by
    apply Store.ext
    · exact hk
    · exact next
  exact ⟨fun s hs => hi.1 s (cp.symm.trans hs),
    fun s hs => hi.2.1 s (sp.symm.trans hs), by simpa only [pp] using hi.2.2⟩


end Leanux.Proofs.WG.Noise.PendingSyscalls
