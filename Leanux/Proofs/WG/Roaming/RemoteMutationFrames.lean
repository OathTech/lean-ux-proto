import Leanux.Proofs.WG.Roaming.Frames
import Leanux.Proofs.WG.Config.EndpointSources
import Leanux.Proofs.WG.Queues.RxPollPrimitives
import Leanux.Proofs.WG.Keypairs.MaterialOrigin

set_option autoImplicit false

namespace Leanux.Proofs.WG.Roaming.RemoteMutation
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing
open Lifetimes Queues

/-- Clearing the cached local route source preserves every remote destination. -/
theorem clear_source_destinations (pid : PeerId) :
    SameView (fun w : WGWorld => destinationAt w) (clearPeerEndpointSrc pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have readRun := run
  unfold clearPeerEndpointSrc at readRun
  rw [MaterialOrigin.bind_ok_ambient] at readRun
  obtain ⟨p,u,c,read,_⟩ := readRun
  obtain ⟨_,_,d,device,resident⟩ := getPeer_normal pid w u p a c read
  obtain ⟨out,reset,final,_,changed,others⟩ :=
    Config.clearEndpointSource_exact pid d p resident w a result v b device run
  change v.dev = some out at final
  funext target
  by_cases same : target = pid
  · subst target
    cases endpoint : p.endpoint <;>
      simp [destinationAt, peerAt, device, final, resident, changed,
        Config.clearedSource, endpoint, destination]
  · simp only [destinationAt, peerAt, device, final, Option.bind_some, others target same]

end Leanux.Proofs.WG.Roaming.RemoteMutation
