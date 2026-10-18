import Leanux.Proofs.WG.Index.ResponseIndexSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

/-- Normal response sending retains the complete index package from current
slot/store bounds and nullable caller compatibility. The native reached-cut
adapter derives those conditions from its actual charged stamped loan. -/
theorem sendHandshakeResponse_indexCore (pid : PeerId) :
    Campaign2.Ensures (sendHandshakeResponse pid)
      (fun s => InitializedBounds.EndpointSafe s ∧ View.IndexCore s ∧ View.HandshakeCompatibleSafe pid s)
      (fun _ s => View.IndexCore s) := by
  intro w a result v b pre run
  have state := sendHandshakeResponse_indexState pid w a result v b
    ⟨pre.1,pre.2.2,fun d device => (pre.2.1 d device).2.1,
      fun d device => (pre.2.1 d device).2.2.2⟩ run
  have tables := sendHandshakeResponse_tables pid w a result v b
    (fun d device => (pre.2.1 d device).1) run
  exact fun d device => ⟨tables d device,(state d device).1,(state d device).2⟩

end Leanux.Proofs.WG.Index
