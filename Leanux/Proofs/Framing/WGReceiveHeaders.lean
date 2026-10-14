import Leanux.Proofs.Framing.Tools
import Leanux.WG.Receive

/-! Original byte/header inspection leaves. Source inspection establishes
that their only effects are branch records or Stops, with no resident-object
access. These stronger frames are the canonical proofs for legacy projections. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

theorem validateHeaderLen_sameKernel (msg : List UInt8) : SameKernel (validateHeaderLen msg) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [validateHeaderLen, WG.andM, branch]

theorem prepareSkbHeader_sameKernel (msg : List UInt8) : SameKernel (prepareSkbHeader msg) := by
  apply sameKernel_of_wp
  intro k
  have hh := sameKernel_wp _ (validateHeaderLen_sameKernel msg) (fun s => s = k)
  mvcgen [prepareSkbHeader, WG.andM, WG.orM, branch, hh]

theorem ipTunnelGetDsfield_sameKernel (protocol : Nat) (hdr : List UInt8) :
    SameKernel (ipTunnelGetDsfield protocol hdr) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [ipTunnelGetDsfield, branch, unsupported]

end Leanux.Proofs.Framing
