import Leanux.Proofs.Framing.Tools
import Leanux.WG.Receive

/-! Original byte/header inspection leaves preserve the native WG world.
Their branch records and Stops retain unrestricted Ambient inputs and outputs. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

theorem validateHeaderLen_sameWGWorld (msg : List UInt8) :
    SameView (id : WGWorld → WGWorld) (validateHeaderLen msg) := by
  apply SameView.of_wp
  intro initial
  mvcgen [validateHeaderLen, WG.andM, branch, AmbientM.branch]

theorem prepareSkbHeader_sameWGWorld (msg : List UInt8) :
    SameView (id : WGWorld → WGWorld) (prepareSkbHeader msg) := by
  apply SameView.of_wp
  intro initial
  have hh := (validateHeaderLen_sameWGWorld msg).wp (fun s => s = initial)
  mvcgen [prepareSkbHeader, WG.andM, WG.orM, branch, AmbientM.branch, hh]

theorem ipTunnelGetDsfield_sameWGWorld (protocol : Nat) (hdr : List UInt8) :
    SameView (id : WGWorld → WGWorld) (ipTunnelGetDsfield protocol hdr) := by
  apply SameView.of_wp
  intro initial
  mvcgen [ipTunnelGetDsfield, branch, AmbientM.branch, unsupported, AmbientM.unsupported]

end Leanux.Proofs.Framing
