import Leanux.Proofs.WG.Index.TablePreservationSource
import Leanux.Proofs.WG.Index.ResponseFrames
import Leanux.Proofs.WG.Index.SendSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Compose the actual creation, session and send/timer suffix on its original success domain. -/
theorem sendHandshakeResponse_tables (pid : PeerId) : Ensures (sendHandshakeResponse pid)
    TablesSafeWG (fun _ => TablesSafeWG) := by
  have hpure : Ensures (pure () : WG.M Unit) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hread : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g ambient result final after pre run).1
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64)
      TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.hiddenClock64 site) TablesSafeWG)
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool)
      TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) TablesSafeWG)
  unfold sendHandshakeResponse
  refine ensures_bind _ _ (hclock .respLastSent) ?_
  intro now
  refine ensures_bind _ _ hread ?_
  intro p
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (setPeer_tables pid _)) ?_
  intro _
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (createResponse_tables pid)) ?_
  intro created
  refine ensures_bind _ _ (hbranch .respCreated created.isSome) ?_
  intro ready
  cases ready with
  | false => exact hpure
  | true =>
    cases created with
    | none =>
      intro g ambient result final after pre run
      cases run
    | some msg =>
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (addMacToPacket_tables pid msg)) ?_
      intro packet
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (beginSession_tables pid)) ?_
      intro begun
      refine ensures_bind _ _ (hbranch .respSessionBegun begun) ?_
      intro active
      cases active with
      | false => exact hpure
      | true =>
        refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (timersSessionDerived_tables pid)) ?_
        intro _
        refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (traversal_tables pid)) ?_
        intro _
        refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (delKeepalive_tables pid)) ?_
        intro _
        refine ensures_bind _ _ (hclock .respLastSentAgain) ?_
        intro now
        refine ensures_bind _ _ hread ?_
        intro p
        refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (setPeer_tables pid _)) ?_
        intro _
        exact (ensures_iff _ _ _).mpr (sendBufferToPeer_tables pid packet)

end Leanux.Proofs.WG.Index
