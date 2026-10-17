import Leanux.Proofs.WG.Index.TablePreservationSource
import Leanux.Proofs.WG.Index.SendFrames
import Leanux.Proofs.WG.Index.PeerReleaseTableFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem sendHandshakeInitiation_tables (pid : PeerId) : Ensures (sendHandshakeInitiation pid)
    TablesSafeWG (fun _ => TablesSafeWG) := by
  have hpure {α : Type} (value : α) :
      Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.branch site value)
  have hread : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g ambient result final after pre run).1
  have hclock (birthday : Int64) :
      Ensures (branchExpired .initRateLimited birthday REKEY_TIMEOUT (!·))
        TablesSafeWG (fun _ => TablesSafeWG) := by
    simp only [branchExpired, birthdateTest, bind_assoc, pure_bind]
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _
      (hambient (AmbientM.hiddenClock64 .birthdateExpired)) ?_
    intro now
    exact hambient (AmbientM.branchCmp _ _ _ _)
  have hstop (message : String) :
      Ensures (invariant message : WG.M Unit) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
  have hset (p : Peer) : Ensures (setPeer pid p) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (setPeer_tables pid p)
  have hmac (msg : List UInt8) :
      Ensures (addMacToPacket pid msg) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (addMacToPacket_tables pid msg)
  have hsend (msg : List UInt8) :
      Ensures (sendBufferToPeer pid msg) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (sendBufferToPeer_tables pid msg)
  have htraversal := (ensures_iff _ _ _).mpr (traversal_tables pid)
  have hdel := (ensures_iff _ _ _).mpr (delKeepalive_tables pid)
  have hinitiated := (ensures_iff _ _ _).mpr (timersHandshakeInitiated_tables pid)
  have hif {α : Type} (condition : Prop) [Decidable condition] (yes no : WG.M α)
      (yesFrame : Ensures yes TablesSafeWG (fun _ => TablesSafeWG))
      (noFrame : Ensures no TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (if condition then yes else no) TablesSafeWG (fun _ => TablesSafeWG) := by
    split <;> assumption
  unfold sendHandshakeInitiation
  refine ensures_bind _ _ hread ?_
  intro peer
  refine ensures_bind _ _ (hclock peer.lastSentHandshake) ?_
  intro limited
  cases limited with
  | true => exact hpure ()
  | false =>
    refine ensures_bind _ _ (hambient (AmbientM.hiddenClock64 .initLastSent)) ?_
    intro now
    refine ensures_bind _ _ hread ?_
    intro p
    refine ensures_bind _ _ (hset {p with lastSentHandshake := now}) ?_
    intro _
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (createInitiation_tables pid)) ?_
    intro created
    cases created
    all_goals
      repeat' first
        | exact hpure _
        | exact hambient _
        | exact hbranch _ _
        | exact hread
        | exact hstop _
        | exact hset _
        | exact hmac _
        | exact hsend _
        | exact htraversal
        | exact hdel
        | exact hinitiated
        | (refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
        | (refine hif _ _ _ ?_ ?_)

theorem handshakeSendWorker_tables (pid : PeerId) : Ensures (handshakeSendWorker pid)
    TablesSafeWG (fun _ => TablesSafeWG) := by
  unfold handshakeSendWorker
  exact ensures_bind _ _ (sendHandshakeInitiation_tables pid)
    (fun _ => (ensures_iff _ _ _).mpr (peerPut_tables (some pid)))

end Leanux.Proofs.WG.Index
