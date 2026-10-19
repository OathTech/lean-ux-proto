import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialCursor
import Leanux.Proofs.WG.Packets.PublicationSession

/-! Native frame contracts for the allocation-stamped crypted RX carrier.
The session frame retains the packet's older numeric key bound explicitly. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues PublicationIdentity AuthenticatedEffects Responder

/-- Original session creation may rotate and delete keys, but its fresh slot
cannot replace a crypted packet's carried older key reference. -/
theorem session (pid : PeerId) : Preserves (Inv h) (beginSession pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have rx := (ProjectedAction.iff_run_ambient _ _ _).mp
    (PublicationFrontier.beginSession_rx pid)
      w a result v b run
  apply before.retains
  · intro id pkt cell _
    exact ⟨by simpa only [rx] using cell,
      congrArg (fun epoch : Option Nat => (epoch.getD 0,id+1)) (congrArg Prod.fst rx)⟩
  · intro d e hd he
    exact ResidentMaterial.session_cursor pid w v a b result hd he run
  · intro d hd slot bound core resident
    exact ResidentMaterial.session_below pid w v a b result hd run slot bound core resident


end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
