import Leanux.Proofs.WG.AuthenticatedEffects.EmissionNativeFrames
import Leanux.Proofs.WG.Queues.TxDisposition

/-! Send-free native TX queue and disposal leaves. No socket action is
covered by these frames. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem skb (body : SkbM α) : SameView WGWorld.sent (liftSkb body) :=
  fun initial => skb_sent_spec (fun s => s = initial) body

theorem peek (queue : PrevQueue α) : SameView WGWorld.sent queue.peek := by
  sent_frame [PrevQueue.peek,PrevQueue.dequeue] using []

theorem keypair_put (key : Option KeypairId) (unreference : Bool) :
    SameView WGWorld.sent (keypairPut key unreference) := by
  intro initial
  change Preserves (fun w : WGWorld => w.sent = initial) _
  unfold keypairPut refcountDecAndTest
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,unsupported,
    IndexOwner.peerDeref,IndexOwner.peerWord]
  repeat' consumer_sent_step initial

theorem keypair_put_spec (P : List SentDatagram → Prop) (key : Option KeypairId) (unreference : Bool) :
    Preserves (fun w => P w.sent) (keypairPut key unreference) := (keypair_put key unreference).wp P

theorem dispose (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    SameView WGWorld.sent (TxDisposition.disposeSource pid item key) := by
  intro initial
  change Preserves (fun w : WGWorld => w.sent = initial) _
  unfold TxDisposition.disposeSource
  apply preserves_bind
  · apply list_view_spec id (fun w : WGWorld => w.sent = initial)
    intro id state
    exact preserves_bind (skb_sent_spec (fun s => s = initial) _) (fun _ => preserves_pure _)
  · intro _
    exact preserves_bind (keypair_put_spec (fun s => s = initial) (some key) false) (fun _ =>
      preserves_bind (peerPut_sent_spec (fun s => s = initial) (some pid)) (fun _ => preserves_pure _))

end Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
