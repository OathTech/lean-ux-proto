import Leanux.Proofs.WG.TransmitSecurity.CompletionPeerFrames

/-! Queue removal and final disposal retain the selected peer words of any
remaining packets. Freed packet cells cannot introduce a contrary value. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CompletionPeer
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Completion

private theorem free_packet (id : SkbId) :
    Preserves (fun w => BatchCoherence.Aligned w pid slot items) (freeTxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have packets := (hoare_iff_run_ambient _ _ _).mp
    (TxDisposition.free_packet_wp id (TxDisposition.txPackets w)) w a result v b rfl run
  apply before.retains
  intro target packet resident
  rw [packets] at resident
  by_cases same : id = target
  · simp only [same,ite_true] at resident; cases resident
  · exact ⟨packet,by simpa only [same,ite_false] using resident,rfl⟩

private theorem free_list (ids : List SkbId) :
    Preserves (fun w => BatchCoherence.Aligned w pid slot items) (TxDisposition.freeList ids) := by
  induction ids with
  | nil => exact preserves_pure _
  | cons id rest ih =>
    rw [TxDisposition.freeList_cons]
    exact preserves_bind (free_packet id) (fun _ => ih)

private theorem dispose_native (peer : PeerId) (ids : List SkbId) (key : KeypairId) :
    Preserves (fun w => BatchCoherence.Aligned w pid slot items)
      (TxDisposition.disposeSource peer ids key) := by
  have factor : TxDisposition.disposeSource peer ids key = (do
      TxDisposition.freeList ids
      keypairPut (some key) false
      peerPut (some peer)
      pure true) := by simp [TxDisposition.disposeSource,TxDisposition.freeList]
  rw [factor]
  exact preserves_bind (free_list ids) fun _ =>
    preserves_bind (BatchCoherence.aligned (PacketMaterial.of_packets (TxDisposition.keyPut_packets (some key) false))) fun _ =>
    preserves_bind (BatchCoherence.aligned (PacketMaterial.of_packets (TxDisposition.peerPut_packets (some peer)))) fun _ =>
    preserves_pure _

theorem drop (peer : PeerId) (ids : List SkbId) :
    PrefixPreserves (Inv pid slot items) Good
      (focusPrefix Completion.Event.disposition Completion.disposition? (TxDisposition.drop peer ids)) := by
  apply quiet (Appends.focus _ _ _) (focusPrefix_other _ _ _ (fun _ => rfl) _)
    (focusPrefix_erases _ _ (TxDisposition.drop_erases peer ids))
  apply PublicationPoll.native_product (fun w => BatchCoherence.Aligned w pid slot items)
  apply BatchCoherence.aligned
  apply SameView.bind (PacketMaterial.read_peer peer)
  intro p
  apply SameView.bind (PacketMaterial.read_peer peer)
  intro q
  unfold setPeer
  exact PacketMaterial.modify_device _ (fun _ => rfl)

theorem dispose (peer : PeerId) (ids : List SkbId) (key : KeypairId) :
    PrefixPreserves (Inv pid slot items) Good
      (focusPrefix Completion.Event.disposition Completion.disposition? (TxDisposition.dispose peer ids key)) :=
  quiet (Appends.focus _ _ _) (focusPrefix_other _ _ _ (fun _ => rfl) _)
    (focusPrefix_erases _ _ (TxDisposition.dispose_erases peer ids key))
    (PublicationPoll.native_product _ _ (dispose_native peer ids key))

theorem stop (s : String) :
    PrefixPreserves (Inv pid slot items) Good (liftPrefix (liftWG (invariant s : WG.M α))) := by
  apply lift_safe
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases run

end Leanux.Proofs.WG.TransmitSecurity.CompletionPeer
