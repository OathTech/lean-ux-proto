import Leanux.Proofs.WG.TransmitSecurity.CompletionCiphertext

/-! The actual selected TX step carries ciphertext certificates through
queue removal, socket calls and final disposal, including stopped prefixes. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CompletionCiphertext
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity
set_option maxHeartbeats 600000

private theorem dispose_native (peer : PeerId) (ids : List SkbId) (key : KeypairId) :
    Preserves (CiphertextOrigins.Inv bank) (TxDisposition.disposeSource peer ids key) := by
  have factor : TxDisposition.disposeSource peer ids key = (do
      TxDisposition.freeList ids
      keypairPut (some key) false
      peerPut (some peer)
      pure true) := by simp [TxDisposition.disposeSource,TxDisposition.freeList]
  rw [factor]
  exact preserves_bind (CiphertextOrigins.free_list ids) fun _ =>
    preserves_bind (CiphertextOrigins.NativeFrames.key_put (some key) false) fun _ =>
    preserves_bind (CiphertextOrigins.NativeFrames.peer_put (some peer)) fun _ => preserves_pure _

theorem drop (peer : PeerId) (ids : List SkbId) :
    PrefixPreserves (Inv bank) (Good bank)
      (focusPrefix Completion.Event.disposition Completion.disposition? (TxDisposition.drop peer ids)) := by
  apply quiet (Appends.focus _ _ _) (focusPrefix_other _ _ _ (fun _ => rfl) _)
    (focusPrefix_erases _ _ (TxDisposition.drop_erases peer ids))
  apply PublicationPoll.native_product (CiphertextOrigins.Inv bank)
  apply preserves_bind (CiphertextOrigins.NativeFrames.read_peer peer)
  intro p
  apply preserves_bind (CiphertextOrigins.NativeFrames.read_peer peer)
  intro q
  unfold setPeer
  exact CiphertextOrigins.frame (CiphertextOrigins.modify _ (fun _ => rfl) (fun _ => rfl))

theorem dispose (peer : PeerId) (ids : List SkbId) (key : KeypairId) :
    PrefixPreserves (Inv bank) (Good bank)
      (focusPrefix Completion.Event.disposition Completion.disposition? (TxDisposition.dispose peer ids key)) :=
  quiet (Appends.focus _ _ _) (focusPrefix_other _ _ _ (fun _ => rfl) _)
    (focusPrefix_erases _ _ (TxDisposition.dispose_erases peer ids key))
    (PublicationPoll.native_product _ _ (dispose_native peer ids key))

theorem stop (s : String) :
    PrefixPreserves (Inv bank) (Good bank) (liftPrefix (liftWG (invariant s : WG.M α))) := by
  apply lift_safe
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases run

macro "completion_body_ciphertext_step" : tactic => `(tactic| first
  | (nonce_product_head Completion.complete; exact CompletionCiphertext.complete _ _)
  | (nonce_product_head focusPrefix; first
      | with_reducible exact CompletionCiphertext.drop _ _
      | with_reducible exact CompletionCiphertext.dispose _ _ _)
  | (nonce_product_head Completion.access; first
      | exact access (getTxSkbPrefix_erases _) (CiphertextOrigins.NativeFrames.read_packet _)
      | exact access (getPeerMixed_erases _) (CiphertextOrigins.NativeFrames.read_peer _)
      | exact access (modifyPeerKeysPrefix_erases _ _) (peer_modify _ _))
  | (nonce_product_head liftPrefix; first
      | exact CompletionCiphertext.branch _ _
      | exact CompletionCiphertext.stop _
      | exact lift_safe _ (PublicationPoll.native_product _ _
          (CiphertextOrigins.NativeFrames.store (prevQueuePeek_sameWGStore _))))
  | (nonce_product_head Pure.pure; exact PrefixPreserves.pure (fun _ _ hi => hi.2) _)
  | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
  | (nonce_product_head ite; apply PrefixPreserves.ite)
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

theorem body (pid : PeerId) (first : Option (List SkbId)) :
    PrefixPreserves (Inv bank) (Good bank) (Completion.body pid first) := by
  unfold Completion.body TxDisposition.andObs
  cases first with
  | none => simp only [Option.isSome_none]; repeat' completion_body_ciphertext_step
  | some items =>
    cases items <;> simp only [Option.isSome_some,List.head?_nil,List.head?_cons]
    all_goals repeat' completion_body_ciphertext_step

theorem step (pid : PeerId) :
    PrefixPreserves (Inv bank) (Good bank) (Completion.step pid) := by
  unfold Completion.step
  repeat' first
    | (nonce_product_head Completion.body; exact body _ _)
    | completion_body_ciphertext_step

end Leanux.Proofs.WG.TransmitSecurity.CompletionCiphertext
