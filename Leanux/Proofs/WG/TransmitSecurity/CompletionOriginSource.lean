import Leanux.Proofs.WG.TransmitSecurity.CompletionOriginFrames

/-! The actual TX worker reads the selected head before entering completion.
That read derives its allocation certificate from resident packet material. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CompletionOrigin
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000

theorem read_packet (id : SkbId) :
    PrefixEnsures (Inv bank) (Good bank) (Completion.access (getTxSkbPrefix id))
      (fun packet h w => Inv bank h w ∧ ∃ generation,
        PacketOrigins.Certificate bank generation id (PacketMaterial.material packet)) := by
  intro w h before
  obtain ⟨suffix,extension,safe,after⟩ :=
    access (bank := bank) (getTxSkbPrefix_erases id) (PacketOrigins.NativeFrames.read_packet id) w h before
  refine ⟨suffix,extension,safe,?_⟩
  cases result : (runPrefix (Completion.access (getTxSkbPrefix id)) w h).1 with
  | error stop => trivial
  | ok out =>
    have native := (Completion.access_erases (getTxSkbPrefix_erases id) w h).symm.trans result
    obtain ⟨generation,_,origin⟩ := PacketOrigins.read_origin before.1 (r := ⟨out.1,w,out.2⟩) native
    exact ⟨by simpa only [result] using after,generation,origin⟩

theorem packet_then (id : SkbId) (next : DataPacket → PrefixM Completion.Event α)
    (safe : ∀ packet, (∃ generation,
      PacketOrigins.Certificate bank generation id (PacketMaterial.material packet)) →
      PrefixPreserves (Inv bank) (Good bank) (next packet)) :
    PrefixPreserves (Inv bank) (Good bank) (Completion.access (getTxSkbPrefix id) >>= next) := by
  apply PrefixEnsures.bind (read_packet id)
  intro packet w h before
  exact safe packet before.2 w h before.1

theorem complete_from_read (pid : PeerId) (id : SkbId) (rest : List SkbId) (packet : DataPacket)
    (origin : ∃ generation, PacketOrigins.Certificate bank generation id (PacketMaterial.material packet)) :
    PrefixPreserves (Inv bank) (Good bank) (Completion.complete pid (id :: rest)) := by
  obtain ⟨generation,cert⟩ := origin
  exact complete pid (id :: rest) ⟨id,rest,generation,PacketMaterial.material packet,rfl,cert⟩

open Lean Meta Elab Tactic in
elab "completion_origin_read_bind" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``PrefixPreserves do throwError "not a preservation contract"
  let some last := target.getAppArgs.back? | throwError "missing action"
  let action := last.consumeMData.headBeta
  unless action.isAppOf ``Bind.bind do throwError "not a bind"
  let args := action.getAppArgs
  unless args.size ≥ 2 do throwError "incomplete bind"
  let some source := args[args.size - 2]? | throwError "missing first action"
  let first := source.consumeMData.headBeta
  unless first.isAppOf ``Completion.access do throwError "not an access"
  let some native := first.getAppArgs.back? | throwError "missing access source"
  unless native.consumeMData.headBeta.isAppOf ``getTxSkbPrefix do
    throwError "not a TX packet read"

macro "completion_origin_source_step" : tactic => `(tactic| first
  | (nonce_product_head Completion.complete; exact complete_from_read _ _ _ _ (by assumption))
  | (completion_origin_read_bind; apply packet_then; intro packet origin)
  | (nonce_product_head focusPrefix; first
      | with_reducible exact CompletionOrigin.drop _ _
      | with_reducible exact CompletionOrigin.dispose _ _ _)
  | (nonce_product_head Completion.access; first
      | exact access (getTxSkbPrefix_erases _) (PacketOrigins.NativeFrames.read_packet _)
      | exact access (getPeerMixed_erases _) (PacketOrigins.NativeFrames.read_peer _)
      | exact access (modifyPeerKeysPrefix_erases _ _) (peer_modify _ _))
  | (nonce_product_head liftPrefix; first
      | exact CompletionOrigin.branch _ _
      | exact CompletionOrigin.stop _
      | exact lift_safe _ (PublicationPoll.native_product _ _
          (PacketOrigins.NativeFrames.store (prevQueuePeek_sameWGStore _))))
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
  | none => simp only [Option.isSome_none]; repeat' completion_origin_source_step
  | some items =>
    cases items <;> simp only [Option.isSome_some,List.head?_nil,List.head?_cons]
    all_goals repeat' completion_origin_source_step

theorem step (pid : PeerId) :
    PrefixPreserves (Inv bank) (Good bank) (Completion.step pid) := by
  unfold Completion.step
  repeat' first
    | (nonce_product_head Completion.body; exact body _ _)
    | completion_origin_source_step

end Leanux.Proofs.WG.TransmitSecurity.CompletionOrigin
