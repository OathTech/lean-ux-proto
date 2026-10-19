import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalEncryptionProjection

/-! Exact old encryption history for the publication callback extension.
No old lifetime events are added by the encryption publication path. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.EncryptionSource
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity AuthenticatedEffects
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

structure Ops.Appends (o : Ops E) : Prop where
  step : ∀ {α} (action : Leanux.M α), Logged.Appends (o.step action)
  head : ∀ id, Logged.Appends (o.head id)
  packet : ∀ headId head id, Logged.Appends (o.packet headId head id)
  publish : ∀ item state, Logged.Appends (o.publish item state)

private theorem capture_appends (action : Leanux.M α) : Appends (captureRun action : PrefixM E _) := by
  intro w h
  refine ⟨[],?_⟩
  rw [runPrefix_captureRun]
  cases action.run w <;> simp

theorem native_appends : Ops.Appends native where
  step := fun _ => Appends.lift _
  head := fun _ => capture_appends _
  packet := by
    intro headId head id
    unfold native WorkerEncryption.packet
    exact Appends.bind (capture_appends _) (fun _ => Appends.focus _ _ _)
  publish := fun _ _ => Appends.lift _

macro "disposal_encryption_align " enc:ident dec:ident inv:ident : tactic => `(tactic| first
  | with_reducible exact CausalFocus.native $enc $dec _ (Ops.Appends.step native_appends _)
  | with_reducible exact CausalFocus.native $enc $dec _ (Ops.Appends.head native_appends _)
  | with_reducible exact CausalFocus.native $enc $dec _ (Ops.Appends.packet native_appends _ _ _)
  | with_reducible exact CausalFocus.native $enc $dec _ (Ops.Appends.publish native_appends _ _)
  | (maintenance_head Pure.pure; exact CausalFocus.pure $enc $dec _)
  | (maintenance_head Bind.bind; apply CausalFocus.bind $enc $dec $inv)
  | (maintenance_head ite; apply CausalFocus.choice $enc $dec)
  | (maintenance_head ForIn.forIn; apply CausalFocus.loop $enc $dec $inv)
  | (maintenance_intro; try dsimp only)
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

variable (encode : WorkerEncryption.Receipt → E) (decode : E → Option WorkerEncryption.Receipt)
  (inverse : ∀ r, decode (encode r) = some r)
include inverse

private theorem afterHead_aligned (first : List SkbId) (headId : SkbId) (head : RunWitness DataPacket) :
    CausalFocus.Aligned encode decode (afterHead (focused encode decode) first headId head)
      (afterHead native first headId head) := by
  unfold afterHead
  simp only [focused]
  repeat' disposal_encryption_align encode decode inverse

theorem tail_focus (item : Option (List SkbId)) :
    tail (focused encode decode) item = focusPrefix encode decode (WorkerEncryption.tail item) := by
  have aligned : CausalFocus.Aligned encode decode (tail (focused encode decode) item) (tail native item) := by
    unfold tail
    simp only [focused]
    repeat' first
      | (maintenance_head afterHead; exact afterHead_aligned encode decode inverse _ _ _)
      | disposal_encryption_align encode decode inverse
  exact aligned.2

omit inverse encode decode in
theorem observed_tail_projects (ρ : E → Option F)
    (eg : WorkerEncryption.Receipt → E) (dg : E → Option WorkerEncryption.Receipt)
    (et : WorkerEncryption.Receipt → F) (dt : F → Option WorkerEncryption.Receipt)
    (enc : ∀ r, ρ (eg r) = some (et r)) (dec : ∀ e, dg e = (ρ e).bind dt)
    (inverse : ∀ r, dt (et r) = some r)
    (disposal : Event → E) (disposalDecode : E → Option Event)
    (quiet : ∀ e, ρ (disposal e) = none) (item : Option (List SkbId)) :
    ProjectsPrefix ρ id (tail (observed eg dg disposal disposalDecode) item)
      (focusPrefix et dt (WorkerEncryption.tail item)) := by
  rw [← tail_focus et dt inverse]
  exact tail_projects ρ (observed_projects ρ eg dg et dt enc dec disposal disposalDecode quiet) item

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.EncryptionSource
