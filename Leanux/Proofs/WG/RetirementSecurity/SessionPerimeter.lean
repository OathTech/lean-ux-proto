import Leanux.Proofs.WG.RetirementSecurity.HolderRotation
import Leanux.Proofs.WG.RetirementSecurity.Session

/-! The complete session path leaves other peers and all packet holders in
place while creating, deriving, rotating and publishing the selected key. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem create_perimeter (pid : PeerId) (word : Option PeerId) :
    SameView (holderPerimeter pid) (keypairCreate word) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases result with
  | none => rw [Origins.create_none word w v a b run]
  | some key =>
    exact congrArg (fun shape =>
      ((fun other => if other = pid then none else shape.1.bind fun peers => peers[other]?),shape.2))
      (create_carriers word key w v a b run)

theorem setKeypair_perimeter (pid : PeerId) (key : KeypairId) (k : Keypair) :
    SameView (holderPerimeter pid) (setKeypair key k) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases run
  cases device : w.dev <;> simp [holderPerimeter,carrierShape,peersAt,device]

theorem ambient_perimeter (pid : PeerId) (action : AmbientM α) :
    SameView (holderPerimeter pid) (monadLift action : WG.M α) :=
  fun initial => hoare_liftAmbient action (fun w => holderPerimeter pid w = initial)

theorem derive_perimeter (pid : PeerId) (key : KeypairId) (initiator : Bool) (ck : List UInt8) :
    SameView (holderPerimeter pid) (deriveKeys key initiator ck) := by
  unfold deriveKeys
  apply SameView.bind (ambient_perimeter pid (AmbientM.hiddenClock64 .deriveKeysBirthdate))
  intro born
  apply SameView.bind ((kdf_sameWGWorld true false ck []).factor (holderPerimeter pid))
  intro outputs
  apply SameView.bind ((kdfOut_sameWGWorld outputs 0).factor (holderPerimeter pid))
  intro first
  apply SameView.bind ((kdfOut_sameWGWorld outputs 1).factor (holderPerimeter pid))
  intro second
  exact (getKeypair_perimeter pid key).bind (fun _ => setKeypair_perimeter pid key _)

theorem init_perimeter (pid : PeerId) (key : KeypairId) (initiator : Bool) (remote : Nat) :
    SameView (holderPerimeter pid) (SessionOrigin.initKey key initiator remote) :=
  (getKeypair_perimeter pid key).bind (fun _ => setKeypair_perimeter pid key _)

theorem zero_perimeter (pid : PeerId) : SameView (holderPerimeter pid) (handshakeZero pid) :=
  updatePeer_perimeter pid zeroedPeer

theorem index_perimeter (pid : PeerId) (action : IndexM α) :
    SameView (holderPerimeter pid) (liftIndex action) := by
  intro initial
  apply hoare_liftIndex
  intro w d table hi device
  simpa [holderPerimeter,carrierShape,peersAt,device] using hi

theorem front_perimeter (pid : PeerId) : SameView (holderPerimeter pid) (SessionOrigin.front pid) := by
  intro initial
  let P : WGWorld → Prop := fun w => holderPerimeter pid w = initial
  change Preserves P (SessionOrigin.front pid)
  unfold SessionOrigin.front SessionOrigin.frontWith
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getPeer; exact (getPeer_perimeter pid _).wp (fun view => view = initial))
    | (index_material_head keypairCreate; exact (create_perimeter pid _).wp (fun view => view = initial))
    | (index_material_head SessionOrigin.initKey; exact (init_perimeter pid _ _ _).wp (fun view => view = initial))
    | (index_material_head deriveKeys; exact (derive_perimeter pid _ _ _).wp (fun view => view = initial))
    | (index_material_head IndexOwner.peerWord; exact indexOwner_peerWord_preserves _ P)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match
    | contradiction

theorem tail_perimeter (pid : PeerId) (key : KeypairId) :
    SameView (holderPerimeter pid) (SessionOrigin.tail pid key) := by
  intro initial
  let P : WGWorld → Prop := fun w => holderPerimeter pid w = initial
  change Preserves P (SessionOrigin.tail pid key)
  unfold SessionOrigin.tail SessionOrigin.tailWith
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getPeer; exact (getPeer_perimeter pid _).wp (fun view => view = initial))
    | (index_material_head handshakeZero; exact (zero_perimeter pid).wp (fun view => view = initial))
    | (index_material_head addNewKeypair; exact (rotation_perimeter pid _).wp (fun view => view = initial))
    | (index_material_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ P)
    | (index_material_head liftIndex; exact (index_perimeter pid _).wp (fun view => view = initial))
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match
    | contradiction

theorem session_perimeter (pid : PeerId) : SameView (holderPerimeter pid) (beginSession pid) := by
  rw [SessionOrigin.factor]
  apply SameView.bind (front_perimeter pid)
  intro context
  cases context with
  | none => exact SameView.pure (holderPerimeter pid) false
  | some context => exact tail_perimeter pid context.slot

end Leanux.Proofs.WG.RetirementSecurity
