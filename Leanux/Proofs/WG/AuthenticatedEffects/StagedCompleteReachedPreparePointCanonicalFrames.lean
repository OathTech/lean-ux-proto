import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPreparePointSourceFrames

/-! Getter-derived frames for the fixed preparation witness. Source transports
retain the same indexed action; no new observer or native event is introduced. -/

namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity CausalJournal RetirementSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

variable {w v : WGWorld} {a b : Ambient}


theorem Framed.source_mpr {E α : Type} {left right : WGPrefix E α} (same : left=right)
    {shape : Shape right} {h : List E} (framed : Framed shape w a h) :
    Framed ((congrArg Shape same).mpr shape) w a h := by
  cases same
  exact framed

elab "prepare_framed_uncast" : tactic => Lean.Elab.Tactic.withMainContext do
  let target := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  unless target.isAppOf ``Framed do Lean.throwError "not a frame certificate"
  let args := target.getAppArgs
  if args.size < 4 then Lean.throwError "missing frame shape and entry"
  let raw := args[args.size-4]!.consumeMData
  let shape := if raw.isAppOf ``id then raw.getAppArgs.back! else raw
  unless shape.isAppOf ``Eq.mpr do Lean.throwError "not a source cast"
  let parts := shape.getAppArgs
  if parts.size < 2 then Lean.throwError "missing cast proof"
  let rec expand (fuel : Nat) (proof : Lean.Expr) : Lean.MetaM Lean.Expr := do
    if proof.isAppOf ``congrArg then return proof
    match fuel with
    | 0 => return proof
    | n+1 =>
      match proof.getAppFn with
      | .const name levels =>
        let info ← Lean.getConstInfo name
        match info.value? true with
        | some value =>
          let unfolded := Lean.mkAppN (value.instantiateLevelParams info.levelParams levels) proof.getAppArgs
          expand n unfolded.consumeMData.headBeta
        | none => return proof
      | _ => return proof
  let proof ← expand 8 parts[parts.size-2]!.consumeMData
  unless proof.isAppOf ``congrArg do Lean.throwError m!"not a canonical source congruence: {proof.getAppFn} ({proof.getAppArgs.size} args), {proof}"
  let proofArgs := proof.getAppArgs
  if proofArgs.size < 4 then Lean.throwError "incomplete source congruence"
  let same := proofArgs.back!
  let function := proofArgs[proofArgs.size-2]!
  let functionType ← Lean.Meta.whnf (← Lean.Meta.inferType function)
  let .forallE _ domain _ _ := functionType | Lean.throwError "not a unary source congruence"
  Lean.Meta.withLocalDeclD `source domain fun source => do
    let shaped := (Lean.mkApp function source).headBeta.consumeMData
    unless shaped.isAppOf ``Shape do Lean.throwError "source congruence does not produce Shape"
    let some action := shaped.getAppArgs.back? | Lean.throwError "missing congruent source"
    let lifted ← Lean.Meta.mkLambdaFVars #[source] action
    let equation ← Lean.Meta.mkAppM ``congrArg #[lifted,same]
    let frameType ← Lean.Meta.mkAppM ``Framed #[parts.back!,args[args.size-3]!,args[args.size-2]!,args.back!]
    let frame ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar frameType
    let result ← Lean.Meta.mkAppM ``Framed.source_mpr #[equation,frame]
    Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let more ← goal.apply result
      return frame.mvarId! :: more

theorem peerDeref_framed (kid : KeypairId) (h : List LifetimeEvent) :
    Framed (peerDeref kid) w a h := by
  unfold peerDeref
  constructor
  · exact ⟨True.intro,fun _ _ _ _ _=>True.intro⟩
  · intro pid u c middle performed
    cases pid <;> trivial

theorem publication_framed (id : SkbId) (state : PacketState) (h : List LifetimeEvent) :
    Framed (publication id state) w a h := by
  unfold publication
  change True ∧ _
  refine ⟨True.intro,?_⟩
  intro pkt u c middle readRx
  change Framed (peerDeref pkt.keypair) u c middle ∧ _
  refine ⟨peerDeref_framed _ _,?_⟩
  intro pid v b last deref
  change Framed (peerGet pid) v b last ∧ _
  refine ⟨peerGet_framed _ _,?_⟩
  intro ignored x ax hx borrowed
  change True ∧ _
  refine ⟨True.intro,?_⟩
  intro p y ay hy readPeer
  dsimp only
  split
  · prepare_framed_uncast
    change True ∧ _
    refine ⟨True.intro,?_⟩
    intro ignored z az hz impossible
    cases impossible
  · prepare_framed_uncast
    change Framed (setRx id _) y ay hy ∧ _
    refine ⟨setRx_framed _ _ _,?_⟩
    intro ignored z az hz written
    change (Access.writePeer pid {p with napiScheduled:=true}).Entry z ∧ _
    exact ⟨publication_write_entry readPeer written,fun _ _ _ _ _=>True.intro⟩

theorem boolShape_framed {E α : Type} {yes no : WGPrefix E α}
    (flag : Bool) (left : Shape yes) (right : Shape no) (h : List E)
    (yesFrame : Framed left w a h) (noFrame : Framed right w a h) :
    Framed (boolShape flag yes no left right) w a h := by
  cases flag
  · exact noFrame
  · exact yesFrame

theorem optionShape_framed {E α ι : Type} {absent : WGPrefix E α} {present : ι → WGPrefix E α}
    (query : Option ι) (no : Shape absent) (yes : ∀value,Shape (present value)) (h : List E)
    (noFrame : Framed no w a h) (yesFrame : ∀value,Framed (yes value) w a h) :
    Framed (optionShape query absent present no yes) w a h := by
  cases query
  · exact noFrame
  · exact yesFrame _

macro "prepare_direct_frame_step" : tactic => `(tactic| first
  | exact True.intro
  | prepare_framed_uncast
  | apply boolShape_framed
  | apply optionShape_framed
  | apply And.intro
  | intro value
  | (dsimp +failIfUnchanged only [Framed,Access.Entry,id])
  | split)

theorem packet_framed (pkt : RxPacket) (h : List LifetimeEvent) :
    Framed (packet pkt) w a h := by
  unfold packet
  repeat' prepare_direct_frame_step


theorem readDecrypt_framed (id : SkbId) (h : List LifetimeEvent) :
    Framed (readDecrypt id) w a h := by
  change True ∧ _
  refine ⟨True.intro,?_⟩
  intro pkt v b middle read
  exact ⟨packet_framed _ _,fun _ _ _ _ _=>True.intro⟩

theorem decrypt_framed (id : SkbId) (h : List (MaterialOrigin.Event RxOrigin.Receipt)) :
    Framed (decrypt id) w a h := readDecrypt_framed _ _

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
