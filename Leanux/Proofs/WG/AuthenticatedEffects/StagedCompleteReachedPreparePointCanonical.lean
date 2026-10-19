import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPreparePointSource

/-! The fixed witness is obtained by expanding the original observed source.
It includes the stored-packet read, both rejection key reads, RX setters, the
peer borrow, the cached peer getter and its final publication write. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity CausalJournal RetirementSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

noncomputable def boolShape (flag : Bool) (yes no : WGPrefix E α)
    (left : Shape yes) (right : Shape no) : Shape (if flag then yes else no) := by
  cases flag with
  | false => exact right
  | true => exact left

noncomputable def optionShape (value : Option ι) (none : WGPrefix E α) (some : ι → WGPrefix E α)
    (absent : Shape none) (present : ∀x,Shape (some x)) :
    Shape (match value with | .none=>none | .some x=>some x) := by
  cases value with
  | none => exact absent
  | some x => exact present x

elab "prepare_shape_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a preparation source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing source action"
  let .const actual _ := action.consumeMData.headBeta.getAppFn | Lean.throwError "not a named source"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different source head"

macro "prepare_shape_step" : tactic => `(tactic| first
  | exact Shape.pure _
  | (prepare_shape_head liftWGPrefix
     apply Shape.quiet
     intro initial
     change Preserves (fun w => StagedEntry.view w = initial) _
     try simp only [decryptKeyReject,WG.orM,branch,branchCmp,hiddenAlloc,invariant,unsupported,refcountInc]
     repeat' first
       | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w=>StagedEntry.view w=initial))
       | entry_key_step initial)
  | (prepare_shape_head getRxSkbPrefix; exact Shape.access (.readRx _))
  | (prepare_shape_head writeRxSkbPrefix; exact Shape.access (.writeRx _ _))
  | (prepare_shape_head getKeypairPrefix; exact Shape.access (.readKey _))
  | (prepare_shape_head setKeypairPrefix; exact Shape.access (.writeKey _ _))
  | (prepare_shape_head Peers.getPeerPrefix; exact Shape.access (.readPeer _))
  | (prepare_shape_head Peers.setPeerPrefix; exact Shape.access (.writePeer _ _))
  | (prepare_shape_head focusStatePrefix; apply Shape.focus; · intro event; rfl)
  | (prepare_shape_head ite; apply boolShape)
  | apply optionShape
  | apply Shape.bind
  | intro value
  | split)

noncomputable def setRx (id : SkbId) (f : RxPacket → RxPacket) : Shape (setRxSkbPrefix id f) := by
  unfold setRxSkbPrefix
  exact .bind (.access (.readRx id)) (fun p=>.access (.writeRx id (f p)))

noncomputable def peerGet (pid : PeerId) : Shape (peerGetMixed pid) := by
  unfold peerGetMixed peerStateFocus peerGetLocal Peers.requireNotPendingPrefix
  repeat' prepare_shape_step

noncomputable def peerDeref (kid : KeypairId) : Shape (peerDerefPrefix (.keypair kid)) := by
  unfold peerDerefPrefix peerWordPrefix
  repeat' prepare_shape_step

noncomputable def publication (id : SkbId) (state : PacketState) : Shape (RxWorkers.publishPrefix id state) := by
  unfold RxWorkers.publishPrefix
  repeat' first
    | (prepare_shape_head peerDerefPrefix; exact peerDeref _)
    | (prepare_shape_head peerGetMixed; exact peerGet _)
    | (prepare_shape_head setRxSkbPrefix; exact setRx _ _)
    | (prepare_shape_head getPeerMixed; unfold getPeerMixed peerStateFocus)
    | (prepare_shape_head setPeerMixed; unfold setPeerMixed peerStateFocus)
    | prepare_shape_step

noncomputable def packet (pkt : RxPacket) : Shape (decryptPacketPrefix pkt) := by
  unfold decryptPacketPrefix
  apply Shape.bind
  · prepare_shape_step
  intro noKey
  apply boolShape noKey
  · exact .pure none
  apply Shape.bind (.access (.readKey pkt.keypair))
  intro k
  apply Shape.bind
  · prepare_shape_step
  intro reject
  apply boolShape reject
  · exact .bind (.access (.readKey pkt.keypair)) (fun fresh=>
      .bind (.access (.writeKey pkt.keypair {fresh with receiving:={fresh.receiving with isValid:=false}}))
        (fun _=>.pure none))
  apply Shape.bind
  · prepare_shape_step
  intro cowOk
  apply Shape.bind
  · prepare_shape_step
  intro cowBad
  apply boolShape cowBad
  · exact .pure none
  apply Shape.bind
  · prepare_shape_step
  intro sgBad
  apply boolShape sgBad
  · exact .pure none
  apply Shape.bind
  · prepare_shape_step
  intro decryptBad
  apply boolShape decryptBad
  · exact .pure none
  let plain:=aeadDecrypt k.receiving.key (counterNonce (u64le pkt.bytes 8)) (pkt.bytes.drop 16) []
  change Shape (match plain with
    | some bytes=>do
      if ← liftWGPrefix (branch .decTrimFailed false) then return none
      return some {pkt with nonce:=u64le pkt.bytes 8,bytes}
    | _=>liftWGPrefix (invariant "unreachable"))
  let finish : List UInt8 → MixedM (Option RxPacket) := fun bytes=>do
    if ← liftWGPrefix (branch .decTrimFailed false) then return none
    return some {pkt with nonce:=u64le pkt.bytes 8,bytes}
  let absent : MixedM (Option RxPacket) := liftWGPrefix (invariant "unreachable")
  let tailShape (bytes : List UInt8) : Shape (finish bytes) := by
    apply Shape.bind
    · prepare_shape_step
    intro trimBad
    exact boolShape trimBad _ _ (.pure none) (.pure (some {pkt with nonce:=u64le pkt.bytes 8,bytes}))
  let emptyShape : Shape absent := by dsimp only [absent]; prepare_shape_step
  let shaped := optionShape (E:=LifetimeEvent) plain absent finish emptyShape tailShape
  let source {action : MixedM (Option RxPacket)} (_ : Shape action) := action
  refine (congrArg Shape (show _ = source shaped from ?_)).mpr shaped
  dsimp only [source]
  cases plain <;> rfl

noncomputable def readDecrypt (id : SkbId) : Shape (RxOrigin.readDecryptPrefix id) := by
  unfold RxOrigin.readDecryptPrefix
  exact .bind (.access (.readRx id)) (fun pkt=>.bind (packet pkt) (fun result=>.pure (pkt,result)))

noncomputable def decrypt (id : SkbId) : Shape (RxOrigin.decrypt id) := by
  unfold RxOrigin.decrypt
  apply Shape.receipt
  index_unfold _private.Leanux.Proofs.WG.Packets.RxOriginCuts.«0».Leanux.Proofs.WG.RxOrigin.accessState
  exact .focus MaterialOrigin.Event.life MaterialOrigin.life? (fun _=>rfl) (readDecrypt id)

noncomputable def canonical : Shape RxOrigin.prepare := by
  unfold RxOrigin.prepare RxOrigin.prepareWith
  index_unfold _private.Leanux.Proofs.WG.Packets.RxOriginCuts.«0».Leanux.Proofs.WG.RxOrigin.accessState
  simp only [monadLift_self]
  repeat' first
    | (prepare_shape_head RxOrigin.decrypt; exact decrypt _)
    | (prepare_shape_head setRxSkbPrefix; exact setRx _ _)
    | (prepare_shape_head RxWorkers.publishPrefix; exact publication _ _)
    | prepare_shape_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
