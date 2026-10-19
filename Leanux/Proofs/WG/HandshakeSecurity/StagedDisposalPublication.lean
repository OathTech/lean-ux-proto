import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalDecorations

/-! The encryption worker's publication was not a lifetime observer. Expose
only its native peer repayment here, so old encryption receipts remain exact
without inventing old disposition events along this previously quiet path. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.Publication
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

def withRelease [Monad m] (step : {α : Type} → WG.M α → m α)
    (release : Option PeerId → m Unit) (item : List SkbId) (state : PacketState) : m Unit := do
  let some first := item.head? | step (invariant "an empty ring item")
  let pid ← step (IndexOwner.peerDeref (.keypair (← step (getTxSkb first)).keypair))
  step (peerGet pid)
  if !((← step (getPeer pid)).txQueue.all.any (·.head? == some first)) then
    step (invariant "an item for the tx worker that is not on its peer's tx_queue")
  step (setTxSkb first fun p => {p with state})
  _ ← step (cpumaskChooseOnline pid)
  if !(← step getDev).txWorkQueue.contains pid || (← step (peekQueuedUnit .txWorker pid)) then
    step (recordQueued .txWorker pid)
    step (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]})
  release (some pid)

theorem native_factor (item : List SkbId) (state : PacketState) :
    withRelease (fun {_} a => a) peerPut item state = enqueuePerPeerTx item state := rfl

def observed (record : Event → E) (decode : E → Option Event)
    (item : List SkbId) (state : PacketState) : WGPrefix E Unit :=
  withRelease liftWGPrefix (Decoration.release record decode) item state

theorem erases (release : Option PeerId → WGPrefix E Unit)
    (hr : ∀ peer, ErasesStatePrefix (release peer) (peerPut peer))
    (item : List SkbId) (state : PacketState) :
    ErasesStatePrefix (withRelease liftWGPrefix release item state) (enqueuePerPeerTx item state) := by
  unfold withRelease enqueuePerPeerTx
  repeat' first
    | exact hr _
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head Bind.bind; apply erasesStatePrefix_bind)
    | maintenance_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | (split; all_goals try simp_all only []; all_goals try subst_vars)

theorem frame (release : Option PeerId → WGPrefix E Unit)
    (hr : ∀ peer, StateHistoryFrame ρ (release peer))
    (item : List SkbId) (state : PacketState) :
    StateHistoryFrame ρ (withRelease liftWGPrefix release item state) := by
  unfold withRelease
  repeat' first
    | exact hr _
    | exact fun _ _ _ => rfl
    | apply StateHistoryFrame.bind
    | (maintenance_intro; try dsimp only)
    | dsimp (config := {failIfUnchanged := true}) only
    | (split; all_goals try simp_all only []; all_goals try subst_vars)

theorem appends (release : Option PeerId → WGPrefix E Unit)
    (hr : ∀ peer, StateAppends (release peer))
    (item : List SkbId) (state : PacketState) :
    StateAppends (withRelease liftWGPrefix release item state) := by
  unfold withRelease
  repeat' first
    | exact hr _
    | exact StateAppends.lift _
    | exact StateAppends.pure _
    | apply StateAppends.bind
    | (maintenance_intro; try dsimp only)
    | dsimp (config := {failIfUnchanged := true}) only
    | (split; all_goals try simp_all only []; all_goals try subst_vars)

theorem observed_erases (record : Event → E) (decode : E → Option Event)
    (item : List SkbId) (state : PacketState) :
    ErasesStatePrefix (observed record decode item state) (enqueuePerPeerTx item state) :=
  erases _ (fun peer => focusStatePrefix_erases record decode (release_erases peer)) item state

theorem observed_projects (record : Event → E) (decode : E → Option Event)
    (ρ : E → Option F) (quiet : ∀ event, ρ (record event) = none)
    (item : List SkbId) (state : PacketState) :
    StateProjectsPrefix ρ id (observed record decode item state)
      (liftWGPrefix (enqueuePerPeerTx item state)) :=
  Exchange.quiet_native_projection ρ _ _ (observed_erases record decode item state)
    (frame _ (fun peer w => focusPrefix_other record decode ρ quiet ((releaseObserved peer).run w)) item state)

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.Publication
