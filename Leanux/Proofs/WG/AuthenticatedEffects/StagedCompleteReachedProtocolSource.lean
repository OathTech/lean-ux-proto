import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeSocketSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerMetadataCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRoutedTransmitComposition

/-! The protocol-buffer source exposes native reads, its actual socket calls and the saved-peer byte update. Socket continuations retain the causal context and original receipt entry. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProtocolPoints
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal

abbrev History := List Event
abbrev Carrier := WorkService.Points.Carrier
abbrev Checked (action : PrefixM Event α) := WorkService.Points.Checked action

def socket (args : ProtocolSocket.Args) : PrefixM Event Int := liftWGObserver
  (CausalEffects.atCurrent scope? fun context=>ProtocolSocket.socket Event.protocolSocket context args)

inductive Shape : {α : Type} → PrefixM Event α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | native (body : WG.M α) (source : PeerMetadata.Shape body) : Shape (liftWGObserver (liftWGPrefix body))
  | socket (args : ProtocolSocket.Args) : Shape (socket args)
  | bind {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀value,Shape (next value)) : Shape (body >>= next)

noncomputable def observerBindShape (body : WGPrefix Event α) (next : α→WGPrefix Event β)
    (head : Shape (liftWGObserver body)) (tail : ∀value,Shape (liftWGObserver (next value))) :
    Shape (liftWGObserver (body >>= next)) := by
  rw [liftWGObserver_bind]
  exact .bind head tail

noncomputable def updateShape (pid : PeerId) (f : Peer → Peer)
    (same : ∀p,(f p).internalId=p.internalId ∧ (f p).staged=p.staged ∧ (f p).txQueue=p.txQueue) :
    Shape (liftWGObserver (liftWGPrefix (getPeer pid) >>= fun p=>liftWGPrefix (setPeer pid (f p)))) := by
  rw [←Queued.lift_bind]
  exact .native _ (PeerMetadata.updateShape pid f same)

open Lean Meta Elab Tactic in
elab "protocol_source_head " expected:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Shape do throwError "not a protocol shape"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``liftWGObserver do throwError "not an observer"
  let body := action.getAppArgs.back!.consumeMData.headBeta
  let name ← realizeGlobalConstNoOverloadWithInfo expected
  unless body.getAppFn.constName? == some name do throwError "different source head"

open Lean Meta Elab Tactic in
elab "protocol_update_head" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Shape do throwError "not a protocol shape"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``liftWGObserver do throwError "not an observer"
  let body := action.getAppArgs.back!.consumeMData.headBeta
  unless body.isAppOf ``Bind.bind do throwError "not a source bind"
  let args := body.getAppArgs
  let first := args[args.size-2]!.consumeMData
  unless first.isAppOf ``liftWGPrefix do throwError "not a native read"
  unless first.getAppArgs.back!.consumeMData.isAppOf ``getPeer do throwError "not a peer read"
  let .lam _ _ tail _ := args.back!.consumeMData | throwError "not a saved-peer continuation"
  unless tail.consumeMData.isAppOf ``liftWGPrefix do throwError "not a native write"
  unless tail.getAppArgs.back!.consumeMData.isAppOf ``setPeer do throwError "not a saved-peer write"

macro "protocol_source_step" : tactic => `(tactic| first
  | dsimp (config := {failIfUnchanged := true}) only
  | (protocol_update_head; apply updateShape; intro p; exact ⟨rfl,rfl,rfl⟩)
  | (protocol_source_head CausalEffects.atCurrent; exact .socket _)
  | (protocol_source_head liftWGPrefix
     apply Shape.native
     apply PeerMetadata.Shape.access
     simp only [getPeer,getDev,hiddenAlloc,branch,invariant]
     repeat' access_source_step)
  | (protocol_source_head Bind.bind; apply observerBindShape)
  | (protocol_source_head Pure.pure; rw [liftWGObserver_pure];exact .pure _)
  | maintenance_intro
  | split)

noncomputable def canonical (pid : PeerId) (bytes : Key) :
    Shape (liftWGObserver (ProtocolSocket.observed Event.protocolSocket scope? pid bytes)) := by
  unfold ProtocolSocket.observed ProtocolSocket.bufferWith
  repeat' protocol_source_step

theorem socket_at (args : ProtocolSocket.Args) (w : World) (h : History) :
    runPrefix (socket args) w h=runPrefix (liftWGObserver
      (ProtocolSocket.socket Event.protocolSocket (CausalScope.current scope? h) args)) w h := rfl

theorem socket_remaining {w : World} (point : NativeSocket.Point args w.wg w.ambient v b) (h : History) :
    ∃remaining,runPrefix (socket args) w h=runPrefix remaining {w with wg:=v,ambient:=b} h := by
  rw [socket_at]
  exact point.receipt_remaining h Event.protocolSocket (CausalScope.current scope? h)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProtocolPoints
