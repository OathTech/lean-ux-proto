import Leanux.Proofs.WG.TimerDiscipline.SessionFrontierEffects
import Leanux.Proofs.WG.TimerDiscipline.SessionFrontierFrames
import Leanux.Proofs.WG.TimerDiscipline.HandshakeJournalPairSource

/-! Carry the actual persistent counter through the unchanged session/hook observer and original handshake caller factories. Stop retains strict history order; the counter bound is a normal-return property. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

theorem session_frontier (pid : PeerId) :
    StatePrefixPreserves (fun h g _=>Frontier h g.keypairCounter) Ordered (session pid) := by
  intro g a h prior
  have eq:=session_exact pid g a h
  change runPrefix ((session pid).run g) a h=_ at eq
  rw [eq]
  cases run : ((beginSession pid).run g).run a with
  | error stop => exact ⟨[],by simp,prior.1,True.intro⟩
  | ok out =>
    obtain ⟨⟨begun,next⟩,inputs⟩:=out
    let r : SessionReceipt := ⟨pid,Campaign2.snapshot g a,begun,Campaign2.snapshot next inputs⟩
    have valid : r.Valid := ⟨g,a,next,inputs,rfl,rfl,run⟩
    have post:=Frontier.session (r:=r) prior valid.counter
    exact ⟨[.session r],rfl,post.1,post⟩

theorem hook_frontier (kind : HookJournal.Hook) (pid : PeerId) :
    StatePrefixPreserves (fun h g _=>Frontier h g.keypairCounter) Ordered (hook kind pid) := by
  intro g a h prior
  have eq:=hook_exact kind pid g a h
  change runPrefix ((hook kind pid).run g) a h=_ at eq
  rw [eq]
  let r : HookJournal.Receipt := ⟨kind,pid,Campaign2.snapshot g a,
    Campaign2.observeResult (((HookJournal.action kind pid).run g).run a)⟩
  have added:=prior.hook r
  refine ⟨[.hook r],rfl,added.1,?_⟩
  cases run : ((HookJournal.action kind pid).run g).run a with
  | error _ => trivial
  | ok out =>
    obtain ⟨⟨value,next⟩,inputs⟩:=out
    have same:=counter_hook kind pid g a value next inputs run
    simpa only [r,run,same] using added
theorem lift_frontier_mono {α : Type} (action : WG.M α)
    (grow : ∀g a value final after,((action.run g).run a)=.ok ((value,final),after)→
      g.keypairCounter≤final.keypairCounter) :
    StatePrefixPreserves (fun h g _=>Frontier h g.keypairCounter) Ordered
      (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift action (fun _ _ _ prior=>prior.1)
  intro h g a value final after prior run
  exact prior.mono (grow g a value final after run)

theorem lift_frontier {α : Type} (action : WG.M α) (same : CounterSame action) :
    StatePrefixPreserves (fun h g _=>Frontier h g.keypairCounter) Ordered
      (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift action (fun _ _ _ prior=>prior.1)
  intro h g a value final after prior run
  simpa only [same g a value final after run] using prior
theorem pure_frontier {α : Type} (x : α) :
    StatePrefixPreserves (fun h g _=>Frontier h g.keypairCounter) Ordered (pure x : Obs α) :=
  StatePrefixEnsures.pure x (fun _ _ _ prior=>prior.1) (fun _ _ _ prior=>prior)
open Origins
macro "journal_counter_lift" : tactic => `(tactic|
  first
    | (maintenance_lift_action_head createResponse; apply lift_frontier; exact counter_snapshot (Keypairs.WGTransitions.createResponse_sameSnapshot _))
    | (maintenance_lift_action_head addMacToPacket; apply lift_frontier; exact counter_snapshot (Keypairs.WGTransitions.addMacToPacket_sameSnapshot _ _))
    | (maintenance_lift_action_head sendBufferToPeer; apply lift_frontier; exact counter_snapshot (Keypairs.WGTransitions.sendBufferToPeer_sameSnapshot _ _))
    | (maintenance_lift_action_head consumeInitiation; apply lift_frontier; exact counter_snapshot (Keypairs.WGTransitions.consumeInitiation_sameSnapshot _))
    | (maintenance_lift_action_head consumeResponse; apply lift_frontier; exact counter_snapshot (Keypairs.WGTransitions.consumeResponse_sameSnapshot _))
    | (maintenance_lift_action_head setPeerEndpointFromSkb; apply lift_frontier; exact counter_snapshot (Keypairs.WGTransitions.setPeerEndpointFromSkb_sameSnapshot _ _))
    | (maintenance_lift_action_head peerPut; apply lift_frontier; exact counter_snapshot (Keypairs.WGFrames.peerPut_sameSnapshot _))
    | (maintenance_lift_action_head getDev; apply lift_frontier; exact counter_snapshot Keypairs.WGFrames.getDev_sameSnapshot)
    | (maintenance_lift_action_head cookieMessageConsume; apply lift_frontier; exact counter_snapshot (Keypairs.WGMore.cookieMessageConsume_sameSnapshot _))
    | (maintenance_lift_action_head cookieValidatePacket; apply lift_frontier; exact counter_pending (Noise.PendingTickets.cookieValidatePacket_frame _ _ _))
    | (maintenance_lift_action_head Cookies.loadPhase; apply lift_frontier; exact counter_pending Noise.PendingTickets.loadPhase_frame)
    | (maintenance_lift_action_head sendHandshakeCookie; apply lift_frontier; exact counter_pending (Noise.PendingTickets.sendHandshakeCookie_frame _ _))
    | (maintenance_lift_action_head sendKeepalive; apply lift_frontier; exact counter_retained (Noise.PendingTickets.sendKeepalive_retained _))
    | (maintenance_lift_action_head modifyDev; apply lift_frontier; exact counter_modifyDev _)
    | (maintenance_lift_action_head Bind.bind; apply lift_frontier; exact counter_modifyPeer _ _)
    | (maintenance_head liftWGPrefix; apply lift_frontier; apply counter_snapshot; snapshot_source [] using []))
macro "journal_frontier" : tactic => `(tactic|
  repeat' first
    | (maintenance_head session; exact session_frontier _)
    | (maintenance_head hook; exact hook_frontier _ _)
    | journal_counter_lift
    | (maintenance_head Pure.pure; exact pure_frontier _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind
        (Q:=fun _ h g _=>Frontier h g.keypairCounter))
    | maintenance_intro
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | contradiction)
theorem response_frontier (pid : PeerId) :
    StatePrefixPreserves (fun h g _=>Frontier h g.keypairCounter) Ordered (response pid) := by
  unfold response HandshakeSources.responseWith
  dsimp (config:={zeta:=false}) only [ops]
  change StatePrefixEnsures _ _ _ (fun _ h (g : WGWorld) _=>Frontier h g.keypairCounter)
  journal_frontier
theorem afterMac_frontier (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    StatePrefixPreserves (fun h g _=>Frontier h g.keypairCounter) Ordered (afterMac msg src loaded mac) := by
  unfold afterMac HandshakeSources.afterMacWith
  simp (config:={zeta:=false}) only [←response_eq]
  dsimp (config:={zeta:=false}) only [ops]
  change StatePrefixEnsures _ _ _ (fun _ h (g : WGWorld) _=>Frontier h g.keypairCounter)
  repeat' first
    | (maintenance_head response; exact response_frontier _)
    | (maintenance_head session; exact session_frontier _)
    | (maintenance_head hook; exact hook_frontier _ _)
    | journal_counter_lift
    | (maintenance_head Pure.pure; exact pure_frontier _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind
        (Q:=fun _ h (g : WGWorld) _=>Frontier h g.keypairCounter))
    | maintenance_intro
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | contradiction
theorem reception_frontier (msg : List UInt8) (src : SkbSource) :
    StatePrefixPreserves (fun h g _=>Frontier h g.keypairCounter) Ordered (reception msg src) := by
  unfold reception HandshakeSources.receptionWith
  apply StatePrefixEnsures.bind
    (lift_frontier _ (by apply counter_snapshot; snapshot_source [] using []))
  intro cookie
  split
  · exact StatePrefixEnsures.bind
      (lift_frontier _ (counter_snapshot (Keypairs.WGMore.cookieMessageConsume_sameSnapshot _)))
      (fun _=>pure_frontier _)
  · apply StatePrefixEnsures.bind (lift_frontier _ (counter_pending Noise.PendingTickets.loadPhase_frame))
    intro loaded
    apply StatePrefixEnsures.bind (lift_frontier _ (counter_pending (Noise.PendingTickets.cookieValidatePacket_frame _ _ _)))
    intro mac
    exact afterMac_frontier msg src loaded mac
theorem step_frontier :
    StatePrefixPreserves (fun h g _=>Frontier h g.keypairCounter) Ordered step := by
  unfold step HandshakeSources.stepWith
  apply StatePrefixEnsures.bind (lift_frontier _ (counter_snapshot Keypairs.WGFrames.getDev_sameSnapshot))
  intro d
  cases d.handshakeQueue.consume with
  | mk packet ring =>
    cases packet with
    | none =>
      exact StatePrefixEnsures.bind
        (lift_frontier _ (by apply counter_snapshot; snapshot_source [] using []))
        (fun _=>pure_frontier _)
    | some packet =>
      obtain ⟨msg,src⟩:=packet
      apply StatePrefixEnsures.bind
        (lift_frontier _ (by apply counter_snapshot; snapshot_source [] using []))
      intro _
      apply StatePrefixEnsures.bind (lift_frontier _ (counter_modifyDev _))
      intro _
      apply StatePrefixEnsures.bind (reception_frontier msg src)
      intro _
      exact StatePrefixEnsures.bind (lift_frontier _ (counter_modifyDev _)) (fun _=>pure_frontier _)

theorem inspect_allocation {α : Type} (observer : Obs α)
    (preserves : StatePrefixPreserves (fun h g _=>Frontier h g.keypairCounter) Ordered observer)
    (paired : StatePrefixPreserves (fun h _ _=>Paired h) Paired observer) :
    Campaign2.Returns (inspect observer) (fun _=>True) (fun result _=>AllocationFacts result) := by
  intro g a _
  obtain ⟨_,_,ordered,post⟩:=preserves g a [] (frontier_nil _)
  obtain ⟨_,_,hp,_⟩:=paired g a [] Paired.nil
  refine ⟨_,g,a,rfl,ordered,ordered.nodup,fun serial=>⟨ordered.session_count serial,ordered.derived_count hp serial⟩,?_⟩
  change (match Campaign2.observeResult (runWGPrefix observer g a []).1 with
    | .error _ => True
    | .ok (_,last) => Frontier (runWGPrefix observer g a []).2 last.wg.keypairCounter)
  cases run : (runPrefix (observer.run g) a []).1 with
  | error stop => simp only [runWGPrefix,runStatePrefix,run,Campaign2.observeResult,Except.map]
  | ok out =>
    obtain ⟨⟨value,last⟩,after⟩:=out
    simpa only [runWGPrefix,runStatePrefix,run,Campaign2.observeResult,Except.map,Campaign2.snapshot,Campaign2.core] using post

end Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
