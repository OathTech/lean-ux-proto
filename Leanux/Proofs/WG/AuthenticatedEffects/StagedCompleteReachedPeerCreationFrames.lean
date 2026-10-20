import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerCreationSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryPeerCreationFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAllocatedCarrier

/-! The native front derives a vacant slot from initialized allocation.
Insertion preserves existing ticket queues and cells even though an empty
peer changes the full resident-peer projection. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerCreation
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal Queues.RxCredits

theorem core_account (before : CompleteCarrier.Accounted h ledger [] [] w) (vacant : Vacant pid w)
    (performed : ((Peers.peerCreateCore pid key).run w).run a=.ok (((),v),b)) :
    CompleteCarrier.Accounted h ledger [] [] v := by
  have staged : ∀epoch stamp,QueueGeometry.queues w epoch pid stamp=[] := by
    intro epoch stamp
    cases dev : w.dev with
    | none=>simp [QueueGeometry.queues,Staged.Obligations.stagedPackets,Staged.stagedAt,dev]
    | some d=>simp [QueueGeometry.queues,Staged.Obligations.stagedPackets,Staged.stagedAt,dev,vacant d dev]
  have queues := (hoare_iff_run_ambient _ _ _).mp (PeerCreationFrames.core_queues (QueueGeometry.queues w) pid key staged) _ _ _ _ _ rfl performed
  have owners : txQueueContents v=txQueueContents w := by
    rw [Peers.peerCreateCore_run] at performed
    cases performed
    funext other
    cases dev : w.dev with
    | none=>simp [Peers.creationCoreWorld,txQueueContents,handoffTxView,dev]
    | some d=>
      by_cases same : pid=other
      · subst other
        simp [Peers.creationCoreWorld,txQueueContents,handoffTxView,dev,Peers.createdPeer,PrevQueue.all,vacant d dev]
      · simp [Peers.creationCoreWorld,txQueueContents,handoffTxView,dev,Std.TreeMap.getElem?_insert,same]
  have geometry : Packets.epoch v=Packets.epoch w ∧ Packets.snapshot v=Packets.snapshot w ∧ TxDisposition.txPackets v=TxDisposition.txPackets w := by
    rw [Peers.peerCreateCore_run] at performed
    cases performed
    cases dev : w.dev <;> simp [Peers.creationCoreWorld,Packets.epoch,Packets.snapshot,Packets.deviceStore,dev]
    all_goals funext id; simp [TxDisposition.txPackets,dev]
  exact ⟨QueueGeometry.transport before.entry geometry.1 queues geometry.2.2 geometry.2.1 owners,before.complete⟩

private theorem ambient_then {α β : Type} (body : AmbientM α) (next : α → WG.M β)
    {P : WGWorld → Prop} {Q : β → WGWorld → Prop} (tail : ∀value,Hoare (next value) P Q) :
    Hoare ((monadLift body : WG.M α) >>= next) P Q :=
  hoare_bind _ _ (hoare_liftAmbient body P) tail

open Lean Meta Elab Tactic in
elab "creation_hoare_head " expected:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Hoare do throwError "not a Hoare contract"
  let args := target.getAppArgs
  let action := args[args.size-3]!.consumeMData.headBeta
  let name ← realizeGlobalConstNoOverloadWithInfo expected
  unless action.getAppFn.constName? == some name do throwError "different native action"

theorem front_admitted (bounded : PeerSlotsBounded w)
    (performed : (front.run w).run a=.ok ((.ok pid,v),b)) : v=w ∧ Vacant pid v := by
  unfold front at performed
  rw [MaterialOrigin.bind_ok_ambient] at performed
  obtain ⟨d,u,c,read,rest⟩:=performed
  cases device : w.dev with
  | none=>simp [getDev,device,invariant,AmbientM.invariant] at read; cases read
  | some current=>
      simp [getDev,device] at read
      obtain ⟨⟨rfl,rfl⟩,rfl⟩:=read
      have vacant : Vacant current.nextPeer w := by
        intro other equal
        have same: current=other := Option.some.inj (device.symm.trans equal)
        subst other
        cases found : current.peers[current.nextPeer]? with
        | none=>rfl
        | some peer=>exact False.elim ((Nat.lt_irrefl _) (bounded current device _ peer found))
      have checks : Hoare (do
          if ← branchCmp .peerCreateMaxPeers (current.numPeers ≥ MAX_PEERS_PER_DEVICE) current.numPeers MAX_PEERS_PER_DEVICE then return .error (-ENOMEM)
          if ← branch .peerCreateNoMem !(←hiddenAlloc .kmemCacheZallocPeer) then return .error (-ENOMEM)
          if ← branch .peerCreateDstCacheFail false then return .error (-ENOMEM)
          pure (.ok current.nextPeer) : WG.M (Except Int PeerId))
          (fun world=>world=w) (fun result world=>world=w ∧ (result=.ok pid → Vacant pid world)) := by
        repeat' first
          | (creation_hoare_head Bind.bind; apply ambient_then; intro value)
          | dsimp (config := {failIfUnchanged := true}) only
          | split
          | (creation_hoare_head Pure.pure; apply hoare_consequence (hoare_pure _ _)
             · intro world before; exact before
             · intro result world after
               rcases after with ⟨rfl,rfl⟩
               exact ⟨rfl,by intro equal; cases equal <;> exact vacant⟩)
      have checked := (hoare_iff_run_ambient _ _ _).mp checks _ _ _ _ _ rfl rest
      exact ⟨checked.1,checked.2 rfl⟩

theorem CorePoint.accounted (before : CompleteCarrier.Accounted h ledger [] [] w)
    (vacant : Vacant pid w) (point : CorePoint pid key w a v b) : CompleteCarrier.Accounted h ledger [] [] v := by
  cases point with
  | front point=>exact before.same_view point.frame
  | returned performed=>exact core_account before vacant performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerCreation
