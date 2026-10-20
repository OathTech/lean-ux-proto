import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConfigMetadataCanonical
import Leanux.Proofs.WG.Peers.CreationAccess

/-! Creation points follow the actual guards, allocation writes and metadata
tail. The core ends at its peer-store write; no receipt or fictitious suffix
is used to certify a point. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerCreation
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal Queues.RxCredits

def front : WG.M (Except Int PeerId) := do
  let d ← getDev
  if ← branchCmp .peerCreateMaxPeers (d.numPeers ≥ MAX_PEERS_PER_DEVICE) d.numPeers MAX_PEERS_PER_DEVICE then
    return .error (-ENOMEM)
  if ← branch .peerCreateNoMem !(←hiddenAlloc .kmemCacheZallocPeer) then return .error (-ENOMEM)
  if ← branch .peerCreateDstCacheFail false then return .error (-ENOMEM)
  return .ok d.nextPeer

def tail (pid : PeerId) (key : Key) (psk : Option Key) : WG.M (Except Int PeerId) := do
  dstCacheReset pid
  handshakeInit pid psk
  resetLastSentHandshake pid
  modifyDev fun d=>{d with peerList:=d.peerList++[pid],peerHashtable:=(key,pid)::d.peerHashtable,numPeers:=d.numPeers+1}
  pure (.ok pid)

def finish (key : Key) (psk : Option Key) : Except Int PeerId → WG.M (Except Int PeerId)
  | .error err=>pure (.error err)
  | .ok pid=>Peers.peerCreateCore pid key >>= fun _=>tail pid key psk

theorem source (key : Key) (psk : Option Key) : peerCreate key psk=(front >>= finish key psk) := by
  rw [←Peers.peerCreateFactored_eq]
  simp only [Peers.peerCreateFactored,front,bind_assoc]
  repeat' first
    | rfl
    | apply RxWorkers.bind_congr
    | maintenance_intro
    | split
    | dsimp (config := {failIfUnchanged := true}) only [finish,tail]
    | simp (config := {failIfUnchanged := true}) only [bind_assoc]

noncomputable def frontShape : Access.Shape front := by
  simp only [front,getDev,invariant]
  repeat' access_source_step

noncomputable def tailShape (pid : PeerId) (key : Key) (psk : Option Key) : PeerMetadata.Shape (tail pid key psk) := by
  unfold tail handshakeInit IndexOwner.setPeerWord dstCacheReset
  repeat' first
    | (metadata_source_head precomputeStaticStatic; exact PeerMetadata.precomputeShape _)
    | (metadata_source_head resetLastSentHandshake; exact PeerMetadata.resetHandshakeShape _)
    | metadata_source_step

def coreFront (pid : PeerId) : WG.M Nat := do
  let stamp := (←get).peerCounter+1
  modify fun w=>{w with peerCounter:=stamp}
  modifyDev fun d=>{d with nextPeer:=pid+1}
  pure stamp

theorem core_source (pid : PeerId) (key : Key) : Peers.peerCreateCore pid key=
    (coreFront pid >>= fun stamp=>setPeer pid (Peers.createdPeer key stamp)) := by
  simp only [Peers.peerCreateCore,coreFront,bind_assoc,pure_bind]

noncomputable def coreFrontShape (pid : PeerId) : PeerMetadata.Shape (coreFront pid) := by
  unfold coreFront
  repeat' first
    | (metadata_source_head modify; apply PeerMetadata.Shape.access; apply Access.Shape.write; exact KeyFrames.world _ (fun _=>rfl))
    | metadata_source_step

inductive CorePoint (pid : PeerId) (key : Key) : WGWorld → Ambient → WGWorld → Ambient → Prop where
  | front (point : PeerMetadata.Point (coreFrontShape pid) w a v b) : CorePoint pid key w a v b
  | returned (performed : ((Peers.peerCreateCore pid key).run w).run a=.ok (((),v),b)) : CorePoint pid key w a v b

theorem CorePoint.remaining (point : CorePoint pid key w a v b) :
    ∃rest : WG.M Unit,((Peers.peerCreateCore pid key).run w).run a=(rest.run v).run b := by
  cases point with
  | front point=>
      obtain ⟨rest,same⟩:=point.remaining
      exact ⟨rest >>= fun stamp=>setPeer pid (Peers.createdPeer key stamp),by rw [core_source];simp only [StateT.run_bind,same]⟩
  | returned performed=>exact ⟨pure (),performed⟩

def Vacant (pid : PeerId) (w : WGWorld) : Prop := ∀d,w.dev=some d → d.peers[pid]?=none

inductive Point (key : Key) (psk : Option Key) : WGWorld → Ambient → WGWorld → Ambient → Prop where
  | front (point : Access.Point frontShape w a v b) : Point key psk w a v b
  | core (prepared : (PeerCreation.front.run w).run a=.ok ((.ok pid,u),c))
      (point : CorePoint pid key u c v b) : Point key psk w a v b
  | tail (prepared : (PeerCreation.front.run w).run a=.ok ((.ok pid,u),c))
      (created : ((Peers.peerCreateCore pid key).run u).run c=.ok (((),x),e))
      (point : PeerMetadata.Point (tailShape pid key psk) x e v b) : Point key psk w a v b
  | returned (performed : ((peerCreate key psk).run w).run a=.ok ((value,v),b)) : Point key psk w a v b

theorem Point.remaining (point : Point key psk w a v b) :
    ∃rest : WG.M (Except Int PeerId),((peerCreate key psk).run w).run a=(rest.run v).run b := by
  cases point with
  | front point=>
      obtain ⟨rest,same⟩:=point.remaining
      exact ⟨rest >>= finish key psk,by rw [source];simp only [StateT.run_bind,same]⟩
  | core prepared point=>
      rename_i pid u c
      obtain ⟨rest,same⟩:=point.remaining
      refine ⟨rest >>= fun _=>PeerCreation.tail pid key psk,?_⟩
      rw [source]
      simp only [StateT.run_bind,prepared]
      change (((Peers.peerCreateCore _ key >>= fun _=>PeerCreation.tail _ key psk).run _).run _)=_
      simp only [StateT.run_bind,same]
  | tail prepared created point=>
      obtain ⟨rest,same⟩:=point.remaining
      refine ⟨rest,?_⟩
      rw [source]
      simp only [StateT.run_bind,prepared]
      change (((Peers.peerCreateCore _ key >>= fun _=>PeerCreation.tail _ key psk).run _).run _)=_
      simp only [StateT.run_bind,created]
      exact same
  | returned performed=>exact ⟨pure _,performed⟩

theorem Point.observed_remaining {E : Type} {w : World}
    (point : Point key psk w.wg w.ambient v b) (h : List E) :
    ∃rest : PrefixM E (Except Int PeerId),runPrefix (liftWGObserver (liftWGPrefix (peerCreate key psk))) w h=
      runPrefix rest {w with wg:=v,ambient:=b} h := by
  obtain ⟨rest,same⟩:=point.remaining
  refine ⟨liftWGObserver (liftWGPrefix rest),?_⟩
  simp only [liftWGObserver_run,runWGPrefix_lift,same]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerCreation
