import Leanux.Proofs.WG.Index.OwnerCoherenceAipRemovalFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceSlotRemovalFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- Local owner/slot variant of C1 WGBase.peerMakeDead_spec, with the actual
resident dead flag and cleanup context. Allowed-IP lists and trie shape are
unrestricted; every fact is derived from this same normal execution. -/
theorem peerMakeDead_spec_aipOwner_variant (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (coherent : HashedOwnersCoherent d)
    (covered : LastOwnerCovered d pid p) :
    Ensures (peerMakeDead pid) (fun g => g.dev = some d)
      (fun _ g => ∃ current q, g.dev = some current ∧ current.peers[pid]? = some q ∧
        q.isDead = true ∧ q.refcount = p.refcount ∧ HashedOwnersCoherent current ∧
        LastOwnerCovered current pid q ∧ current.numPeers = d.numPeers ∧
        current.sendWorkQueue = d.sendWorkQueue ∧ current.clearWorkQueue = d.clearWorkQueue) := by
  have unlist : Ensures (modifyDev (Config.unlistPeer · pid)) (fun g => g.dev = some d)
      (fun _ g => g.dev.map aipOwnerView = some (aipOwnerView d)) := by
    intro g ambient value final after device run
    cases run
    simp [device,Config.unlistPeer,aipOwnerView]
  rw [Config.peerMakeDead_source]
  refine ensures_bind _ _ unlist ?_
  intro _
  refine ensures_bind _ _ (removeByPeer_spec_aipOwner_variant pid (some (aipOwnerView d))) ?_
  intro _ g ambient value final after pre run
  cases device : g.dev with
  | none => simp [device] at pre
  | some removed =>
    have same : aipOwnerView removed = aipOwnerView d := by simpa [device] using pre
    obtain ⟨safe,q,found,count,coverage,number,send,clear⟩ :=
      aipOwnerView_transport d removed pid p same resident coherent covered
    let marked := {q with isDead := true}
    let unlinked : Device := {removed with peerHashtable := removed.peerHashtable.filter (·.2 != pid)}
    let dead := Config.withPeer unlinked pid marked
    let inputs := {ambient with steps := ambient.steps.push {
      decision := .pubkeyRemoveHashed, outcome := removed.peerHashtable.any (·.2 == pid),
      netRx := ambient.netRxSection}}
    have actual : ((Config.makeDeadAfterRemoval pid).run g).run ambient =
        .ok (((),{g with dev := some dead}),inputs) := by
      simp [Config.makeDeadAfterRemoval,getDev,device,branch,AmbientM.branch,modifyDev,
        getPeer,setPeer,found,dead,unlinked,marked,Config.withPeer,inputs]
      rfl
    rw [actual] at run
    have finalEq : {g with dev := some dead} = final :=
      congrArg (fun result => result.1.2) (Except.ok.inj run)
    rw [← finalEq]
    refine ⟨dead,marked,rfl,?_,rfl,count,?_,?_,number,send,clear⟩
    · simp [dead,Config.withPeer]
    · exact peerWrite_owner_coherent unlinked pid q marked found rfl rfl safe
    · exact peerWrite_lastOwnerCovered unlinked pid q marked rfl rfl coverage

end Leanux.Proofs.WG.Index
