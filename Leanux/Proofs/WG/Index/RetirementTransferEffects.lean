import Leanux.Proofs.WG.Index.RetirementModel
import Leanux.Proofs.WG.Index.FundedBaseSource
import Leanux.Proofs.WG.Index.AipRemovalFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.Framing
open Queues.RxCredits Queues.RxCredits.DurableHolders Lifetimes

/-- The new reservation is required only for an owner newly marked dead.
Already dead hashed owners retain their original reservation. -/
theorem deadHashedReserved_mark
    (retired added : Reservations) (d final : Device) (target : PeerId)
    (before : DeadHashedReserved retired d)
    (table : final.indexTable = d.indexTable)
    (words : ∀ (kid : KeypairId), (final.keypairs[kid]?).map Keypair.peer =
      (d.keypairs[kid]?).map Keypair.peer)
    (configured : ConfiguredIdentity.state final =
      (ConfiguredIdentity.state d).kill target)
    (newly : ∀ p, d.peers[target]? = some p → p.isDead = false →
      (⟨d.ifindex,target,p.internalId⟩ : Owner) ∈ added) :
    DeadHashedReserved (added ++ retired) final := by
  intro entry member kid key pid p owner keyFound word peerFound dead
  have oldMember : entry ∈ d.indexTable := table ▸ member
  have oldWord : (d.keypairs[kid]?).map Keypair.peer = some (some pid) := by
    rw [← words kid,keyFound]
    exact congrArg some word
  obtain ⟨oldKey,oldKeyFound,oldKeyWord⟩ := Option.map_eq_some_iff.mp oldWord
  have epoch : final.ifindex = d.ifindex := congrArg ConfiguredIdentity.State.epoch configured
  have peer := congrFun (congrArg ConfiguredIdentity.State.peers configured) pid
  by_cases same : target = pid
  · subst target
    have old : (d.peers[pid]?).map (fun q => {ConfiguredIdentity.cell q with dead := true}) =
        some (ConfiguredIdentity.cell p) := by
      simpa [ConfiguredIdentity.state,ConfiguredIdentity.State.kill,peerFound,
        Option.map_map,Function.comp_def] using peer.symm
    obtain ⟨q,found,cell⟩ := Option.map_eq_some_iff.mp old
    have stamp : q.internalId = p.internalId := congrArg ConfiguredIdentity.Cell.stamp cell
    cases priorDead : q.isDead with
    | false =>
      apply List.mem_append.mpr
      left
      simpa only [epoch,←stamp] using newly q found priorDead
    | true =>
      apply List.mem_append.mpr
      right
      simpa only [epoch,←stamp] using
        before entry oldMember kid oldKey pid q owner oldKeyFound oldKeyWord found priorDead
  · have old : (d.peers[pid]?).map ConfiguredIdentity.cell =
        some (ConfiguredIdentity.cell p) := by
      simpa [ConfiguredIdentity.state,ConfiguredIdentity.State.kill,same,peerFound] using peer.symm
    obtain ⟨q,found,cell⟩ := Option.map_eq_some_iff.mp old
    have stamp : q.internalId = p.internalId := congrArg ConfiguredIdentity.Cell.stamp cell
    have priorDead : q.isDead = true :=
      (congrArg ConfiguredIdentity.Cell.dead cell).trans dead
    apply List.mem_append.mpr
    right
    simpa only [epoch,←stamp] using
      before entry oldMember kid oldKey pid q owner oldKeyFound oldKeyWord found priorDead

end Leanux.Proofs.WG.Index
