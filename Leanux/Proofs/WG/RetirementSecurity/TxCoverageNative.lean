import Leanux.Proofs.WG.RetirementSecurity.TxCoverageStaging

/-! Shared native frames for TX coverage. These preserve the owning logical
queues and actual cell presence; reads, key maintenance and peer reference
bookkeeping cannot discard an allocated packet obligation. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxCoverageNative
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits
variable {locals : List TxLocalBatch}

abbrev Inv := TxCoverage locals

theorem contents {action : WG.M α} (queues : SameView txQueueContents action)
    (packets : SameView TxDisposition.txPackets action) : Preserves (Inv (locals:=locals)) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact before.cells ((ProjectedAction.iff_run_ambient _ _ _).mp packets w a result v b run)
    ((ProjectedAction.iff_run_ambient _ _ _).mp queues w a result v b run)

theorem wire {action : WG.M α} (queues : SameView handoffTxView action)
    (packets : SameView txCryptWire action) : Preserves (Inv (locals:=locals)) action :=
  coverage_passive packets queues

theorem contents_wire {action : WG.M α} (queues : SameView txQueueContents action)
    (packets : SameView txCryptWire action) : Preserves (Inv (locals:=locals)) action :=
  contents queues (packets.factor Prod.snd)

theorem store {action : WG.M α} (same : SameWGStore action) : Preserves (Inv (locals:=locals)) action :=
  contents (same.of_factor (fun s=>txQueueContents {dev:=s.dev}) _ (fun _=>rfl))
    (same.of_factor (fun s=>TxDisposition.txPackets {dev:=s.dev}) _ (fun _=>rfl))

theorem modify_device (f : Device→Device) (peers : ∀d,(f d).peers=d.peers)
    (packets : ∀d,(f d).txSkbs=d.txSkbs) : Preserves (Inv (locals:=locals)) (modifyDev f) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases run
  apply before.cells
  · funext id
    simp [TxDisposition.txPackets,Option.bind_map,Function.comp_def,packets]
  · funext pid
    simp [txQueueContents,handoffTxView,Option.bind_map,Function.comp_def,peers]

theorem peer_put (pid : Option PeerId) : Preserves (Inv (locals:=locals)) (peerPut pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  exact before.peer_put pid a b run

theorem staged (pid : PeerId) : Preserves (Inv (locals:=locals)) (sendStagedPackets pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  exact before.staged pid a b run

end Leanux.Proofs.WG.RetirementSecurity.TxCoverageNative
