import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalSource
import Leanux.Proofs.WG.TransmitSecurity.StagedTrim

/-! Disposal evidence uses queue positions and allocation stamps. The count
comes from the actual named source arm, not from an inference from absence. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open TransmitSecurity.Staged Lifetimes
set_option pp.structureInstances false

structure Partition (pid : PeerId) (w v : WGWorld) where
  stamp : Nat
  packets : List Packet
  removed : Nat
  bounded : removed ≤ packets.length
  before : stagedAt w pid = some (stamp,packets)
  after : stagedAt v pid = some (stamp,packets.drop removed)
  charged : ∃ count, dropped w = some count ∧ dropped v = some (count+removed)
  epoch : Packets.epoch v = Packets.epoch w
  others : ∀ q, pid ≠ q → stagedAt v q = stagedAt w q

theorem Partition.split (p : Partition pid w v) :
    p.packets.take p.removed ++ p.packets.drop p.removed = p.packets :=
  List.take_append_drop _ _

theorem purge_exact (pid : PeerId) (r : WGRunWitness Unit)
    (valid : r.Valid (purgeStagedPackets pid)) :
    ∃ p : Partition pid r.before r.after, p.removed = p.packets.length := by
  obtain ⟨d,p,device,resident,after⟩ := purge pid r valid
  refine ⟨⟨p.internalId,p.staged,p.staged.length,Nat.le_refl _,?_,?_,?_,?_,?_⟩,rfl⟩
  · simp only [stagedAt,device,Option.bind_some,resident,Option.map_some]
  · simp only [stagedAt,after,Option.bind_some,Std.TreeMap.getElem?_insert_self,
      Option.map_some,List.drop_length]
  · exact ⟨d.txDropped,by simp only [dropped,device,Option.map_some],
      by simp only [dropped,after,Option.map_some]⟩
  · simp only [Packets.epoch,device,after,Option.map_some]
  · intro q different
    simp only [stagedAt,device,after,Option.bind_some,Std.TreeMap.getElem?_insert,
      Std.LawfulEqOrd.compare_eq_iff_eq,different,↓reduceIte]

theorem overflow_epoch (pid : PeerId) (r : WGRunWitness Unit)
    (valid : r.Valid (Lifetimes.xmitTrim pid)) :
    Packets.epoch r.after = Packets.epoch r.before := by
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Origins.Retaining.xmitTrim_material pid)
    r.before r.ambientBefore r.value r.after r.ambientAfter valid
  have epoch := congrArg (Option.map Prod.fst) frame
  simpa only [Origins.view,Packets.epoch,Option.map_map,Function.comp_def] using epoch

theorem overflow_exact (pid : PeerId) (r : WGRunWitness Unit)
    (valid : r.Valid (Lifetimes.xmitTrim pid)) :
    Nonempty (Partition pid r.before r.after) := by
  have source := valid
  unfold WGRunWitness.Valid Lifetimes.xmitTrim at source
  rw [MaterialOrigin.bind_ok_ambient] at source
  obtain ⟨p,middle,clock,read,_⟩ := source
  obtain ⟨_,_,d,device,resident⟩ :=
    Origins.getPeer_return pid r.before middle p r.ambientBefore clock read
  obtain ⟨n,bound,after,count,others,_⟩ := trim_exact pid r valid d p device resident
  exact ⟨⟨p.internalId,p.staged,n,bound,
    by simp only [stagedAt,device,Option.bind_some,resident,Option.map_some],
    after,⟨d.txDropped,by simp only [dropped,device,Option.map_some],count⟩,
    overflow_epoch pid r valid,others⟩⟩

theorem release_exact (peer : Option PeerId)
    (r : WGRunWitness (Option (PeerId × Peer)))
    (valid : r.Valid (releaseCut peer)) (pid : PeerId) (p : Peer)
    (released : r.value = some (pid,p)) :
    ∃ d, peer = some pid ∧ r.before.dev = some d ∧ d.peers[pid]? = some p ∧
      p.refcount = 1 ∧ stagedAt r.after pid = none ∧
      dropped r.after = some (d.txDropped+p.staged.length) ∧
      Packets.epoch r.after = Packets.epoch r.before ∧
      (∀ q, pid ≠ q → stagedAt r.after q = stagedAt r.before q) := by
  rcases r with ⟨value,w,v,a,b⟩
  dsimp only at released
  subst value
  unfold WGRunWitness.Valid at valid
  dsimp only at valid ⊢
  cases peer with
  | none => simp [releaseCut,branch,AmbientM.branch] at valid
  | some selected =>
    cases device : w.dev with
    | none =>
      simp [releaseCut,requireNotPending,getPeer,getDev,device,branch,AmbientM.branch,
        invariant,AmbientM.invariant] at valid
      cases valid
    | some d =>
      cases resident : d.peers[selected]? with
      | none =>
        simp [releaseCut,requireNotPending,getPeer,getDev,device,resident,branch,AmbientM.branch,
          invariant,AmbientM.invariant] at valid
        cases valid
      | some original =>
        have lifted (action : IndexM Unit) : (liftM action : WG.M Unit) = liftIndex action := rfl
        by_cases positive : 0 < original.refcount
        · have nonzero : original.refcount ≠ 0 := by omega
          by_cases final : original.refcount = 1
          all_goals
            simp [releaseCut,requireNotPending,getPeer,getDev,setPeer,modifyDev,
              refcountDecAndTest,branch,branchCmp,indexRemove_eq,indexUnhash,
              lifted,liftIndex_run,CounterWindow.branch_run,CounterWindow.branchCmp_run,
              device,resident,positive,nonzero,final,StateT.run_bind,StateT.run_pure,
              StateT.run_monadLift,CounterWindow.except_ok_bind,CounterWindow.except_pure,
              invariant,AmbientM.invariant,unsupported,AmbientM.unsupported] at valid
          all_goals repeat' first | split at valid | contradiction
          all_goals
            simp [Except.map,StateT.run_map,StateT.run_modify,
              CounterWindow.except_ok_bind,CounterWindow.except_pure] at valid
          all_goals
            rcases valid with ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩
            refine ⟨d,rfl,rfl,resident,final,?_,rfl,?_,?_⟩
            · simp [stagedAt]
            · simp only [Packets.epoch,device,Option.map_some]
            · intro q different
              simp [stagedAt,device,Std.TreeMap.getElem?_erase,
                Std.TreeMap.getElem?_insert,different]
        · have zero : original.refcount = 0 := by omega
          simp [releaseCut,requireNotPending,getPeer,getDev,setPeer,modifyDev,
            refcountDecAndTest,branch,branchCmp,CounterWindow.branch_run,
            CounterWindow.branchCmp_run,device,resident,zero,StateT.run_bind,
            StateT.run_pure,StateT.run_monadLift,CounterWindow.except_ok_bind,
            CounterWindow.except_pure,unsupported,AmbientM.unsupported] at valid
          cases valid

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal
