import Leanux.Proofs.WG.TransmitSecurity.StagedTransferFrames
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceKeepalive

/-! Exact source preparation of a keepalive. Its canonical empty payload is
bound to the caller's peer and actual device MTU; this is not an authentication
or causal-root certificate. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open RetirementSecurity.OccurrenceHandshake
set_option pp.structureInstances false

/-- Native preparation either preserves a nonempty queue, declines allocation
without editing the empty queue, or stages exactly one empty keepalive for the
specified peer. The following native send uses that same peer. -/
theorem keepalive_prepare (pid : PeerId) (r : WGRunWitness Bool)
    (valid : r.Valid (keepalivePrepare pid)) :
    ∃ d p, r.before.dev = some d ∧ d.peers[pid]? = some p ∧
      ((p.staged ≠ [] ∧ r.value = true ∧ r.after = r.before) ∨
       (p.staged = [] ∧ r.value = false ∧ r.after = r.before) ∨
       (p.staged = [] ∧ r.value = true ∧
        r.after = {r.before with dev := some {d with peers := d.peers.insert pid {p with staged := [{mtu := d.mtu}]}}})) := by
  unfold WGRunWitness.Valid keepalivePrepare at valid
  rw [MaterialOrigin.bind_ok_ambient] at valid
  obtain ⟨p,middle,clock,read,tail⟩ := valid
  obtain ⟨rfl,rfl,d,device,resident⟩ := Origins.getPeer_return pid r.before middle p r.ambientBefore clock read
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨flag,u,c,guard,tail⟩ := tail
  have same : u = r.before := by cases guard; rfl
  have choice : flag = p.staged.isEmpty := by cases guard; rfl
  subst u
  rw [choice] at tail
  refine ⟨d,p,device,resident,?_⟩
  by_cases empty : p.staged = []
  · have isEmpty : p.staged.isEmpty = true := by simp [empty]
    simp only [isEmpty,ite_true] at tail
    rw [MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨allocation,u,c,allocated,tail⟩ := tail
    have unchanged : u = r.before :=
      (hoare_iff_run_ambient _ _ _).mp
        (hoare_liftAmbient (AmbientM.hiddenAlloc .keepaliveSkb) (fun w : WGWorld => w = r.before))
        r.before _ allocation u c rfl allocated
    subst u
    cases allocation with
    | false =>
      simp [branch,AmbientM.branch] at tail
      exact Or.inr (Or.inl ⟨empty,tail.1.1,tail.1.2.symm⟩)
    | true =>
      simp [branch,AmbientM.branch,getDev,device,setPeer,modifyDev,empty] at tail
      exact Or.inr (Or.inr ⟨empty,tail.1.1,tail.1.2.symm⟩)
  · have isEmpty : p.staged.isEmpty = false := by cases h : p.staged <;> simp_all
    simp [isEmpty] at tail
    exact Or.inl ⟨empty,tail.1.1,tail.1.2.symm⟩

theorem keepalive_projection (pid : PeerId) (r : WGRunWitness Bool)
    (valid : r.Valid (keepalivePrepare pid)) :
    dropped r.after = dropped r.before ∧
      (∀ q, pid ≠ q → stagedAt r.after q = stagedAt r.before q) ∧
      ∃ stamp packets mtu,
        stagedAt r.before pid = some (stamp,packets) ∧
        r.before.dev.map Device.mtu = some mtu ∧
        (stagedAt r.after pid = some (stamp,packets) ∨
          (packets = [] ∧ r.value = true ∧ stagedAt r.after pid = some (stamp,[{mtu}]))) := by
  obtain ⟨d,p,device,resident,outcome⟩ := keepalive_prepare pid r valid
  rcases outcome with ⟨_,_,same⟩ | ⟨_,_,same⟩ | ⟨empty,ready,changed⟩
  · rw [same]
    exact ⟨rfl,fun _ _ => rfl,p.internalId,p.staged,d.mtu,
      by simp [stagedAt,device,resident],by simp [device],Or.inl (by simp [stagedAt,device,resident])⟩
  · rw [same]
    exact ⟨rfl,fun _ _ => rfl,p.internalId,p.staged,d.mtu,
      by simp [stagedAt,device,resident],by simp [device],Or.inl (by simp [stagedAt,device,resident])⟩
  · refine ⟨?_,?_,p.internalId,p.staged,d.mtu,?_,?_,Or.inr ⟨empty,ready,?_⟩⟩
    · simp [dropped,changed,device]
    · intro q different
      simp [stagedAt,changed,device,Std.TreeMap.getElem?_insert,different]
    · simp [stagedAt,device,resident]
    · simp [device]
    · simp [stagedAt,changed]

end Leanux.Proofs.WG.TransmitSecurity.Staged
