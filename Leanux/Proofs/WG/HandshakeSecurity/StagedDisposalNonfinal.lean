import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalFrames
import Leanux.Proofs.WG.Queues.TxDispositionBorrow

/-! A native strict acquire supplies its own nonfinal repayment fact. This
can justify an omitted disposal observation only when callers transport the
actual acquired peer's count to that cut; no initialized empty-queue premise
is assumed here. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def Nonfinal (pid : PeerId) (w : WGWorld) : Prop :=
  ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧ 1 < p.refcount

theorem acquired_nonfinal (pid : PeerId) (r : WGRunWitness Unit)
    (run : r.Valid (peerGet pid)) : Nonfinal pid r.after := by
  obtain ⟨d,p,_,_,positive,after⟩ := (hoare_iff_run_ambient _ _ _).mp
    (PeerBorrow.strict_acquire_spec pid (wgStoreView r.before))
    r.before r.ambientBefore r.value r.after r.ambientAfter rfl run
  have device := congrArg WGStoreView.dev after
  refine ⟨{d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}},
    {p with refcount := p.refcount + 1},device,Std.TreeMap.getElem?_insert_self,?_⟩
  simpa using positive

theorem Nonfinal.store (before : Nonfinal pid w) (same : wgStoreView v = wgStoreView w) :
    Nonfinal pid v := by
  obtain ⟨d,p,device,resident,positive⟩ := before
  exact ⟨d,p,(congrArg WGStoreView.dev same).trans device,resident,positive⟩

/-- A completed native release cut on a still-borrowed peer cannot select the
counted erase arm, regardless of the staged queue's contents. -/
theorem cut_nonfinal (pid : PeerId) (r : WGRunWitness (Option (PeerId × Peer)))
    (run : r.Valid (releaseCut (some pid))) (before : Nonfinal pid r.before) :
    r.value = none := by
  cases value : r.value with
  | none => rfl
  | some out =>
    rcases out with ⟨selected,original⟩
    obtain ⟨d,selectedEq,device,resident,count,_⟩ := release_exact (some pid) r run selected original value
    have equal : pid = selected := Option.some.inj selectedEq
    subst selected
    obtain ⟨other,p,beforeDevice,stored,positive⟩ := before
    have sameDevice : other = d := Option.some.inj (beforeDevice.symm.trans device)
    subst other
    have samePeer : p = original := Option.some.inj (stored.symm.trans resident)
    subst p
    omega

theorem acquired_cut_nonfinal (pid : PeerId) (acquire : WGRunWitness Unit)
    (release : WGRunWitness (Option (PeerId × Peer)))
    (got : acquire.Valid (peerGet pid))
    (continued : wgStoreView release.before = wgStoreView acquire.after)
    (paid : release.Valid (releaseCut (some pid))) : release.value = none :=
  cut_nonfinal pid release paid ((acquired_nonfinal pid acquire got).store continued)

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal
