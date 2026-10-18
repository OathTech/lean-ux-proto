import Leanux.Proofs.WG.Queues.BaseCoherence

namespace Leanux.Proofs.WG.Index.FundedBase
open Leanux Leanux.WG Leanux.Proofs.WG
open Queues.RxCredits Queues.RxCredits.DurableHolders

variable {holders : DurableHolders} {cs : Ledger} {loans : Reservations}
  {w : WGWorld} {d : Device} {pid : PeerId} {p : Peer}

/-- Funding recovers the actual allocation stamp of a base-list occurrence. -/
theorem resident_base_reservation
    (funded : holders.Funded cs loans w)
    (hd : w.dev = some d) (hp : d.peers[pid]? = some p)
    (member : pid ∈ d.peerList) :
    (⟨d.ifindex,pid,p.internalId⟩ : Owner) ∈ holders.base := by
  have mapped : pid ∈ holders.base.map Owner.slot := by
    rw [funded.aligned.base]
    simpa only [hd,Option.map_some,Option.getD_some] using member
  obtain ⟨o,inside,slot⟩ := List.mem_map.mp mapped
  have held : o ∈ holders.owners := by
    simp only [DurableHolders.owners,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl inside))))
  obtain ⟨q,hr⟩ := funded.resident held
  obtain ⟨e,he,epoch,hq,stamp⟩ := resident_fields hr
  have ed : e = d := Option.some.inj (he.symm.trans hd)
  subst e
  have qp : q = p := Option.some.inj
    ((show d.peers[pid]? = some q by simpa only [slot] using hq).symm.trans hp)
  subst q
  have same : o = ⟨d.ifindex,pid,p.internalId⟩ := by
    cases o
    simp_all
  simpa only [same] using inside

/-- Configured identity and table/base coherence supply the base occurrence
for every actual nondead resident; it is not a new reachability premise. -/
theorem live_base_reservation
    (configured : ConfiguredIdentity.Inv w) (base : BaseCoherence.Inv w)
    (funded : holders.Funded cs loans w)
    (hd : w.dev = some d) (hp : d.peers[pid]? = some p)
    (live : p.isDead = false) :
    (⟨d.ifindex,pid,p.internalId⟩ : Owner) ∈ holders.base := by
  have ci := configured (ConfiguredIdentity.state d)
    (by simp only [ConfiguredIdentity.view,hd,Option.map_some])
  have row : (p.remoteStatic,pid) ∈ d.peerHashtable :=
    ci.live pid (ConfiguredIdentity.cell p)
      (by simp only [ConfiguredIdentity.state,hp,Option.map_some]) live (by simp)
  have member : pid ∈ d.peerList := by
    have := base.2 (p.remoteStatic,pid)
      (by simpa only [BaseCoherence.rows,hd,Option.map_some,Option.getD_some] using row)
    simpa only [BaseCoherence.slots,hd,Option.map_some,Option.getD_some] using this
  exact resident_base_reservation funded hd hp member

/-- The base occurrence contributes one credit in addition to all explicit
loans and RX carriers, including repeated occurrences of the same owner. -/
theorem live_base_credit
    (configured : ConfiguredIdentity.Inv w) (base : BaseCoherence.Inv w)
    (funded : holders.Funded cs loans w)
    (hd : w.dev = some d) (hp : d.peers[pid]? = some p)
    (live : p.isDead = false) :
    (⟨d.ifindex,pid,p.internalId⟩ : Owner) ∈ holders.base ∧
      1 + demand cs loans ⟨d.ifindex,pid,p.internalId⟩ ≤ p.refcount := by
  have member := live_base_reservation configured base funded hd hp live
  have held : (⟨d.ifindex,pid,p.internalId⟩ : Owner) ∈ holders.owners := by
    simp only [DurableHolders.owners,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl member))))
  have positive : 0 < holders.owners.count ⟨d.ifindex,pid,p.internalId⟩ :=
    List.count_pos_iff.mpr held
  have bound : demand cs (holders.owners ++ loans) ⟨d.ifindex,pid,p.internalId⟩
      ≤ p.refcount := by
    simpa only [balance,resident_at hd hp,Option.map_some,Option.getD_some]
      using funded.carriers.funded ⟨d.ifindex,pid,p.internalId⟩
  refine ⟨member,?_⟩
  simp only [demand,List.count_append] at bound ⊢
  omega

/-- Paying a separately held same-owner loan cannot be the final reference
while the actual peer is live and its base occurrence remains funded. -/
theorem live_loan_credit
    (configured : ConfiguredIdentity.Inv w) (base : BaseCoherence.Inv w)
    (funded : holders.Funded cs (⟨d.ifindex,pid,p.internalId⟩ :: loans) w)
    (hd : w.dev = some d) (hp : d.peers[pid]? = some p)
    (live : p.isDead = false) :
    2 + demand cs loans ⟨d.ifindex,pid,p.internalId⟩ ≤ p.refcount := by
  have bound := (live_base_credit configured base funded hd hp live).2
  simp only [demand,List.count_cons_self] at bound ⊢
  omega

end Leanux.Proofs.WG.Index.FundedBase
