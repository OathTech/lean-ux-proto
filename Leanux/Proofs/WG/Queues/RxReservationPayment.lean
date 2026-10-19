import Leanux.Proofs.WG.Queues.RxIngressStable

/-! A source-attributed reservation pays for its actual peer release. The
remaining carriers keep their existing inventory and queue multiplicity;
positive funding supplies the entry identity, including final releases. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

/-- A normal put consumes one named reservation, with no unexplained debit
against the credit protecting other packets. Final peer deletion is allowed. -/
theorem reservation_payment (hi : CarrierState cs (o :: loans) w)
    (ambient ambient' : Ambient)
    (run : ((peerPut (some o.slot)).run w).run ambient = .ok (((),v),ambient')) :
    CarrierState cs loans v := by
  have charged : 0 < demand cs (o :: loans) o := by simp [demand]; omega
  obtain ⟨p, resident, bound⟩ := protected_resident hi.funded charged
  obtain ⟨d, hd, epoch, hp, stamp⟩ := resident_fields resident
  have positive : 0 < p.refcount := by omega
  obtain ⟨_, peers, packets⟩ := peerPut_effect o.slot w v d p ambient ambient' hd hp run
  have owner : o = ⟨d.ifindex,o.slot,p.internalId⟩ := by cases o; simp_all
  have funded : Protected cs loans v := by
    intro q
    have old := hi.funded q
    have delta := (balance_view (o := q) peers).trans (payment_balance hd hp positive q)
    rw [←owner] at delta
    by_cases same : q = o
    · subst q
      simp only [ite_true] at delta
      simp only [demand, List.count_cons_self] at old
      unfold demand
      omega
    · simp only [ite_eq_right same] at delta
      have count : (o :: loans).count q = loans.count q := by
        simp [Ne.symm same]
      simpa only [demand, count, delta] using old
  have keys := (KeyEffects.iff_run_ambient _ _).mp
    (peerPut_keyEffect (allowed := NoPromotion) (some o.slot)) w ambient () v ambient' run
  exact ⟨inventory_view hi.inventory packets,
    queueOwners_view (queueOwners_paymentState hi.queues hd hp) peers, funded,
    keys.rxCompatible packets hi.keys.1,
    keys.currentsCompatible hi.keys.2 (fun _ _ impossible => impossible.elim)⟩

/-- A stable boundary survives payment of that same reservation. This
combines funding with the exact native queue/ring/packet frame of peerPut. -/
theorem reservation_payment_stable (hi : CarrierState cs (o :: loans) w)
    (stable : StableRx cs w) (ambient ambient' : Ambient)
    (run : ((peerPut (some o.slot)).run w).run ambient = .ok (((),v),ambient')) :
    CarrierState cs loans v ∧ StableRx cs v :=
  ⟨reservation_payment hi ambient ambient' run, stable.put ambient ambient' run⟩

end Leanux.Proofs.WG.Queues.RxCredits
