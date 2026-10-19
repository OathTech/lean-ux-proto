import Leanux.Proofs.WG.TransmitSecurity.SocketJournalQuiet
import Leanux.Proofs.WG.TransmitSecurity.EncryptionHistoryFrames

/-! Exact native erasure transports the batch projection; quiet source paths
retain the entire previous socket receipt list, including stopped runs. -/
namespace Leanux.Proofs.WG.TransmitSecurity.SocketJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity

theorem product_checked {g : PrefixM Journal.Event α}
    (history : ∀ past, Driver.ProductHistorySafe (Quiet.Stable past) g)
    (native : ∀ w h result v, BatchCoherence.Native.Coherent [] active w.wg →
      (runPrefix g w h).1 = .ok (result,v) → BatchCoherence.Native.Coherent [] active v.wg) :
    PrefixPreserves (Inv active) Safe g := by
  intro w h before
  obtain ⟨suffix,extension,same,_⟩ := history (receipts h) w h rfl
  have safe := before.2.frame same
  refine ⟨suffix,extension,safe,?_⟩
  cases result : (runPrefix g w h).1 with
  | error stop => trivial
  | ok out => exact ⟨native w h out.1 out.2 before.1 result,safe⟩

theorem state_checked {g : WGPrefix Journal.Event α}
    (history : ∀ past, Driver.StateHistorySafe (Quiet.Stable past) g)
    (native : ∀ w a h result v b, BatchCoherence.Native.Coherent [] active w →
      (runWGPrefix g w a h).1 = .ok ((result,v),b) → BatchCoherence.Native.Coherent [] active v) :
    StatePrefixPreserves (fun h w _ => StateInv active h w) Safe g := by
  intro w a h before
  obtain ⟨suffix,extension,same,_⟩ := history (receipts h) w a h rfl
  have safe := before.2.frame same
  refine ⟨suffix,extension,safe,?_⟩
  cases result : (runPrefix (g.run w) a h).1 with
  | error stop => trivial
  | ok out => exact ⟨native w a h out.1.1 out.1.2 out.2 before.1 result,safe⟩

theorem product_quiet {g : PrefixM Journal.Event α} {action : Leanux.M α}
    (history : ∀ past, Driver.ProductHistorySafe (Quiet.Stable past) g)
    (erases : ErasesPrefix g action)
    (keeps : Preserves (fun w : World => BatchCoherence.Native.Coherent [] active w.wg) action) :
    PrefixPreserves (Inv active) Safe g :=
  product_checked history (fun w h result v before run =>
    (hoare_iff_run _ _ _).mp keeps w result v before ((erases w h).symm.trans run))

theorem softirq : PrefixPreserves (Inv active) Safe (Driver.softirqObserved Journal.hooks) := by
  apply product_quiet (fun _ => Quiet.softirq_history)
  · have projected := Driver.softirq_projects Journal.hooks_projects
    rw [Driver.nonce_softirqObserved_eq] at projected
    exact EncryptionHistory.projected_erases projected Nonce.softirqObserved_erases
  · exact BatchCoherence.Napi.softirq [] active

theorem poll : PrefixEnsures (Inv active) Safe Journal.poll
    (fun item => Inv (item.toList ++ active)) := by
  intro w h before
  have history := (Quiet.hooks_safe (past := receipts h)).poll
  obtain ⟨suffix,extension,same,_⟩ := history w h rfl
  have safe := before.2.frame same
  refine ⟨suffix,extension,safe,?_⟩
  cases result : (runPrefix Journal.poll w h).1 with
  | error stop => trivial
  | ok output =>
    obtain ⟨item,v⟩ := output
    refine ⟨?_,safe⟩
    have native := DriverOwnership.product_native Journal.hooks_projects.poll
      (erasesPrefix_lift (liftWG TxRing.pollSource)) w v h result
    rw [liftWG_run] at native
    cases performed : (TxRing.pollSource.run w.wg).run w.ambient with
    | error stop => simp [performed,Except.map] at native
    | ok output =>
      obtain ⟨⟨out,g⟩,a⟩ := output
      simp only [performed,Except.map,Except.ok.injEq,Prod.mk.injEq] at native
      obtain ⟨rfl,rfl⟩ := native
      exact BatchCoherence.Encrypt.poll before.1 w.ambient a performed

end Leanux.Proofs.WG.TransmitSecurity.SocketJournal
