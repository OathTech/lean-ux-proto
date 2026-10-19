import Leanux.Proofs.WG.RetirementSecurity.OccurrenceInitialized
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceWorkers

/-! Exact shared-driver encryption cuts. The polled alias remains explicit
through native softirq before the actual encryption hook starts. Histories and
intermediate worlds belong to that one invocation, including a stopped tail. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceDriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open OccurrenceStack TransmitSecurity
variable {E : Type} {ρ : E → Option Nonce.Allocation} {hooks : Driver.Hooks E}

theorem poll (projects : Driver.HooksProjects ρ hooks Driver.nonceHooks)
    (before : Ready locals active w.wg) (h : List E)
    (run : (runPrefix hooks.poll w h).1 = .ok (item,v)) :
    Ready locals (item.toList ++ active) v.wg := by
  have native := DriverOwnership.product_native projects.poll
    (erasesPrefix_lift (liftWG TxRing.pollSource)) w v h run
  rw [liftWG_run] at native
  cases performed : (TxRing.pollSource.run w.wg).run w.ambient with
  | error stop => simp [performed,Except.map] at native
  | ok output =>
    obtain ⟨⟨out,g⟩,a⟩ := output
    simp only [performed,Except.map,Except.ok.injEq,Prod.mk.injEq] at native
    obtain ⟨rfl,rfl⟩ := native
    exact OccurrenceEncrypt.poll before w.ambient a performed

theorem softirq (projects : Driver.HooksProjects ρ hooks Driver.nonceHooks)
    (before : Ready locals active w.wg) (h : List E)
    (run : (runPrefix (Driver.softirqObserved hooks) w h).1 = .ok ((),v)) :
    Ready locals active v.wg := by
  have projected := Driver.softirq_projects projects
  rw [Driver.nonce_softirqObserved_eq] at projected
  exact (hoare_iff_run _ _ _).mp (OccurrenceNapi.softirq locals active) w () v before
    (DriverOwnership.product_native projected Nonce.softirqObserved_erases w v h run)

def Selected (active : List (List SkbId)) (items : List SkbId) (w : WGWorld) : Prop :=
  items.Nodup ∧ TxQueuedBatch w items ∧
  (∀ id ∈ items, ∃ packet, TxDisposition.txPackets w id = some packet) ∧
  (∃ first, items.head? = some first ∧ TxDisposition.HeadState first .uncrypted w) ∧
  (∀ id ∈ items, id ∉ (txCryptItems w ++ active).flatten)

theorem selected (before : Ready locals (items :: active) w) : Selected active items w :=
  ⟨before.2.2.selected_unique,before.2.2.selected_owned,
    before.2.2.selected_resident before.2.1,before.2.2.selected_uncrypted,
    before.2.2.selected_disjoint⟩

/-- The two actual preceding source calls derive selection safety at the
exact encryption entry, and the entire remaining run is the actual tail on
that intermediate world and history. The tail may return or Stop. -/
theorem entry (projects : Driver.HooksProjects ρ hooks Driver.nonceHooks)
    (before : Ready locals active w.wg)
    (polled : runPrefix hooks.poll w h = (.ok (some items,u),j))
    (callback : runPrefix (Driver.softirqObserved hooks) u j = (.ok ((),v),k)) :
    Ready locals (items :: active) v.wg ∧ Selected active items v.wg ∧
    runPrefix (Driver.encryptIterObserved hooks) w h =
      runPrefix (Driver.encryptTailObserved hooks (some items)) v k := by
  have atPoll := poll projects before h (congrArg Prod.fst polled)
  have atEntry := softirq projects atPoll j (congrArg Prod.fst callback)
  refine ⟨atEntry,selected atEntry,?_⟩
  simp only [Driver.encryptIterObserved,runPrefix_bind,polled,callback]

private theorem bind_normal {g : PrefixM E α} {f : α → PrefixM E β}
    (run : runPrefix (g >>= f) w h = (.ok (result,v),k)) :
    ∃ value u j, runPrefix g w h = (.ok (value,u),j) ∧
      runPrefix (f value) u j = (.ok (result,v),k) := by
  rw [runPrefix_bind] at run
  cases front : runPrefix g w h with
  | mk outcome j =>
    cases outcome with
    | error stop => simp only [front,Prod.mk.injEq,reduceCtorEq,false_and] at run
    | ok pair =>
      obtain ⟨value,u⟩ := pair
      exact ⟨value,u,j,rfl,by simpa only [front] using run⟩

/-- Every normal shared encryption iteration has these exact native poll,
softirq and tail cuts. A nonempty selection is resident, owned, unique,
uncrypted at its head and disjoint from other pending encryption aliases. -/
theorem normal (projects : Driver.HooksProjects ρ hooks Driver.nonceHooks)
    (before : Ready locals active w.wg)
    (run : runPrefix (Driver.encryptIterObserved hooks) w h = (.ok (result,v),k)) :
    ∃ item u j t l,
      runPrefix hooks.poll w h = (.ok (item,u),j) ∧
      runPrefix (Driver.softirqObserved hooks) u j = (.ok ((),t),l) ∧
      runPrefix (Driver.encryptTailObserved hooks item) t l = (.ok (result,v),k) ∧
      Ready locals (item.toList ++ active) t.wg ∧
      (∀ items, item = some items → Selected active items t.wg) := by
  unfold Driver.encryptIterObserved at run
  obtain ⟨item,u,j,polled,rest⟩ := bind_normal run
  obtain ⟨ignored,t,l,callback,tail⟩ := bind_normal rest
  cases ignored
  have ready := softirq projects (poll projects before h (congrArg Prod.fst polled))
    j (congrArg Prod.fst callback)
  refine ⟨item,u,j,t,l,polled,callback,tail,ready,?_⟩
  intro items same
  subst item
  exact selected ready

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceDriverCuts
