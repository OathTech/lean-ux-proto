import Leanux.Proofs.WG.Queues.BatchAccount
import Leanux.Proofs.WG.Queues.FloodAccount
import Leanux.Proofs.WG.Queues.InjectAccount

/-! Source relations for dynamic receive ledgers over the unchanged observer.
These are proof data, not another observer or operational interpreter. Every
normal certificate fixes the actual action, World, old history and returned
history. The unique ledger is selected by the source, independently of funding.
Normal establishment and accounting inside a stopped admission are separate
obligations; source uniqueness alone proves neither. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.ConservationSource
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

abbrev Relation (α : Type) := Ledger → World → List RxHistory.Event →
  α → World → List RxHistory.Event → Ledger → Prop

/-- A source relation has no funding field. Its uniqueness is relative to the
same incoming ledger and the same original execution, including both histories. -/
structure Rule (action : RxHistory.Obs α) where
  relation : Relation α
  source : ∀ {cs w h x v k next}, relation cs w h x v k next →
    runPrefix action w h=(.ok (x,v),k)
  appends : ∀ {cs w h x v k next}, relation cs w h x v k next → ∃ suffix,k=h++suffix
  unique : ∀ {cs w h x v k left right}, relation cs w h x v k left →
    relation cs w h x v k right → left=right

/-- Identity has an actual pure return and does not reset the ledger or history. -/
def pure (x : α) : Rule (pure x : RxHistory.Obs α) where
  relation := fun cs w h y v k next => y=x ∧ v=w ∧ k=h ∧ next=cs
  source := by rintro cs w h y v k next ⟨rfl,rfl,rfl,rfl⟩; rfl
  appends := by rintro cs w h y v k next ⟨_,_,rfl,_⟩; exact ⟨[],by simp⟩
  unique := by intro cs w h y v k left right a b; exact a.2.2.2.trans b.2.2.2.symm

/-- The intermediate state, journal and ledger are all the returned cut of
one actual first action. Equal-valued events at other positions are irrelevant. -/
def bind {action : RxHistory.Obs α} {nextAction : α → RxHistory.Obs β}
    (first : Rule action) (next : ∀ x,Rule (nextAction x)) : Rule (action >>= nextAction) where
  relation := fun cs w h y v k final =>
    ∃ x u j middle,first.relation cs w h x u j middle ∧ (next x).relation middle u j y v k final
  source := by
    rintro cs w h y v k final ⟨x,u,j,middle,a,b⟩
    simp only [runPrefix_bind,first.source a,(next x).source b]
  appends := by
    rintro cs w h y v k final ⟨x,u,j,middle,a,b⟩
    obtain ⟨front,hfront⟩ := first.appends a
    obtain ⟨tail,htail⟩ := (next x).appends b
    exact ⟨front++tail,by rw [htail,hfront,List.append_assoc]⟩
  unique := by
    rintro cs w h y v k left right ⟨x,u,j,middle,a,b⟩ ⟨x',u',j',middle',a',b'⟩
    have same := (first.source a).symm.trans (first.source a')
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := same
    have ledger := first.unique a a'
    subst middle'
    exact (next x).unique b b'

/-- A successful prefix followed by a Stop retains the exact stopped journal
and the last completed ledger cut. This does not invent a failed World or assert
that the tail performed no admission before stopping. -/
theorem stopped_tail {action : RxHistory.Obs α} {nextAction : α → RxHistory.Obs β}
    (first : Rule action) (certificate : first.relation cs w h x u j middle)
    (reason : Stop) (stopped : runPrefix (nextAction x) u j=(.error reason,k)) :
    runPrefix (action >>= nextAction) w h=(.error reason,k) := by
  simp only [runPrefix_bind,first.source certificate,stopped]

/-- The relation retains the source-selected receive ledger and its native
receipt inside the original caller's exact source relation. -/
def receive (msg : List UInt8) (src : SkbSource) : Rule (AdmissionCaller.receive msg src) where
  relation := fun cs w h x v k next => x=() ∧ AdmissionCaller.Step cs next msg src w v h k
  source := by rintro cs w h x v k next ⟨rfl,step⟩; exact step.1
  appends := by rintro cs w h x v k next ⟨_,step⟩; exact AdmissionCaller.step_appends step
  unique := by intro cs w h x v k left right a b; exact AdmissionCaller.step_unique a.2 b.2

/-- Polling subtracts the removals at this precise fresh suffix, rather than
all equal events or all old removals in the incoming history. -/
def poll (pid : PeerId) (budget : Nat) : Rule (RxHistory.observePoll pid budget) where
  relation := fun cs w h x v k next =>
    runPrefix (RxHistory.observePoll pid budget) w h=(.ok (x,v),k) ∧
      ∃ suffix,k=h++suffix ∧ next=remaining cs (NapiCarrier.removedPackets suffix)
  source := by intro cs w h x v k next hi; exact hi.1
  appends := by rintro cs w h x v k next ⟨_,suffix,hist,_⟩; exact ⟨suffix,hist⟩
  unique := by
    rintro cs w h x v k left right ⟨_,suffix,hist,rfl⟩ ⟨_,other,hist',rfl⟩
    have same := List.append_cancel_left (hist.symm.trans hist')
    rw [same]

/-- Flood's existing finite path records each actual receive occurrence; its
final ledger already includes the final afterBatch removal suffix. -/
def flood (count port family : Nat) (messages : List (List UInt8)) :
    Rule (RxHistory.flood count port family messages) where
  relation := fun cs w h x v k next => FloodAccount.Outcome cs next count port family messages w v h k x
  source := FloodAccount.Outcome.source
  appends := by
    intro cs w h x v k next hi
    obtain ⟨src,u,t,j,middle,suffix,start,path,done,hist,_⟩ := hi
    obtain ⟨front,old⟩ := path.appends
    exact ⟨front++suffix,by rw [hist,old,List.append_assoc]⟩
  unique := FloodAccount.Outcome.unique

/-- Inject's old Outcome names the ledger after admission. This relation
additionally selects its final ledger from the actual crypt/drain suffix. -/
def InjectFinal (cs : Ledger) (family port : Nat) (msg : List UInt8) (tos : Nat)
    (ll : Bool) (dest : Nat) (w : World) (h : List RxHistory.Event)
    (result : Int) (v : World) (k : List RxHistory.Event) (next : Ledger) : Prop :=
  ∃ src u t j admitted suffix,
    runPrefix (InjectAccount.front family port tos ll dest) w h=(.ok (src,u),h) ∧
    AdmissionSection.Step cs admitted msg src u t h j ∧
    runPrefix (InjectAccount.finish msg) t j=(.ok (result,v),k) ∧
    k=j++suffix ∧ next=remaining admitted (NapiCarrier.removedPackets suffix)

def inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Rule (RxHistory.inject family port msg tos ll dest) where
  relation := fun cs w h x v k next => InjectFinal cs family port msg tos ll dest w h x v k next
  source := by
    rintro cs w h x v k next ⟨src,u,t,j,admitted,suffix,start,step,done,_,_⟩
    exact InjectAccount.Outcome.source ⟨src,u,t,j,start,step,done⟩
  appends := by
    rintro cs w h x v k next ⟨src,u,t,j,admitted,suffix,start,step,done,hist,_⟩
    obtain ⟨front,old⟩ := step.appends
    exact ⟨front++suffix,by rw [hist,old,List.append_assoc]⟩
  unique := by
    rintro cs w h x v k left right
      ⟨src,u,t,j,admitted,suffix,start,step,done,hist,rfl⟩
      ⟨src',u',t',j',admitted',suffix',start',step',done',hist',rfl⟩
    rw [start] at start'
    obtain ⟨⟨rfl,rfl⟩,_⟩ := start'
    have same := step.source.symm.trans step'.source
    obtain ⟨⟨_,rfl⟩,rfl⟩ := same
    have ledger := step.unique step'
    have tail := List.append_cancel_left (hist.symm.trans hist')
    rw [ledger,tail]

/-- Finite source composition retains each ordered invocation, including
repeated equal inputs. The executable loop is the existing List.forM. -/
def forM (items : List γ) (action : γ → RxHistory.Obs Unit)
    (rules : ∀ item,Rule (action item)) : Rule (items.forM action) :=
  match items with
  | [] => pure ()
  | item::tail => bind (rules item) (fun _ => forM tail action rules)

/-- Actual bounded loops may stop early with `done`; the source relation
retains the same returned accumulator and only the calls actually executed. -/
def forIn (items : List γ) (initial : β)
    (action : γ → β → RxHistory.Obs (ForInStep β))
    (rules : ∀ item acc,Rule (action item acc)) : Rule (ForIn.forIn items initial action) :=
  match items with
  | [] => pure initial
  | item::tail => by
      rw [List.forIn_cons]
      apply bind (rules item initial)
      intro step
      cases step with
      | done result => exact pure result
      | yield result => exact forIn tail result action rules

/-- Batch preserves its original ordered saved-device/CQE path. Its relation
already includes each actual receive admission and interleaved removal suffix. -/
def batch (entries : List Env.BatchItem) : Rule (RxHistory.batch entries) where
  relation := fun cs w h x v k next => BatchAccount.Outcome cs next entries w v h k x
  source := BatchAccount.Outcome.source
  appends := by
    intro cs w h x v k next hi
    obtain ⟨suffix,hist⟩ := RxHistory.batch_appends entries w h
    exact ⟨suffix,by simpa only [BatchAccount.Outcome.source hi] using hist⟩
  unique := BatchAccount.Outcome.unique

/-- This relation describes a removal-only stage; by itself it asserts no
account preservation. Concrete stages below obtain that separately from their
already checked actual-source contracts. -/
private def removals (action : RxHistory.Obs α) : Rule action where
  relation := fun cs w h x v k next => runPrefix action w h=(.ok (x,v),k) ∧
    ∃ suffix,k=h++suffix ∧ next=remaining cs (NapiCarrier.removedPackets suffix)
  source := by intro cs w h x v k next hi; exact hi.1
  appends := by rintro cs w h x v k next ⟨_,suffix,hist,_⟩; exact ⟨suffix,hist⟩
  unique := by
    rintro cs w h x v k left right ⟨_,suffix,hist,rfl⟩ ⟨_,other,hist',rfl⟩
    have same := List.append_cancel_left (hist.symm.trans hist')
    rw [same]

def crypt : Rule RxHistory.runCryptWorkers := removals _
def afterBatch : Rule RxHistory.afterBatch := removals _

end Leanux.Proofs.WG.Queues.RxCredits.ConservationSource
