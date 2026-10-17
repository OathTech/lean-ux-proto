import Leanux.Proofs.WG.Queues.TrafficOccurrences
import Leanux.Proofs.WG.Queues.HolderTrafficDispatch
import Leanux.Proofs.WG.Queues.ConservationOuter

/-! Queries select subcertificates of the existing source rules. Bind direction
is part of the query construction; identical inputs or events at another source
position do not identify this selection. No execution is defined here. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.AdmissionSelection
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open ConservationSource TrafficOccurrences

abbrev Query {action : RxHistory.Obs α} (rule : Rule action) :=
  ∀ {cs w h x v k next}, rule.relation cs w h x v k next → Carrier → Prop

def Fates {action : RxHistory.Obs α} {rule : Rule action} (query : Query rule) : Prop :=
  ∀ {cs w h x v k next} (certificate : rule.relation cs w h x v k next) {c},
    query certificate c → Fate c next h k

def never {action : RxHistory.Obs α} (rule : Rule action) : Query rule :=
  fun _ _ => False

theorem never_fates {action : RxHistory.Obs α} (rule : Rule action) : Fates (never rule) := by
  intro cs w h x v k next certificate c selected
  contradiction

def inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Query (ConservationSource.inject family port msg tos ll dest) :=
  fun {cs w h result v k next} _ c => InjectAdmission cs next family port msg tos ll dest w v h k result c

theorem inject_fates (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Fates (inject family port msg tos ll dest) := by
  intro cs w h x v k next certificate c selected
  exact inject_fate selected

def flood (count port family : Nat) (messages : List (List UInt8)) (index : Nat) :
    Query (ConservationSource.flood count port family messages) :=
  fun {cs w h result v k next} _ c => FloodAdmission cs next count port family messages w v h k result index c

theorem flood_fates (count port family : Nat) (messages : List (List UInt8)) (index : Nat) :
    Fates (flood count port family messages index) := by
  intro cs w h x v k next certificate c selected
  exact flood_fate selected

def batch (items : List Env.BatchItem) (index : Nat) : Query (ConservationSource.batch items) :=
  fun {cs w h result v k next} _ c => BatchAdmission cs next items w v h k result index c

theorem batch_fates (items : List Env.BatchItem) (index : Nat) : Fates (batch items index) := by
  intro cs w h x v k next certificate c selected
  exact batch_fate selected

/-- Selection is inside the first actual action, before this exact continuation. -/
def left {action : RxHistory.Obs α} {nextAction : α → RxHistory.Obs β}
    (first : Rule action) (next : ∀ x, Rule (nextAction x)) (query : Query first) :
    Query (ConservationSource.bind first next) :=
  fun {cs w h y v k final} _ c =>
    ∃ x u j middle, ∃ front : first.relation cs w h x u j middle,
      (next x).relation middle u j y v k final ∧ query front c

/-- Selection is inside the returned-value-specific continuation, after the
actual first action's complete state, ledger and journal cut. -/
def right {action : RxHistory.Obs α} {nextAction : α → RxHistory.Obs β}
    (first : Rule action) (next : ∀ x, Rule (nextAction x)) (query : ∀ x, Query (next x)) :
    Query (ConservationSource.bind first next) :=
  fun {cs w h y v k final} _ c =>
    ∃ x u j middle, first.relation cs w h x u j middle ∧
      ∃ tail : (next x).relation middle u j y v k final, query x tail c

theorem left_fates {action : RxHistory.Obs α} {nextAction : α → RxHistory.Obs β}
    (first : Rule action) (next : ∀ x, Rule (nextAction x)) (query : Query first)
    (selected : Fates query)
    (conserved : ∀ x {cs w h y v k final}, (next x).relation cs w h y v k final →
      TrafficEffects.Conserved cs final h k) : Fates (left first next query) := by
  rintro cs w h y v k final certificate c ⟨x,u,j,middle,front,tail,chosen⟩
  exact fate_continue (selected front chosen) (conserved x tail)

theorem right_fates {action : RxHistory.Obs α} {nextAction : α → RxHistory.Obs β}
    (first : Rule action) (next : ∀ x, Rule (nextAction x)) (query : ∀ x, Query (next x))
    (selected : ∀ x, Fates (query x)) : Fates (right first next query) := by
  rintro cs w h y v k final certificate c ⟨x,u,j,middle,front,tail,chosen⟩
  obtain ⟨lead,hist⟩ := first.appends front
  exact fate_prefix (selected x tail chosen) hist

def branch (condition : Bool) {yes no : RxHistory.Obs α}
    (a : Rule yes) (b : Rule no) (yesQuery : Query a) (noQuery : Query b) :
    Query (HolderTrafficDispatch.branch condition a b) := by
  cases condition
  · exact noQuery
  · exact yesQuery

theorem branch_fates (condition : Bool) {yes no : RxHistory.Obs α}
    (a : Rule yes) (b : Rule no) (yesQuery : Query a) (noQuery : Query b)
    (hy : Fates yesQuery) (hn : Fates noQuery) :
    Fates (branch condition a b yesQuery noQuery) := by
  cases condition
  · exact hn
  · exact hy

/-- The body selection exists only in the original descriptor-present arm.
The exact fdget result, body return and fdput all remain in the parent Rule. -/
def socket (fd : Nat) {body : RxHistory.Obs Int} (rule : Rule body) (query : Query rule) :
    Query (HolderTrafficDispatch.socket fd rule) :=
  right (HolderTrafficDispatch.lift (liftFS (fdget fd)))
    (fun f => HolderTrafficDispatch.branch f.file.isNone (ConservationSource.pure (-EBADF))
      (ConservationSource.bind rule fun ret =>
        ConservationSource.bind (HolderTrafficDispatch.lift (liftFS (fdput f))) fun _ => ConservationSource.pure ret))
    (fun f => branch f.file.isNone _ _ (never _)
      (left rule (fun ret =>
        ConservationSource.bind (HolderTrafficDispatch.lift (liftFS (fdput f))) fun _ => ConservationSource.pure ret) query))

theorem socket_fates (fd : Nat) {body : RxHistory.Obs Int} (rule : Rule body) (query : Query rule)
    (selected : Fates query) : Fates (socket fd rule query) := by
  apply right_fates
  intro f
  apply branch_fates
  · exact never_fates _
  · apply left_fates _ _ _ selected
    rintro ret cs w h y v k final ⟨x,u,j,middle,front,tail⟩
    have first : j=h ∧ middle=cs := front.2
    have second : k=j ∧ final=middle := tail.2.2
    obtain ⟨rfl,rfl⟩ := first
    obtain ⟨rfl,rfl⟩ := second
    exact TrafficEffects.refl

def injectDispatch (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Query (HolderTrafficDispatch.injectDispatch family port msg tos ll dest) :=
  socket SENDER_FD _ (inject family port msg tos ll dest)

theorem injectDispatch_fates (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Fates (injectDispatch family port msg tos ll dest) :=
  socket_fates _ _ _ (inject_fates family port msg tos ll dest)

abbrev OuterQuery {action : PrefixOuter RxHistory.Event α} (rule : ConservationOuter.Rule action) :=
  ∀ {cs h x k next}, rule.relation cs h x k next → Carrier → Prop

def OuterFates {action : PrefixOuter RxHistory.Event α} {rule : ConservationOuter.Rule action}
    (query : OuterQuery rule) : Prop :=
  ∀ {cs h x k next} (certificate : rule.relation cs h x k next) {c},
    query certificate c → Fate c next h k

/-- The runner's actual operation index and supplied World are retained by
runAtPrefix. This is exactly the inner certificate, with its returned World. -/
def runAt (index : Nat) (w : World) {action : RxHistory.Obs α}
    (rule : Rule action) (query : Query rule) : OuterQuery (ConservationOuter.runAt index w rule) :=
  fun certificate c => query certificate c

theorem runAt_fates (index : Nat) (w : World) {action : RxHistory.Obs α}
    (rule : Rule action) (query : Query rule) (selected : Fates query) :
    OuterFates (runAt index w rule query) := by
  intro cs h out k next certificate c chosen
  exact selected certificate chosen

def outerLeft {action : PrefixOuter RxHistory.Event α} {nextAction : α → PrefixOuter RxHistory.Event β}
    (first : ConservationOuter.Rule action) (next : ∀ x, ConservationOuter.Rule (nextAction x))
    (query : OuterQuery first) : OuterQuery (ConservationOuter.bind first next) :=
  fun {cs h y k final} _ c => ∃ x j middle, ∃ front : first.relation cs h x j middle,
    (next x).relation middle j y k final ∧ query front c

def outerRight {action : PrefixOuter RxHistory.Event α} {nextAction : α → PrefixOuter RxHistory.Event β}
    (first : ConservationOuter.Rule action) (next : ∀ x, ConservationOuter.Rule (nextAction x))
    (query : ∀ x, OuterQuery (next x)) : OuterQuery (ConservationOuter.bind first next) :=
  fun {cs h y k final} _ c => ∃ x j middle, first.relation cs h x j middle ∧
    ∃ tail : (next x).relation middle j y k final, query x tail c

theorem outerLeft_fates {action : PrefixOuter RxHistory.Event α} {nextAction : α → PrefixOuter RxHistory.Event β}
    (first : ConservationOuter.Rule action) (next : ∀ x, ConservationOuter.Rule (nextAction x))
    (query : OuterQuery first) (selected : OuterFates query)
    (conserved : ∀ x {cs h y k final}, (next x).relation cs h y k final →
      TrafficEffects.Conserved cs final h k) : OuterFates (outerLeft first next query) := by
  rintro cs h y k final certificate c ⟨x,j,middle,front,tail,chosen⟩
  exact fate_continue (selected front chosen) (conserved x tail)

theorem outerRight_fates {action : PrefixOuter RxHistory.Event α} {nextAction : α → PrefixOuter RxHistory.Event β}
    (first : ConservationOuter.Rule action) (next : ∀ x, ConservationOuter.Rule (nextAction x))
    (query : ∀ x, OuterQuery (next x)) (selected : ∀ x, OuterFates (query x)) :
    OuterFates (outerRight first next query) := by
  rintro cs h y k final certificate c ⟨x,j,middle,front,tail,chosen⟩
  obtain ⟨lead,hist⟩ := first.appends front
  exact fate_prefix (selected x tail chosen) hist

end Leanux.Proofs.WG.Queues.RxCredits.AdmissionSelection
