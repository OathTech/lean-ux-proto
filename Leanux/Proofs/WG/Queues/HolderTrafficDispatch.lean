import Leanux.Proofs.WG.Queues.ConservationCertificates
import Leanux.Proofs.WG.Queues.HolderEntryDeferred
import Leanux.Proofs.WG.Queues.HolderEntryDispatch
import Leanux.Proofs.WG.Origins.OwnerSyscalls

/-! The original traffic dispatcher carries source certificates through its
actual descriptor and observation wrappers. Each certificate selects a ledger
without a funding field; its establishment theorem derives the next outer entry
from the input entry and this identical original execution. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderTrafficDispatch
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders ConservationSource

/-- Normal establishment is separate from the source relation. -/
def Established {action : RxHistory.Obs α} (rule : Rule action) (loans : Reservations) : Prop :=
  ∀ {cs w h result v k},HolderEntry.Inv cs loans h w→
    runPrefix action w h=(.ok (result,v),k)→
    ∃ next,rule.relation cs w h result v k next ∧ HolderEntry.Inv next loans k v

theorem pure_established (x : α) : Established (ConservationSource.pure x) loans := by
  intro cs w h result v k hi run
  simp only [runPrefix_pure,Prod.mk.injEq,Except.ok.injEq] at run
  obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
  exact ⟨cs,⟨rfl,rfl,rfl,rfl⟩,hi⟩

theorem bind_established {action : RxHistory.Obs α} {nextAction : α→RxHistory.Obs β}
    {first : Rule action} {next : ∀x,Rule (nextAction x)}
    (a : Established first loans) (b : ∀x,Established (next x) loans) :
    Established (ConservationSource.bind first next) loans := by
  intro cs w h result v k hi run
  obtain ⟨x,u,j,start,finish⟩ := DecryptIteration.bind_normal run
  obtain ⟨middle,front,entry⟩ := a hi start
  obtain ⟨final,tail,entry'⟩ := b x entry finish
  exact ⟨final,⟨x,u,j,middle,front,tail⟩,entry'⟩

/-- A raw lift has the exact source run, unchanged journal and ledger. Its
source relation alone asserts no state frame or funding preservation. -/
def lift (action : Leanux.M α) : Rule (liftPrefix action : RxHistory.Obs α) where
  relation := fun cs w h x v k next=>action.run w=.ok (x,v) ∧ k=h ∧ next=cs
  source := by
    rintro cs w h x v k next ⟨run,rfl,_⟩
    exact Prod.ext run rfl
  appends := by rintro cs w h x v k next ⟨_,rfl,_⟩; exact ⟨[],by simp⟩
  unique := by intro cs w h x v k left right a b; exact a.2.2.trans b.2.2.symm

theorem lift_established (action : Leanux.M α)
    (frame : SameView (fun w : World=>wgStoreView w.wg) action) :
    Established (lift action) loans := by
  intro cs w h result v k hi run
  change (action.run w,h)=(.ok (result,v),k) at run
  obtain ⟨actual,rfl⟩ := Prod.mk.inj run
  exact ⟨cs,⟨actual,rfl,rfl⟩,HolderEntryDispatch.wg_store hi
    ((ProjectedAction.iff_run _ _ _).mp frame w result v actual)⟩

/-- The relation selects the same actual Boolean branch as the source. -/
def branch (condition : Bool) {yes no : RxHistory.Obs α} (a : Rule yes) (b : Rule no) :
    Rule (if condition then yes else no) where
  relation := if condition then a.relation else b.relation
  source := by cases condition <;> first | exact a.source | exact b.source
  appends := by cases condition <;> first | exact a.appends | exact b.appends
  unique := by cases condition <;> first | exact a.unique | exact b.unique

theorem branch_established (condition : Bool) {yes no : RxHistory.Obs α} {a : Rule yes} {b : Rule no}
    (ha : Established a loans) (hb : Established b loans) : Established (branch condition a b) loans := by
  cases condition
  · exact hb
  · exact ha

/-- Missing descriptors return EBADF before the body. Every normal body
status, including errno, executes the original fdput. -/
def socket (fd : Nat) {body : RxHistory.Obs Int} (rule : Rule body) :
    Rule (RxHistory.socketCallOn fd body) :=
  ConservationSource.bind (lift (liftFS (fdget fd))) fun f=>
    branch f.file.isNone (ConservationSource.pure (-EBADF))
      (ConservationSource.bind rule fun ret=>
        ConservationSource.bind (lift (liftFS (fdput f))) fun _=>ConservationSource.pure ret)

theorem socket_established (fd : Nat) {body : RxHistory.Obs Int} {rule : Rule body}
    (entry : Established rule loans) : Established (socket fd rule) loans := by
  unfold socket
  apply bind_established
  · exact lift_established _ (fun initial=>productFS_spec _ _ (fun _ _ _ _ hi=>hi))
  · intro f
    apply branch_established
    · exact pure_established _
    · apply bind_established entry
      intro ret
      apply bind_established
      · exact lift_established _ (fun initial=>productFS_spec _ _ (fun _ _ _ _ hi=>hi))
      · intro _; exact pure_established _

theorem inject_established (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Established (ConservationSource.inject family port msg tos ll dest) loans := by
  intro cs w h result v k hi run
  obtain ⟨certificate,_⟩ := ConservationCertificates.inject_empty hi run
  obtain ⟨_,_,entry,_,_⟩ := HolderTrafficEntry.inject_normal hi run
  exact ⟨[],certificate,entry⟩

theorem flood_established (count port family : Nat) (messages : List (List UInt8)) :
    Established (ConservationSource.flood count port family messages) loans := by
  intro cs w h result v k hi run
  exact HolderTrafficEntry.flood_normal hi run

theorem batch_established (entries : List Env.BatchItem) :
    Established (ConservationSource.batch entries) loans := by
  intro cs w h result v k hi run
  exact HolderTrafficEntry.batch_normal entries hi run

/-- The idle stage admits no packets. Its selected ledger subtracts exactly
the removals in its actual fresh suffix, including the absent-device case. -/
def idle : Rule RxHistory.idleTimers where
  relation := fun cs w h x v k next=>runPrefix RxHistory.idleTimers w h=(.ok (x,v),k) ∧
    ∃ suffix,k=h++suffix ∧ next=remaining cs (NapiCarrier.removedPackets suffix)
  source := by intro cs w h x v k next hi; exact hi.1
  appends := by rintro cs w h x v k next ⟨_,suffix,hist,_⟩; exact ⟨suffix,hist⟩
  unique := by
    rintro cs w h x v k left right ⟨_,suffix,hist,rfl⟩ ⟨_,other,hist',rfl⟩
    have same := List.append_cancel_left (hist.symm.trans hist')
    rw [same]

theorem idle_established : Established idle loans := by
  intro cs w h result v k hi run
  obtain ⟨suffix,hist,entry⟩ := HolderEntryDeferred.idle_normal hi run
  exact ⟨_,⟨run,suffix,hist,rfl⟩,entry⟩

def observe : Rule RxHistory.observe :=
  ConservationSource.bind idle fun _=>lift Environment.observeTail

theorem observe_established : Established observe loans :=
  bind_established idle_established (fun _=>lift_established _
    (observeTail_sameKernel.of_factor (fun s : ProductStore43=>s.2.2.2) _ (fun _=>rfl)))

def injectDispatch (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Rule (RxHistory.syscallDispatch (.wgInject family port msg tos ll dest)) :=
  socket SENDER_FD (ConservationSource.inject family port msg tos ll dest)

theorem injectDispatch_established (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Established (injectDispatch family port msg tos ll dest) loans :=
  socket_established _ (inject_established family port msg tos ll dest)

def observeDispatch : Rule (RxHistory.syscallDispatch .wgObserve) :=
  ConservationSource.bind observe fun out=>
    ConservationSource.bind (lift (modifyAmbient fun w=>
      {w with extraOut:=["datagrams","replies","stats"].map fun k=>(k,out.2.getObjValD k)})) fun _=>
      socket LISTEN4_FD (ConservationSource.pure out.1)

theorem observeDispatch_established : Established observeDispatch loans := by
  apply bind_established observe_established
  intro out
  apply bind_established
  · exact lift_established _ (fun initial=>productAmbient_spec _ _ (fun _ _ hi=>hi))
  · intro _; exact socket_established _ (pure_established _)

theorem floodDispatch_established (count port family : Nat) (messages : List (List UInt8)) :
    Established (show Rule (RxHistory.syscallDispatch (.wgFlood count port family messages)) from
      ConservationSource.flood count port family messages) loans := flood_established count port family messages

theorem batchDispatch_established (entries : List Env.BatchItem) (waitMs : Nat) :
    Established (show Rule (RxHistory.syscallDispatch (.wgBatch entries waitMs)) from
      ConservationSource.batch entries) loans := batch_established entries

/-- Pair any established concrete dispatcher certificate with the existing
owner-safe journal. No state or final ledger is invented for a stopped run. -/
theorem dispatch_checked (call : Syscall) (rule : Rule (RxHistory.syscallDispatch call))
    (entry : Established rule loans) (hi : HolderEntry.Inv cs loans h w) :
    ∃ suffix,(runPrefix (RxHistory.syscallDispatch call) w h).2=h++suffix ∧
      OwnerChecks.Safe (runPrefix (RxHistory.syscallDispatch call) w h).2 ∧
      match (runPrefix (RxHistory.syscallDispatch call) w h).1 with
      | .error _=>True
      | .ok (result,v)=>∃next,rule.relation cs w h result v
          (runPrefix (RxHistory.syscallDispatch call) w h).2 next ∧
          HolderEntry.Inv next loans (runPrefix (RxHistory.syscallDispatch call) w h).2 v := by
  obtain ⟨suffix,hist,safe,_⟩ := OwnerSyscalls.dispatch call w h hi.2
  refine ⟨suffix,hist,safe,?_⟩
  cases run:(runPrefix (RxHistory.syscallDispatch call) w h).1 with
  | error reason=>trivial
  | ok out=>exact entry hi (Prod.ext run rfl)

end Leanux.Proofs.WG.Queues.RxCredits.HolderTrafficDispatch
