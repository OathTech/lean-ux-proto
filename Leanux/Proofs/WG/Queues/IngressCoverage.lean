import Leanux.Proofs.WG.Queues.DispatchSourceCuts

/-! Coverage predicates expose the actual source path independently of any
accepted carrier and of the postcondition to be proved for it. They retain
all receive positions, including admissions removed before dispatch returns. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.IngressCoverage
open Leanux Leanux.WG Leanux.Proofs.Logged
open AdmissionSourceCuts TrafficOccurrences

def Flood (count port family : Nat) (messages : List (List UInt8))
    (cs : Ledger) (w : World) (h : List RxHistory.Event) (post : Nat→Carrier→Prop) : Prop :=
  ∃src u t j middle,
    runPrefix (FloodAccount.front family port) w h=(.ok (src,u),h) ∧
    ∃path : FloodLoop.Path family src (FloodAccount.messages count messages) cs u h middle t j,
      (∀index,index<(FloodAccount.messages count messages).length→
        ∃msg before after a b l m,∃step : FloodLoop.Step family src msg before after a b l m,
          FloodCut family src step path index) ∧
      ∀{index msg before after a b l m}
        {step : FloodLoop.Step family src msg before after a b l m},
        FloodCut family src step path index→∀c,
        FloodStepAdmission family src msg before after a b l m c→post index c

def Batch (items : List Env.BatchItem) (cs : Ledger) (w : World)
    (h : List RxHistory.Event) (post : Nat→Carrier→Prop) : Prop :=
  ∃d cqes u t j middle,
    runPrefix BatchAccount.front w h=(.ok (d,u),h) ∧
    ∃path : BatchAccount.Path d items [] cs u h cqes middle t j,
      ∀{index qs item out before after a b l m}
        {step : BatchAccount.Step d qs item out before after a b l m},
        BatchCut d step path index→∀c,
        BatchStepAdmission d qs item out before after a b l m c→post index c

def Inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat)
    (cs : Ledger) (w : World) (h : List RxHistory.Event) (post : Nat→Carrier→Prop) : Prop :=
  ∃f entered,(liftFS (fdget SENDER_FD)).run w=.ok (f,entered) ∧
    (f.file.isNone=true ∨
      f.file.isNone=false ∧ ∃src prepared a b admitted received,
        runPrefix (InjectAccount.front family port tos ll dest) entered h=(.ok (src,prepared),h) ∧
        runPrefix AdmissionSection.enter prepared h=(.ok ((),a),h) ∧
        AdmissionCaller.Step cs admitted msg src a b h received ∧
        ∀c,ReceiveEffects.Accepted cs admitted msg src a.wg b.wg a.ambient b.ambient c→post 0 c)

/-- The three ingress dispatch constructors are specified separately. Each
case retains its original source prefix/path before quantifying over carriers. -/
def Complete (call : Syscall) (cs : Ledger) (w : World) (h : List RxHistory.Event)
    (post : Nat→Carrier→Prop) : Prop :=
  (∀count port family messages,call=.wgFlood count port family messages→
    Flood count port family messages cs w h post) ∧
  (∀items waitMs,call=.wgBatch items waitMs→Batch items cs w h post) ∧
  (∀family port msg tos ll dest,call=.wgInject family port msg tos ll dest→
    Inject family port msg tos ll dest cs w h post)

theorem flood_mono (coverage : Flood count port family messages cs w h post)
    (step : ∀index c,post index c→next index c) : Flood count port family messages cs w h next := by
  obtain ⟨src,u,t,j,middle,start,path,total,covered⟩ := coverage
  refine ⟨src,u,t,j,middle,start,path,total,?_⟩
  intro index msg before after a b l m source cut c accepted
  exact step index c (covered cut c accepted)

theorem batch_mono (coverage : Batch items cs w h post)
    (step : ∀index c,post index c→next index c) : Batch items cs w h next := by
  obtain ⟨d,cqes,u,t,j,middle,start,path,covered⟩ := coverage
  refine ⟨d,cqes,u,t,j,middle,start,path,?_⟩
  intro index qs item out before after a b l m source cut c accepted
  exact step index c (covered cut c accepted)

theorem inject_mono (coverage : Inject family port msg tos ll dest cs w h post)
    (step : ∀index c,post index c→next index c) : Inject family port msg tos ll dest cs w h next := by
  obtain ⟨f,entered,read,absent | ⟨present,src,prepared,a,b,admitted,received,start,enter,receive,covered⟩⟩ := coverage
  · exact ⟨f,entered,read,Or.inl absent⟩
  · exact ⟨f,entered,read,Or.inr ⟨present,src,prepared,a,b,admitted,received,start,enter,receive,
      fun c accepted=>step 0 c (covered c accepted)⟩⟩

theorem mono (coverage : Complete call cs w h post)
    (step : ∀index c,post index c→next index c) : Complete call cs w h next := by
  refine ⟨?_,?_,?_⟩
  · intro count port family messages same
    exact flood_mono (coverage.1 count port family messages same) step
  · intro items waitMs same
    exact batch_mono (coverage.2.1 items waitMs same) step
  · intro family port msg tos ll dest same
    exact inject_mono (coverage.2.2 family port msg tos ll dest same) step

/-- This concrete source certificate supplies every ingress position without
requiring an accepted packet, a selected query or final membership as input. -/
theorem dispatch (call : Syscall)
    (source : (ConservationSyscall.dispatch call).rule.relation cs w h result v k next) :
    Complete call cs w h (fun index c=>SyscallSelection.dispatch call index source c) := by
  refine ⟨?_,?_,?_⟩
  · intro count port family messages same
    subst call
    exact DispatchSourceCuts.flood count port family messages source
  · intro items waitMs same
    subst call
    exact DispatchSourceCuts.batch items waitMs source
  · intro family port msg tos ll dest same
    subst call
    exact DispatchSourceCuts.inject family port msg tos ll dest source

/-- The normal original syscall exposes a complete ingress path behind its
actual entry prefix; every covered occurrence selects the full syscall query. -/
theorem syscall (call : Syscall) (traffic : SyscallEntryCuts.TrafficCall call)
    (source : (ConservationSyscall.rule call).relation cs w h result v k next) :
    ∃entered,runPrefix (SyscallEntryCuts.enter call) w h=(.ok ((),entered),h) ∧
      Complete call cs entered h (fun index c=>SyscallSelection.syscall call index source c) := by
  obtain ⟨entered,ret,returned,received,admitted,start,front,lifted⟩ :=
    SyscallSourceCuts.syscall_cut call traffic source
  exact ⟨entered,start,mono (dispatch call front) lifted⟩

end Leanux.Proofs.WG.Queues.RxCredits.IngressCoverage
