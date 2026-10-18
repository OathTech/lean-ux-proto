import Leanux.Proofs.WG.Queues.SyscallSourceCuts
import Leanux.Proofs.WG.Queues.AdmissionSourceCuts

/-! Carrier-free source cuts of the three ingress dispatch constructors.
These cuts expose the actual normal path before selecting an accepted receive.
A removed admission is covered equally with one still present at return. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DispatchSourceCuts
open Leanux Leanux.WG Leanux.Proofs.Logged
open AdmissionSelection AdmissionSourceCuts TrafficOccurrences

/-- Every flood input position has its actual receive Step. -/
theorem flood (count port family : Nat) (messages : List (List UInt8))
    (source : (ConservationSyscall.dispatch (.wgFlood count port family messages)).rule.relation
      cs w h result v k next) :
    ∃src u t j middle,
      runPrefix (FloodAccount.front family port) w h=(.ok (src,u),h) ∧
      ∃path : FloodLoop.Path family src (FloodAccount.messages count messages) cs u h middle t j,
        (∀index,index<(FloodAccount.messages count messages).length→
          ∃msg before after a b l m,∃step : FloodLoop.Step family src msg before after a b l m,
            FloodCut family src step path index) ∧
        ∀{index msg before after a b l m}
          {step : FloodLoop.Step family src msg before after a b l m},
          FloodCut family src step path index→∀c,
          FloodStepAdmission family src msg before after a b l m c→
          SyscallSelection.dispatch (.wgFlood count port family messages) index source c := by
  obtain ⟨src,u,t,j,middle,suffix,start,path,done,hist,ledger⟩ := source
  refine ⟨src,u,t,j,middle,start,path,fun index bound=>flood_total path bound,?_⟩
  intro index msg before after a b l m step cut c accepted
  exact ⟨src,u,t,j,middle,suffix,path,start,done,hist,ledger,flood_selected cut accepted⟩

/-- The actual done/yield batch path exposes every executed receive cursor. -/
theorem batch (items : List Env.BatchItem) (waitMs : Nat)
    (source : (ConservationSyscall.dispatch (.wgBatch items waitMs)).rule.relation
      cs w h result v k next) :
    ∃d cqes u t j middle,
      runPrefix BatchAccount.front w h=(.ok (d,u),h) ∧
      ∃path : BatchAccount.Path d items [] cs u h cqes middle t j,
        ∀{index qs item out before after a b l m}
          {step : BatchAccount.Step d qs item out before after a b l m},
          BatchCut d step path index→∀c,
          BatchStepAdmission d qs item out before after a b l m c→
          SyscallSelection.dispatch (.wgBatch items waitMs) index source c := by
  obtain ⟨d,cqes,u,t,j,middle,suffix,start,path,done,hist,ledger⟩ := source
  refine ⟨d,cqes,u,t,j,middle,start,path,?_⟩
  intro index qs item out before after a b l m step cut c accepted
  exact ⟨d,cqes,u,t,j,middle,suffix,path,start,done,hist,ledger,batch_selected cut accepted⟩

/-- Branch selection retains a certificate at the actual false arm. -/
theorem branch_no (condition : Bool) {yes no : RxHistory.Obs α}
    (a : ConservationSource.Rule yes) (b : ConservationSource.Rule no)
    (yesQuery : Query a) (noQuery : Query b) (disabled : condition=false)
    (source : (HolderTrafficDispatch.branch condition a b).relation cs w h result v k next)
    (chosen : ∀certificate : b.relation cs w h result v k next,noQuery certificate c) :
    AdmissionSelection.branch condition a b yesQuery noQuery source c := by
  cases condition
  · exact chosen source
  · contradiction

/-- Descriptor failure is distinguished from the actual body's source cut.
The normal fdput and errno return remain in the enclosing source certificate. -/
theorem socket (fd : Nat) {body : RxHistory.Obs Int} (rule : ConservationSource.Rule body)
    (source : (HolderTrafficDispatch.socket fd rule).relation cs w h result v k next) :
    ∃f entered,(liftFS (fdget fd)).run w=.ok (f,entered) ∧
      (f.file.isNone=true ∨
        f.file.isNone=false ∧ ∃ret returned received admitted,∃front : rule.relation cs entered h ret returned received admitted,
          ∀query : Query rule,∀c,query front c→AdmissionSelection.socket fd rule query source c) := by
  obtain ⟨f,entered,j,middle,get,rest⟩ := source
  obtain ⟨read,rfl,rfl⟩ := get
  refine ⟨f,entered,read,?_⟩
  cases missing : f.file.isNone with
  | true=>exact Or.inl rfl
  | false=>
    refine Or.inr ⟨rfl,?_⟩
    simp only [HolderTrafficDispatch.branch,missing,Bool.false_eq_true,↓reduceIte] at rest
    obtain ⟨ret,returned,received,admitted,front,tail⟩ := rest
    refine ⟨ret,returned,received,admitted,front,?_⟩
    intro query c chosen
    refine ⟨f,entered,j,middle,⟨read,rfl,rfl⟩,?_,?_⟩
    · simpa only [HolderTrafficDispatch.branch,missing,Bool.false_eq_true,↓reduceIte] using
        (show (ConservationSource.bind rule _).relation middle entered j result v k next from
          ⟨ret,returned,received,admitted,front,tail⟩)
    · apply branch_no _ _ _ _ _ missing
      intro certificate
      exact ⟨ret,returned,received,admitted,front,tail,chosen⟩

/-- The sole inject occurrence is exposed even when its deferred tail has
already removed it. A missing descriptor has no receive occurrence. -/
theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat)
    (source : (ConservationSyscall.dispatch (.wgInject family port msg tos ll dest)).rule.relation
      cs w h result v k next) :
    ∃f entered,(liftFS (fdget SENDER_FD)).run w=.ok (f,entered) ∧
      (f.file.isNone=true ∨
        f.file.isNone=false ∧ ∃src prepared a b admitted received,
          runPrefix (InjectAccount.front family port tos ll dest) entered h=(.ok (src,prepared),h) ∧
          runPrefix AdmissionSection.enter prepared h=(.ok ((),a),h) ∧
          AdmissionCaller.Step cs admitted msg src a b h received ∧
            ∀c,ReceiveEffects.Accepted cs admitted msg src a.wg b.wg a.ambient b.ambient c→
              SyscallSelection.dispatch (.wgInject family port msg tos ll dest) 0 source c) := by
  obtain ⟨f,entered,read,missing | ⟨present,ret,returned,received,next,front,lifted⟩⟩ :=
    socket SENDER_FD (ConservationSource.inject family port msg tos ll dest) source
  · exact ⟨f,entered,read,Or.inl missing⟩
  · obtain ⟨src,u,t,j,admitted,suffix,start,sectionStep,done,hist,ledger⟩ := front
    obtain ⟨a,b,enter,receive,leave⟩ := sectionStep
    refine ⟨f,entered,read,Or.inr ⟨present,src,u,a,b,admitted,j,start,enter,receive,?_⟩⟩
    intro c accepted
    apply lifted (AdmissionSelection.inject family port msg tos ll dest) c
    exact ⟨src,u,t,j,admitted,suffix,a,b,start,enter,receive,leave,done,hist,ledger,accepted⟩

end Leanux.Proofs.WG.Queues.RxCredits.DispatchSourceCuts
