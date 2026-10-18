import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeAdmissionFacts

/-! Successful native consumers must already have emitted their pre-write
acceptance receipt. This closes the return-value link used by receive suffixes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues.RxCredits.HandshakeLoans
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private theorem any (action : WG.M α) : Preserves (fun _ => True) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  trivial

private theorem chain {Q : α → WGWorld → Prop} (action : WG.M β) (next : β → WG.M α)
    (ht : ∀ x, Hoare (next x) (fun _ => True) Q) :
    Hoare (action >>= next) (fun _ => True) Q :=
  hoare_bind action next (any action) ht

private theorem pure_result (x : α) : Hoare (pure x : WG.M α) (fun _ => True) (fun y _ => y = x) :=
  hoare_consequence (hoare_pure x _) (fun _ h => h) (fun _ _ h => h.1)

private theorem out_result (peer result : Option PeerId) :
    Hoare (initiationOut peer result) (fun _ => True) (fun value _ => value = result) := by
  unfold initiationOut
  repeat' first
    | with_reducible exact pure_result _
    | with_reducible apply chain
    | split
    | (session_origin_intro_forall; try dsimp only)

theorem initiation_finish_result (msg : Key) (accepted : AcceptedInitiation) :
    Hoare (initiationAcceptedFinish msg accepted) (fun _ => True)
      (fun result _ => result = some accepted.peer) := by
  unfold initiationAcceptedFinish
  repeat' first
    | with_reducible exact out_result _ _
    | with_reducible apply chain
    | split
    | (session_origin_intro_forall; try dsimp only)

theorem response_finish_result (msg : Key) (accepted : AcceptedResponse) :
    Hoare (responseAcceptedFinish msg accepted) (fun _ => True)
      (fun result _ => result = some accepted.peer) := by
  unfold responseAcceptedFinish
  apply chain
  intro p
  apply chain
  intro doneUnit
  exact pure_result _

theorem initiation_success_receipt (msg : Key) (w v : WGWorld) (a b : Ambient)
    (h journal : List InitiationAcceptance) (pid : PeerId)
    (run : runWGPrefix (acceptedInitiation msg) w a h = (.ok ((some pid,v),b),journal)) :
    ∃ accepted u c,
      journal = h ++ [⟨msg,⟨some accepted,w,u,a,c⟩⟩] ∧ accepted.peer = pid ∧
      ((initiationAcceptedCheck msg).run w).run a = .ok ((some accepted,u),c) ∧
      ((initiationAcceptedFinish msg accepted).run u).run c = .ok ((some pid,v),b) := by
  rw [acceptedInitiation_run] at run
  cases check : ((initiationAcceptedCheck msg).run w).run a with
  | error err => simp only [check] at run; cases run
  | ok out =>
    rcases out with ⟨⟨admission,u⟩,c⟩
    rw [check] at run
    cases admission with
    | none => cases run
    | some accepted =>
      simp only [Option.isSome_some,↓reduceIte,initiationAcceptedContinue,Prod.mk.injEq] at run
      have returned := (hoare_iff_run_ambient _ _ _).mp (initiation_finish_result msg accepted)
        u c (some pid) v b True.intro run.1
      exact ⟨accepted,u,c,run.2.symm,Option.some.inj returned.symm,rfl,run.1⟩

theorem response_success_receipt (msg : Key) (w v : WGWorld) (a b : Ambient)
    (h journal : List ResponseAcceptance) (pid : PeerId)
    (run : runWGPrefix (acceptedResponse msg) w a h = (.ok ((some pid,v),b),journal)) :
    ∃ accepted u c,
      journal = h ++ [⟨msg,⟨some accepted,w,u,a,c⟩⟩] ∧ accepted.peer = pid ∧
      ((responseAcceptedCheck msg).run w).run a = .ok ((some accepted,u),c) ∧
      ((responseAcceptedFinish msg accepted).run u).run c = .ok ((some pid,v),b) := by
  rw [acceptedResponse_run] at run
  cases check : ((responseAcceptedCheck msg).run w).run a with
  | error err => simp only [check] at run; cases run
  | ok out =>
    rcases out with ⟨⟨admission,u⟩,c⟩
    rw [check] at run
    cases admission with
    | none => cases run
    | some accepted =>
      simp only [Option.isSome_some,↓reduceIte,responseAcceptedContinue,Prod.mk.injEq] at run
      have returned := (hoare_iff_run_ambient _ _ _).mp (response_finish_result msg accepted)
        u c (some pid) v b True.intro run.1
      exact ⟨accepted,u,c,run.2.symm,Option.some.inj returned.symm,rfl,run.1⟩

def HandshakeAdmission.ForPeer (r : HandshakeAdmission) (pid : PeerId) : Prop :=
  match r with
  | .initiation _ checked => ∃ accepted, checked.value = some accepted ∧ accepted.peer = pid
  | .response _ checked => ∃ accepted, checked.value = some accepted ∧ accepted.peer = pid

def HasAdmission (h : List HandshakeAdmission) (pid : PeerId) : Prop :=
  ∃ r ∈ h, r.ForPeer pid

theorem admitInitiation_run (mac : HandshakeMac)
    (w : WGWorld) (a : Ambient) (h : List HandshakeAdmission) :
    runWGPrefix (admitInitiation mac) w a h =
      match ((initiationAcceptedCheck mac.input).run w).run a with
      | .error err => (.error err,h)
      | .ok ((admission,u),b) =>
        (((initiationAcceptedContinue mac.input admission).run u).run b,
          if admission.isSome then h ++ [.initiation mac ⟨admission,w,u,a,b⟩] else h) := by
  unfold admitInitiation
  change runStatePrefix _ w a h = _
  rw [runStatePrefix_bind]
  have capture := runWGPrefix_captureWGRun (E := HandshakeAdmission) (initiationAcceptedCheck mac.input) w a h
  change runStatePrefix _ w a h = _ at capture
  rw [capture]
  cases checked : ((initiationAcceptedCheck mac.input).run w).run a with
  | error err => rfl
  | ok out =>
    rcases out with ⟨⟨admission,u⟩,b⟩
    cases admission <;> simp only [Except.map,Option.isSome_none,Option.isSome_some,
      Bool.false_eq_true,↓reduceIte,runStatePrefix_bind,runStatePrefix_emit] <;> rfl

theorem admitInitiation_success (mac : HandshakeMac) (w v : WGWorld) (a b : Ambient)
    (h journal : List HandshakeAdmission) (pid : PeerId)
    (run : runWGPrefix (admitInitiation mac) w a h = (.ok ((some pid,v),b),journal)) :
    ∃ accepted u c,
      journal = h ++ [.initiation mac ⟨some accepted,w,u,a,c⟩] ∧ accepted.peer = pid ∧
      ((initiationAcceptedCheck mac.input).run w).run a = .ok ((some accepted,u),c) ∧
      ((initiationAcceptedFinish mac.input accepted).run u).run c = .ok ((some pid,v),b) := by
  rw [admitInitiation_run] at run
  cases check : ((initiationAcceptedCheck mac.input).run w).run a with
  | error err => simp only [check] at run; cases run
  | ok out =>
    rcases out with ⟨⟨admission,u⟩,c⟩
    rw [check] at run
    cases admission with
    | none => cases run
    | some accepted =>
      simp only [Option.isSome_some,↓reduceIte,initiationAcceptedContinue,Prod.mk.injEq] at run
      have returned := (hoare_iff_run_ambient _ _ _).mp (initiation_finish_result mac.input accepted)
        u c (some pid) v b True.intro run.1
      exact ⟨accepted,u,c,run.2.symm,Option.some.inj returned.symm,rfl,run.1⟩

theorem admitInitiation_post (mac : HandshakeMac) (valid : mac.Valid) :
    StatePrefixEnsures HandshakeAdmissionFacts.Inv HandshakeAdmissionFacts.Safe (admitInitiation mac)
      (fun result h _ _ => HandshakeAdmissionFacts.Safe h ∧
        ∀ pid, result = some pid → HasAdmission h pid) := by
  intro w a h safe
  obtain ⟨suffix,history,good,normal⟩ := HandshakeAdmissionFacts.initiation mac valid w a h safe
  refine ⟨suffix,history,good,?_⟩
  cases output : runWGPrefix (admitInitiation mac) w a h with
  | mk outcome journal =>
    have good' : HandshakeAdmissionFacts.Safe journal := by
      change HandshakeAdmissionFacts.Safe (runWGPrefix (admitInitiation mac) w a h).2 at good
      simpa only [output] using good
    cases outcome with
    | error err => simp only [runWGPrefix,runStatePrefix] at output; simp [output]
    | ok out =>
      rcases out with ⟨⟨result,v⟩,b⟩
      have post : HandshakeAdmissionFacts.Safe journal ∧
          ∀ pid, result = some pid → HasAdmission journal pid := by
        refine ⟨good',?_⟩
        intro pid same
        subst result
        obtain ⟨accepted,u,c,hist,peer,_,_⟩ := admitInitiation_success mac w v a b h journal pid output
        refine ⟨.initiation mac ⟨some accepted,w,u,a,c⟩,?_,accepted,rfl,peer⟩
        simp [hist]
      simp only [runWGPrefix,runStatePrefix] at output
      simpa only [output] using post

theorem admitResponse_run (mac : HandshakeMac)
    (w : WGWorld) (a : Ambient) (h : List HandshakeAdmission) :
    runWGPrefix (admitResponse mac) w a h =
      match ((responseAcceptedCheck mac.input).run w).run a with
      | .error err => (.error err,h)
      | .ok ((admission,u),b) =>
        (((responseAcceptedContinue mac.input admission).run u).run b,
          if admission.isSome then h ++ [.response mac ⟨admission,w,u,a,b⟩] else h) := by
  unfold admitResponse
  change runStatePrefix _ w a h = _
  rw [runStatePrefix_bind]
  have capture := runWGPrefix_captureWGRun (E := HandshakeAdmission) (responseAcceptedCheck mac.input) w a h
  change runStatePrefix _ w a h = _ at capture
  rw [capture]
  cases checked : ((responseAcceptedCheck mac.input).run w).run a with
  | error err => rfl
  | ok out =>
    rcases out with ⟨⟨admission,u⟩,b⟩
    cases admission <;> simp only [Except.map,Option.isSome_none,Option.isSome_some,
      Bool.false_eq_true,↓reduceIte,runStatePrefix_bind,runStatePrefix_emit] <;> rfl

theorem admitResponse_success (mac : HandshakeMac) (w v : WGWorld) (a b : Ambient)
    (h journal : List HandshakeAdmission) (pid : PeerId)
    (run : runWGPrefix (admitResponse mac) w a h = (.ok ((some pid,v),b),journal)) :
    ∃ accepted u c,
      journal = h ++ [.response mac ⟨some accepted,w,u,a,c⟩] ∧ accepted.peer = pid ∧
      ((responseAcceptedCheck mac.input).run w).run a = .ok ((some accepted,u),c) ∧
      ((responseAcceptedFinish mac.input accepted).run u).run c = .ok ((some pid,v),b) := by
  rw [admitResponse_run] at run
  cases check : ((responseAcceptedCheck mac.input).run w).run a with
  | error err => simp only [check] at run; cases run
  | ok out =>
    rcases out with ⟨⟨admission,u⟩,c⟩
    rw [check] at run
    cases admission with
    | none => cases run
    | some accepted =>
      simp only [Option.isSome_some,↓reduceIte,responseAcceptedContinue,Prod.mk.injEq] at run
      have returned := (hoare_iff_run_ambient _ _ _).mp (response_finish_result mac.input accepted)
        u c (some pid) v b True.intro run.1
      exact ⟨accepted,u,c,run.2.symm,Option.some.inj returned.symm,rfl,run.1⟩

theorem admitResponse_post (mac : HandshakeMac) (valid : mac.Valid) :
    StatePrefixEnsures HandshakeAdmissionFacts.Inv HandshakeAdmissionFacts.Safe (admitResponse mac)
      (fun result h _ _ => HandshakeAdmissionFacts.Safe h ∧
        ∀ pid, result = some pid → HasAdmission h pid) := by
  intro w a h safe
  obtain ⟨suffix,history,good,normal⟩ := HandshakeAdmissionFacts.response mac valid w a h safe
  refine ⟨suffix,history,good,?_⟩
  cases output : runWGPrefix (admitResponse mac) w a h with
  | mk outcome journal =>
    have good' : HandshakeAdmissionFacts.Safe journal := by
      change HandshakeAdmissionFacts.Safe (runWGPrefix (admitResponse mac) w a h).2 at good
      simpa only [output] using good
    cases outcome with
    | error err => simp only [runWGPrefix,runStatePrefix] at output; simp [output]
    | ok out =>
      rcases out with ⟨⟨result,v⟩,b⟩
      have post : HandshakeAdmissionFacts.Safe journal ∧
          ∀ pid, result = some pid → HasAdmission journal pid := by
        refine ⟨good',?_⟩
        intro pid same
        subst result
        obtain ⟨accepted,u,c,hist,peer,_,_⟩ := admitResponse_success mac w v a b h journal pid output
        refine ⟨.response mac ⟨some accepted,w,u,a,c⟩,?_,accepted,rfl,peer⟩
        simp [hist]
      simp only [runWGPrefix,runStatePrefix] at output
      simpa only [output] using post


end Leanux.Proofs.WG.AuthenticatedEffects
