import Leanux.Proofs.WG.Noise.ReceptionCallerSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.ReceptionCaller
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.WG.Origins

def InitiationShape (msg : List UInt8) (h : List TagReceipt) : Prop :=
  (∃ r, h = [r] ∧ r.operation = .consumeInitiation msg ∧ r.result = .consumed none) ∨
  (∃ r pid tail, h = r :: tail ∧ r.operation = .consumeInitiation msg ∧
    r.result = .consumed (some pid) ∧ ResponseShape pid tail)

def ResponseInputShape (msg : List UInt8) (h : List TagReceipt) : Prop :=
  (∃ r, h = [r] ∧ r.operation = .consumeResponse msg ∧ r.result = .consumed none) ∨
  (∃ r se pid ok, h = [r,se] ∧ r.operation = .consumeResponse msg ∧
    r.result = .consumed (some pid) ∧ se.operation = .beginSession pid ∧
    se.result = .begun ok)

def SelectedShape (msg : List UInt8) (needsCookie : Bool) (h : List TagReceipt) : Prop :=
  if messageType msg == MESSAGE_HANDSHAKE_INITIATION then
    if needsCookie then h = [] else InitiationShape msg h
  else if messageType msg == MESSAGE_HANDSHAKE_RESPONSE then
    if needsCookie then h = [] else ResponseInputShape msg h
  else False

theorem finish_none_impossible (msg : List UInt8) (P : List TagReceipt → Prop) :
    StatePrefixEnsures (fun h _ _ => P h) (fun _ => True) (finish msg none)
      (fun _ _ _ _ => False) := by
  intro g ambient h prior
  exact ⟨[], (List.append_nil h).symm, True.intro, True.intro⟩

theorem selected_dispatch_shape (msg : List UInt8) (src : SkbSource)
    (needsCookie : Bool) (initial : List TagReceipt) :
    StatePrefixEnsures (fun h _ _ => h = initial) (fun _ => True) (selected msg src needsCookie)
      (fun _ h _ _ => ∃ tail, h = initial ++ tail ∧ SelectedShape msg needsCookie tail) := by
  unfold selected
  dsimp (config := { zeta := false }) only [ops]
  apply branch_then
  by_cases initiation : (messageType msg == MESSAGE_HANDSHAKE_INITIATION) = true
  · simp only [initiation, ite_true, SelectedShape]
    apply branch_then
    cases needsCookie with
    | true =>
      simp only [ite_true]
      apply StatePrefixEnsures.bind (lift_history _ (fun h => h = initial))
      intro u
      exact StatePrefixEnsures.pure () (fun _ _ _ _ => True.intro)
        (fun _ _ _ prior => ⟨[],by simpa only [List.append_nil] using prior,rfl⟩)
    | false =>
      simp only [Bool.false_eq_true,ite_false]
      apply record_then
      intro value r operation result
      cases value with
      | none =>
        apply branch_then
        simp only [Option.isNone_none,ite_true]
        exact StatePrefixEnsures.pure () (fun _ _ _ _ => True.intro)
          (fun _ _ _ prior => ⟨[r],prior,Or.inl ⟨r,rfl,operation,result⟩⟩)
      | some pid =>
        apply branch_then
        simp only [Option.isNone_some,Bool.false_eq_true,ite_false]
        apply StatePrefixEnsures.bind (lift_history _ (fun h => h = initial ++ [r]))
        intro u
        apply StatePrefixEnsures.bind (response_shape pid (initial ++ [r]))
        intro u
        let Finished := fun h => ∃ tail, h = initial ++ tail ∧ InitiationShape msg tail
        apply StatePrefixEnsures.consequence (finish_history msg (some pid) Finished)
        · intro h g ambient prior
          obtain ⟨tail,hist,shape⟩ := prior
          refine ⟨r::tail,?_,Or.inr ⟨r,pid,tail,rfl,operation,result,shape⟩⟩
          simpa only [List.append_assoc,List.singleton_append] using hist
        · intro value h g ambient prior
          exact prior
  · simp only [initiation, SelectedShape]
    apply branch_then
    by_cases response : (messageType msg == MESSAGE_HANDSHAKE_RESPONSE) = true
    · simp only [response,ite_true]
      apply branch_then
      cases needsCookie with
      | true =>
        simp only [ite_true]
        apply StatePrefixEnsures.bind (lift_history _ (fun h => h = initial))
        intro u
        exact StatePrefixEnsures.pure () (fun _ _ _ _ => True.intro)
          (fun _ _ _ prior => ⟨[],by simpa only [List.append_nil] using prior,rfl⟩)
      | false =>
        simp only [Bool.false_eq_true,ite_false]
        apply record_then
        intro value r operation result
        cases value with
        | none =>
          apply branch_then
          simp only [Option.isNone_none,ite_true]
          exact StatePrefixEnsures.pure () (fun _ _ _ _ => True.intro)
            (fun _ _ _ prior => ⟨[r],prior,Or.inl ⟨r,rfl,operation,result⟩⟩)
        | some pid =>
          apply branch_then
          simp only [Option.isNone_some,Bool.false_eq_true,ite_false]
          apply StatePrefixEnsures.bind (lift_history _ (fun h => h = initial ++ [r]))
          intro u
          apply record_then
          intro ok se sessionOp sessionResult
          let Finished := fun h => ∃ tail, h = initial ++ tail ∧ ResponseInputShape msg tail
          have pureFinished {α : Type} (x : α) :
              StatePrefixPreserves (fun h _ _ => Finished h) (fun _ => True) (pure x : Obs α) :=
            StatePrefixEnsures.pure x (fun _ _ _ _ => True.intro) (fun _ _ _ prior => prior)
          apply StatePrefixEnsures.consequence (P := fun h _ _ => Finished h)
          · change StatePrefixEnsures (fun h _ _ => Finished h) (fun _ => True) _
              (fun _ h _ _ => Finished h)
            repeat' first
              | (maintenance_head finish; exact finish_history _ _ Finished)
              | (maintenance_head liftWGPrefix; exact lift_history _ Finished)
              | (maintenance_head Pure.pure; exact pureFinished _)
              | (maintenance_head Bind.bind
                 apply StatePrefixEnsures.bind (Q := fun _ h _ _ => Finished h))
              | maintenance_intro
              | maintenance_join_let
              | maintenance_join_use
              | (maintenance_head ite; split)
              | (maintenance_head dite; split)
              | maintenance_reduce
              | maintenance_reduce_match
              | maintenance_match
              | contradiction
          · intro h g ambient prior
            refine ⟨[r,se],?_,Or.inr ⟨r,se,pid,ok,rfl,operation,result,sessionOp,sessionResult⟩⟩
            simpa only [List.append_assoc,List.singleton_append] using prior
          · intro value h g ambient prior
            exact prior
    · simp only [response]
      apply StatePrefixEnsures.consequence (finish_none_impossible msg (fun h => h = initial))
      · intro h g ambient prior
        exact prior
      · intro result h g ambient impossible
        exact False.elim impossible

def gateProceeds (loaded : Bool) (mac : MacState) : Bool :=
  (loaded && (mac == .withCookie)) || ((!loaded) && (mac == .noCookie))

def gateNeedsCookie (loaded : Bool) (mac : MacState) : Bool :=
  loaded && (mac == .noCookie)

def AfterShape (msg : List UInt8) (loaded : Bool) (mac : MacState) (h : List TagReceipt) : Prop :=
  if gateProceeds loaded mac then SelectedShape msg false h
  else if gateNeedsCookie loaded mac then SelectedShape msg true h
  else h = []

theorem choice_then {α : Type} (a : WG.M Bool) (value : Bool)
    (P : List TagReceipt → Prop) (next : Bool → Obs α)
    (Q : α → List TagReceipt → WGWorld → Ambient → Prop)
    (choice : ∀ g ambient result final after,
      (a.run g).run ambient = .ok ((result,final),after) → result = value)
    (rest : StatePrefixEnsures (fun h _ _ => P h) (fun _ => True) (next value) Q) :
    StatePrefixEnsures (fun h _ _ => P h) (fun _ => True)
      (liftWGPrefix a >>= next) Q := by
  apply StatePrefixEnsures.bind (Q := fun result h _ _ => result = value ∧ P h)
  · exact StatePrefixEnsures.lift _ (fun _ _ _ _ => True.intro)
      (fun _ g ambient result final after prior run =>
        ⟨choice g ambient result final after run,prior⟩)
  intro result g ambient h prior
  obtain ⟨rfl,prior⟩ := prior
  exact rest g ambient h prior

theorem after_dispatch_shape (msg : List UInt8) (src : SkbSource)
    (loaded : Bool) (mac : MacState) (initial : List TagReceipt) :
    StatePrefixEnsures (fun h _ _ => h = initial) (fun _ => True) (observeAfter msg src loaded mac)
      (fun _ h _ _ => ∃ tail, h = initial ++ tail ∧ AfterShape msg loaded mac tail) := by
  rw [after_selected]
  dsimp (config := {zeta := false}) only [ops]
  apply choice_then (value := gateProceeds loaded mac)
  · intro g ambient result final after run
    cases loaded <;> cases mac <;> cases run <;> rfl
  by_cases proceed : gateProceeds loaded mac = true
  · simp only [proceed,ite_true,AfterShape]
    exact selected_dispatch_shape msg src false initial
  · simp only [proceed,AfterShape]
    apply choice_then (value := gateNeedsCookie loaded mac)
    · intro g ambient result final after run
      cases loaded <;> cases mac <;> cases run <;> rfl
    by_cases needs : gateNeedsCookie loaded mac = true
    · simp only [needs,ite_true]
      exact selected_dispatch_shape msg src true initial
    · simp only [needs]
      exact StatePrefixEnsures.pure () (fun _ _ _ _ => True.intro)
        (fun _ _ _ prior => ⟨[],by simpa only [List.append_nil] using prior,rfl⟩)

structure GateReceipt where
  before : Campaign2.Snapshot
  loaded : Bool
  mac : MacState
  after : Campaign2.Snapshot

def gate (msg : List UInt8) (src : SkbSource) : WG.M (Bool × MacState) := do
  let loaded ← Cookies.loadPhase
  let mac ← cookieValidatePacket msg src loaded
  return (loaded,mac)

def GateValid (msg : List UInt8) (src : SkbSource) (r : GateReceipt) : Prop :=
  ∃ g ambient final after,
    r.before = Campaign2.snapshot g ambient ∧
    r.after = Campaign2.snapshot final after ∧
    ((gate msg src).run g).run ambient = .ok (((r.loaded,r.mac),final),after)

def observeGate (msg : List UInt8) (src : SkbSource) : WG.M GateReceipt := fun g ambient =>
  ((gate msg src).run g).run ambient |>.map fun ((value,final),after) =>
    ((⟨Campaign2.snapshot g ambient,value.1,value.2,Campaign2.snapshot final after⟩,final),after)

theorem observeGate_discard (msg : List UInt8) (src : SkbSource) :
    (do let r ← observeGate msg src; pure (r.loaded,r.mac)) = gate msg src := by
  funext g ambient
  change ((gate msg src g ambient).map _ >>= _) = gate msg src g ambient
  cases gate msg src g ambient <;> rfl

theorem observeGate_valid (msg : List UInt8) (src : SkbSource) :
    Campaign2.Ensures (observeGate msg src) (fun _ => True)
      (fun r _ => GateValid msg src r) := by
  intro g ambient r final after _ run
  change ((((gate msg src).run g).run ambient).map _) = _ at run
  cases actual : ((gate msg src).run g).run ambient with
  | error stop => simp only [actual,Except.map] at run; cases run
  | ok out =>
    obtain ⟨⟨⟨loaded,mac⟩,next⟩,inputs⟩ := out
    simp only [actual,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
    exact ⟨g,ambient,next,inputs,rfl,rfl,actual⟩

def afterNative (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    WG.M (List TagReceipt) := fun g ambient =>
  let observed := runWGPrefix (observeAfter msg src loaded mac) g ambient []
  observed.1.map fun ((_,final),after) => ((observed.2,final),after)

theorem afterNative_discard (msg : List UInt8) (src : SkbSource)
    (loaded : Bool) (mac : MacState) :
    (do let _ ← afterNative msg src loaded mac; pure ()) = Cookies.afterMac msg src loaded mac := by
  funext g ambient
  have erased := afterMac_erases msg src loaded mac g ambient []
  change (runWGPrefix (observeAfter msg src loaded mac) g ambient []).1 = _ at erased
  change (((afterNative msg src loaded mac).run g).run ambient >>= fun ((_,final),after) =>
    Except.ok (((),final),after)) = _
  cases observed : runWGPrefix (observeAfter msg src loaded mac) g ambient [] with
  | mk result history =>
    cases result with
    | error stop =>
      simpa only [StateT.run,afterNative,observed,Except.map,bind,Except.bind] using erased
    | ok result =>
      obtain ⟨⟨u,final⟩,after⟩ := result
      cases u
      simpa only [StateT.run,afterNative,observed,Except.map,bind,Except.bind] using erased

theorem afterNative_claim (msg : List UInt8) (src : SkbSource)
    (loaded : Bool) (mac : MacState) :
    Campaign2.Ensures (afterNative msg src loaded mac) (fun _ => True)
      (fun history _ => AfterShape msg loaded mac history ∧
        ∀ r ∈ history, ReceiptValid r ∧ TagReceiptEffect r) := by
  intro g ambient history final after _ run
  cases observed : runWGPrefix (observeAfter msg src loaded mac) g ambient [] with
  | mk result events =>
    cases result with
    | error stop =>
      simp only [StateT.run,afterNative,observed,Except.map] at run
      cases run
    | ok result =>
      obtain ⟨⟨u,current⟩,inputs⟩ := result
      cases u
      simp only [StateT.run,afterNative,observed,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
      obtain ⟨suffix,appended,safe,normal⟩ :=
        after_dispatch_shape msg src loaded mac [] g ambient [] rfl
      obtain ⟨suffix',appended',valid,normal'⟩ :=
        afterMac_valid msg src loaded mac g ambient [] (by intro r member; cases member)
      have raw := observed
      simp only [runWGPrefix,runStatePrefix] at raw
      simp only [raw] at normal valid
      obtain ⟨found,same,shape⟩ := normal
      simp only [List.nil_append] at same
      subst found
      exact ⟨shape,fun r member => ⟨valid r member,(valid r member).effect⟩⟩

inductive GateEntry where
  | cookie
  | checked (receipt : GateReceipt)

structure ReceptionCall where
  gate : GateEntry
  receipts : List TagReceipt

def observeClassified (msg : List UInt8) (src : SkbSource) : WG.M ReceptionCall := do
  if ← branch .hsCookie (messageType msg == MESSAGE_HANDSHAKE_COOKIE) then
    cookieMessageConsume msg
    return ⟨.cookie,[]⟩
  let r ← observeGate msg src
  let receipts ← afterNative msg src r.loaded r.mac
  return ⟨.checked r,receipts⟩

theorem observeClassified_discard (msg : List UInt8) (src : SkbSource) :
    (do let _ ← observeClassified msg src; pure ()) = receiveHandshakePacket msg src := by
  rw [Cookies.receive_factor]
  simp only [observeClassified,bind_assoc]
  apply bind_congr
  intro cookie
  split
  · simp only [bind_assoc,pure_bind]
  · simp only [bind_assoc,pure_bind]
    change (do
      let r ← observeGate msg src
      (do let _ ← afterNative msg src r.loaded r.mac; pure ())) = _
    simp only [afterNative_discard]
    calc
      _ = (do let result ← gate msg src; Cookies.afterMac msg src result.1 result.2) := by
        rw [← observeGate_discard msg src]
        simp only [bind_assoc,pure_bind]
      _ = _ := by simp only [gate,bind_assoc,pure_bind]

def EntryShape (msg : List UInt8) (call : ReceptionCall) : Prop :=
  match call.gate with
  | .cookie => (messageType msg == MESSAGE_HANDSHAKE_COOKIE) = true ∧ call.receipts = []
  | .checked r => (messageType msg == MESSAGE_HANDSHAKE_COOKIE) = false ∧
      AfterShape msg r.loaded r.mac call.receipts

def GateEntryValid (msg : List UInt8) (src : SkbSource) (entry : GateEntry) : Prop :=
  match entry with
  | .cookie => True
  | .checked r => GateValid msg src r

theorem observeClassified_native (msg : List UInt8) (src : SkbSource) :
    Campaign2.Ensures (observeClassified msg src) (fun _ => True)
      (fun call _ => EntryShape msg call ∧ GateEntryValid msg src call.gate ∧
        ∀ r ∈ call.receipts, ReceiptValid r ∧ TagReceiptEffect r) := by
  intro g ambient call final after _ run
  let next : Ambient := {ambient with steps := (ambient.steps.push
    {decision := .hsCookie, outcome := messageType msg == MESSAGE_HANDSHAKE_COOKIE,
      netRx := ambient.netRxSection})}
  change ((if messageType msg == MESSAGE_HANDSHAKE_COOKIE then
    (do cookieMessageConsume msg; pure (⟨.cookie,[]⟩ : ReceptionCall))
    else (do let r ← observeGate msg src
             let receipts ← afterNative msg src r.loaded r.mac
             pure (⟨.checked r,receipts⟩ : ReceptionCall))) g next) = _ at run
  by_cases cookie : (messageType msg == MESSAGE_HANDSHAKE_COOKIE) = true
  · simp only [cookie,ite_true] at run
    change (cookieMessageConsume msg g next >>= fun ((_,current),inputs) =>
      Except.ok (((⟨.cookie,[]⟩ : ReceptionCall),current),inputs)) = _ at run
    cases consumed : cookieMessageConsume msg g next with
    | error stop => rw [consumed] at run; cases run
    | ok out =>
      obtain ⟨⟨u,current⟩,inputs⟩ := out
      rw [consumed] at run
      cases run
      exact ⟨⟨cookie,rfl⟩,True.intro,by intro r member; cases member⟩
  · simp only [cookie] at run
    change (observeGate msg src g next >>= fun ((r,current),inputs) =>
      afterNative msg src r.loaded r.mac current inputs >>= fun ((history,last),tail) =>
        Except.ok (((⟨.checked r,history⟩ : ReceptionCall),last),tail)) = _ at run
    cases checked : observeGate msg src g next with
    | error stop => rw [checked] at run; cases run
    | ok out =>
      obtain ⟨⟨r,current⟩,inputs⟩ := out
      simp only [checked,bind,Except.bind] at run
      have gateValid := observeGate_valid msg src g next r current inputs True.intro checked
      cases observed : afterNative msg src r.loaded r.mac current inputs with
      | error stop => rw [observed] at run; cases run
      | ok out =>
        obtain ⟨⟨history,last⟩,tail⟩ := out
        rw [observed] at run
        cases run
        obtain ⟨shape,valid⟩ :=
          afterNative_claim msg src r.loaded r.mac current inputs history last tail True.intro observed
        exact ⟨⟨Bool.eq_false_iff.mpr cookie,shape⟩,gateValid,valid⟩

inductive DispatchKind where
  | cookie | macDrop | cookieReplyAttempt | initiation | response | wrongType
  deriving DecidableEq

def selectedKind (msg : List UInt8) (needsCookie : Bool) : DispatchKind :=
  if messageType msg == MESSAGE_HANDSHAKE_INITIATION then
    if needsCookie then .cookieReplyAttempt else .initiation
  else if messageType msg == MESSAGE_HANDSHAKE_RESPONSE then
    if needsCookie then .cookieReplyAttempt else .response
  else .wrongType

def dispatchKind (msg : List UInt8) (entry : GateEntry) : DispatchKind :=
  match entry with
  | .cookie => .cookie
  | .checked r =>
    if gateProceeds r.loaded r.mac then selectedKind msg false
    else if gateNeedsCookie r.loaded r.mac then selectedKind msg true
    else .macDrop

theorem InitiationShape.nonempty {msg : List UInt8} {h : List TagReceipt}
    (shape : InitiationShape msg h) : h ≠ [] := by
  rcases shape with ⟨r,rfl,_,_⟩ | ⟨r,pid,tail,rfl,_,_,_⟩ <;> simp

theorem ResponseInputShape.nonempty {msg : List UInt8} {h : List TagReceipt}
    (shape : ResponseInputShape msg h) : h ≠ [] := by
  rcases shape with ⟨r,rfl,_,_⟩ | ⟨r,se,pid,ok,rfl,_,_,_,_⟩ <;> simp

theorem selected_classifies {msg : List UInt8} {needs : Bool} {h : List TagReceipt}
    (shape : SelectedShape msg needs h) :
    selectedKind msg needs ≠ .wrongType ∧
    (h ≠ [] ↔ selectedKind msg needs = .initiation ∨ selectedKind msg needs = .response) := by
  by_cases initiation : (messageType msg == MESSAGE_HANDSHAKE_INITIATION) = true
  · cases needs <;> simp only [SelectedShape,selectedKind,initiation,ite_true,
      Bool.false_eq_true,ite_false] at shape ⊢
    · exact ⟨by decide,⟨fun _ => Or.inl True.intro,fun _ => shape.nonempty⟩⟩
    · subst h; simp
  · by_cases response : (messageType msg == MESSAGE_HANDSHAKE_RESPONSE) = true
    · cases needs <;> simp only [SelectedShape,selectedKind,initiation,response,ite_true,
        ite_false,Bool.false_eq_true] at shape ⊢
      · exact ⟨by decide,⟨fun _ => Or.inr True.intro,fun _ => shape.nonempty⟩⟩
      · subst h; simp
    · simp [SelectedShape,initiation,response] at shape

theorem EntryShape.classifies {msg : List UInt8} {call : ReceptionCall}
    (shape : EntryShape msg call) :
    dispatchKind msg call.gate ≠ .wrongType ∧
    (call.receipts ≠ [] ↔ dispatchKind msg call.gate = .initiation ∨
      dispatchKind msg call.gate = .response) := by
  obtain ⟨entry,history⟩ := call
  cases entry with
  | cookie =>
    obtain ⟨_,rfl⟩ := shape
    simp [dispatchKind]
  | checked r =>
    obtain ⟨_,shape⟩ := shape
    by_cases proceed : gateProceeds r.loaded r.mac = true
    · simp only [AfterShape,dispatchKind,proceed,ite_true] at shape ⊢
      exact selected_classifies shape
    · by_cases needs : gateNeedsCookie r.loaded r.mac = true
      · simp only [AfterShape,dispatchKind,proceed,needs,ite_true] at shape ⊢
        exact selected_classifies shape
      · simp [AfterShape,proceed,needs] at shape
        subst history
        simp [dispatchKind,proceed,needs]

end Leanux.Proofs.WG.Noise.ReceptionCaller
