import Leanux.Proofs.WG.Roaming.NapiPublicationFrames
import Leanux.Proofs.WG.Roaming.PollEndpointClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Env Noise

/-- Actual successful queue reads return the logical first retained packet. -/
theorem PrevQueue_peek_head (q : PrevQueue SkbId) :
    Noise.Ensures q.peek (fun _ => True)
      (fun result _ => result.1 = q.all.head?) := by
  intro g ambient result final after _ run
  cases peeked : q.peeked with
  | some id =>
    simp [PrevQueue.peek, peeked, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    simp [PrevQueue.all, peeked]
  | none =>
    cases stub : q.tailIsStub <;> cases items : q.items with
    | nil =>
      simp [PrevQueue.peek, PrevQueue.dequeue, peeked, stub, items,
        branch, AmbientM.branch, invariant, AmbientM.invariant] at run
      all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      all_goals simp [PrevQueue.all, peeked, items]
    | cons id rest =>
      cases rest <;>
        simp [PrevQueue.peek, PrevQueue.dequeue, peeked, stub, items,
          branch, AmbientM.branch] at run
      all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      all_goals simp [PrevQueue.all, peeked, items]

/-- A setter cut's id is derived from the actual queue read, not supplied as
an authentication certificate. The queue may be peeked or physically malformed. -/
theorem pollEndpointPrefix_head (pid : PeerId) (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures (pollEndpointPrefix pid) (fun s => s = entry)
      (fun result _ => ∀ cut, result = .endpoint cut → queueHead entry pid = some cut.id) := by
  let tail (first : Option SkbId) (q : PrevQueue SkbId) : Leanux.M PollPrepared := do
    setPeer pid { (← getPeer pid) with rxQueue := q }
    let go ← WG.andM (branch .rxPollPacket first.isSome) do
      let some f := first | invariant "unreachable"
      branch .rxPollNotUncrypted ((← getRxSkb f).state != .uncrypted)
    if !go then return .drained
    let some id := first | invariant "unreachable"
    let beforeRead ← Campaign2.Product.read
    let pkt ← getRxSkb id
    if pkt.peer != pid then invariant "a packet on another peer's rx_queue"
    setPeer pid { (← getPeer pid) with rxQueue := (← getPeer pid).rxQueue.dropPeeked }
    if ← branch .rxPollNotCrypted (pkt.state != .crypted) then return .rejected id pkt
    let beforeCounter ← Campaign2.Product.read
    let valid ← counterValidate pkt.keypair pkt.nonce
    let afterCounter ← Campaign2.Product.read
    if ← branch .rxPollCounterInvalid !valid then return .rejected id pkt
    let endpoint ← endpointFromSkb pkt.source
    if ← branch .rxPollEndpointFailed endpoint.isNone then return .rejected id pkt
    let some e := endpoint | invariant "unreachable"
    setPeerEndpoint pid e
    let atEndpoint ← Campaign2.Product.read
    return .endpoint ⟨id,pkt,e,beforeRead,beforeCounter,afterCounter,
      .ok (valid,afterCounter),atEndpoint⟩
  have tailId (first : Option SkbId) (q : PrevQueue SkbId) :
      Noise.Product.Ensures (tail first q) (fun _ => True)
        (fun result _ => ∀ cut, result = .endpoint cut → first = some cut.id) := by
    have seq {α : Type} (action : Leanux.M α) (next : α → Leanux.M PollPrepared)
        (h : ∀ x, Noise.Product.Ensures (next x) (fun _ => True)
          (fun result _ => ∀ cut, result = .endpoint cut → first = some cut.id)) :
        Noise.Product.Ensures (action >>= next) (fun _ => True)
          (fun result _ => ∀ cut, result = .endpoint cut → first = some cut.id) := by
      exact Noise.Product.ensures_bind _ _ (by intro _ _ _ _ _; trivial) h
    have reject (id : SkbId) (pkt : RxPacket) :
        Noise.Product.Ensures (pure (.rejected id pkt) : Leanux.M PollPrepared) (fun _ => True)
          (fun result _ => ∀ cut, result = .endpoint cut → first = some cut.id) := by
      intro w result final _ run cut same
      cases run
      cases same
    unfold tail
    refine seq _ _ ?_
    intro p
    refine seq _ _ ?_
    intro ignored
    refine seq _ _ ?_
    intro go
    cases go with
    | false =>
      intro w result final _ run cut same
      cases run
      cases same
    | true =>
      simp only [Bool.not_true,Bool.false_eq_true,ite_false]
      cases first with
      | none => intro w result final _ run; cases run
      | some id =>
        refine seq _ _ ?_
        intro beforeRead
        refine seq _ _ ?_
        intro pkt
        split
        · intro w result final _ run; cases run
        refine seq _ _ ?_
        intro p1
        refine seq _ _ ?_
        intro p2
        refine seq _ _ ?_
        intro ignored
        refine seq _ _ ?_
        intro crypted
        cases crypted with
        | true => exact reject id pkt
        | false =>
          refine seq _ _ ?_
          intro beforeCounter
          refine seq _ _ ?_
          intro valid
          refine seq _ _ ?_
          intro afterCounter
          refine seq _ _ ?_
          intro invalid
          cases invalid with
          | true => exact reject id pkt
          | false =>
            refine seq _ _ ?_
            intro endpoint
            refine seq _ _ ?_
            intro failed
            cases failed with
            | true => exact reject id pkt
            | false =>
              cases endpoint with
              | none => intro w result final _ run; cases run
              | some e =>
                refine seq _ _ ?_
                intro ignored
                refine seq _ _ ?_
                intro atEndpoint
                intro w result final _ run cut same
                cases run
                cases same
                rfl
  have liftFacts {α : Type} (action : WG.M α) (P : WGWorld → Prop)
      (Q : α → WGWorld → Prop) (fact : Noise.Ensures action P Q) :
      Noise.Product.Ensures (liftWG action) (fun w => P w.wg) (fun x w => Q x w.wg) := by
    intro w x final pre run
    change ((action.run w.wg).run w.ambient >>= fun ((y,g),a) => Except.ok (y,{w with wg := g,ambient := a})) = _ at run
    cases native : (action.run w.wg).run w.ambient with
    | error stop => rw [native] at run; cases run
    | ok out =>
      obtain ⟨⟨y,g⟩,a⟩ := out
      rw [native] at run
      cases run
      exact fact w.wg w.ambient x g a pre native
  intro w result final pre run
  subst entry
  have factor : pollEndpointPrefix pid = (do
      let p ← getPeer pid
      let selected ← p.rxQueue.peek
      tail selected.1 selected.2) := rfl
  rw [factor,StateT.run_bind] at run
  change ((liftWG (getPeer pid)).run w >>= fun (p,next) =>
    ((do let selected ← p.rxQueue.peek; tail selected.1 selected.2) : Leanux.M PollPrepared).run next) = _ at run
  cases hr : (liftWG (getPeer pid)).run w with
  | error stop => rw [hr] at run; cases run
  | ok out =>
    obtain ⟨p,next⟩ := out
    have hp := liftFacts _ _ _ ((Noise.ensures_iff _ _ _).mpr (getPeer_spec pid (fun g => g = w.wg)))
      w p next rfl hr
    have resident : Noise.peerAt w.wg pid = some p := by simpa [hp.1] using hp.2
    rw [hr] at run
    change ((liftWG p.rxQueue.peek).run next >>= fun (selected,after) =>
      (tail selected.1 selected.2).run after) = _ at run
    cases hs : (liftWG p.rxQueue.peek).run next with
    | error stop => rw [hs] at run; cases run
    | ok out =>
      obtain ⟨⟨first,q⟩,after⟩ := out
      have head := liftFacts _ _ _ (PrevQueue_peek_head p.rxQueue) next (first,q) after trivial hs
      rw [hs] at run
      intro cut same
      have selected := tailId first q after result final trivial run cut same
      have original : queueHead (Campaign2.Product.snapshot w) pid = p.rxQueue.all.head? := by
        change (w.wg.dev.bind fun d => (d.peers[pid]?).bind fun p => p.rxQueue.all.head?) = _
        rw [← Option.bind_assoc]
        change (Noise.peerAt w.wg pid).bind (fun p => p.rxQueue.all.head?) = _
        rw [resident]
        rfl
      exact original.trans (head.symm.trans selected)

theorem pollInitialPrefix_head (pid : PeerId) (budget : Nat) (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures (pollInitialPrefix pid budget) (fun s => s = entry)
      (fun result _ => ∀ cut, result = some (.endpoint cut) → queueHead entry pid = some cut.id) := by
  intro w result final pre run cut same
  subst entry
  by_cases zero : budget = 0
  · simp [pollInitialPrefix,branch,AmbientM.branch,zero] at run
    rcases run with ⟨rfl,rfl⟩
    cases same
  · let next := {w with ambient := {w.ambient with steps := w.ambient.steps.push {
      decision := .rxPollNoBudget,outcome := false,netRx := w.ambient.netRxSection}}}
    have falseB : (budget == 0) = false := by simp [zero]
    have factor : (pollInitialPrefix pid budget).run w =
        ((pollEndpointPrefix pid).run next >>= fun (prepared,out) => Except.ok (some prepared,out)) := by
      simp [pollInitialPrefix,branch,AmbientM.branch,falseB,next,StateT.run_bind]
      rfl
    rw [factor] at run
    cases hp : (pollEndpointPrefix pid).run next with
    | error stop => rw [hp] at run; cases run
    | ok out =>
      obtain ⟨prepared,after⟩ := out
      rw [hp] at run
      cases run
      have head := pollEndpointPrefix_head pid (Campaign2.Product.snapshot next) next prepared final rfl hp cut
        (Option.some.inj same)
      exact head

theorem observedNapiFirst_facts (pending : Option (List PeerId)) (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures (observedNapiFirst pending) (fun s => s = entry)
      (fun result _ => NapiFirstFacts pending entry result) := by
  intro w result final pre run cut same
  subst entry
  cases selected : pending.bind List.head? with
  | none =>
    have factor : (observedNapiFirst pending).run w =
        ((napiPublicationTail pending).run w >>= fun (_,out) => Except.ok (none,out)) := by
      simp only [observedNapiFirst,selected,pure_bind]
      rfl
    rw [factor] at run
    cases ht : (napiPublicationTail pending).run w with
    | error stop => rw [ht] at run; cases run
    | ok out => rw [ht] at run; cases run; cases same
  | some pid =>
    let actual : NapiFirstCut := ⟨pid,Campaign2.Product.snapshot w,
      Campaign2.Product.observeResult ((pollInitialPrefix pid NAPI_POLL_WEIGHT).run w)⟩
    have factor : (observedNapiFirst pending).run w =
        ((napiPublicationTail pending).run w >>= fun (_,out) => Except.ok (some actual,out)) := by
      simp only [observedNapiFirst,selected,pure_bind]
      rfl
    rw [factor] at run
    cases ht : (napiPublicationTail pending).run w with
    | error stop => rw [ht] at run; cases run
    | ok out =>
      rw [ht] at run
      have eq : some actual = result := congrArg Prod.fst (Except.ok.inj run)
      have eqCut : actual = cut := Option.some.inj (eq.trans same)
      subst cut
      refine ⟨rfl,rfl,?_⟩
      intro endpoint atEndpoint observed
      change Campaign2.Product.observeResult ((pollInitialPrefix pid NAPI_POLL_WEIGHT).run w) = _ at observed
      cases hp : (pollInitialPrefix pid NAPI_POLL_WEIGHT).run w with
      | error stop =>
        simp only [Campaign2.Product.observeResult,hp,Except.map] at observed
        cases observed
      | ok out =>
        obtain ⟨prepared,after⟩ := out
        simp only [Campaign2.Product.observeResult,hp,Except.map] at observed
        have eqPrepared : prepared = some (.endpoint endpoint) := congrArg Prod.fst (Except.ok.inj observed)
        refine ⟨(pollInitialPrefix_facts pid NAPI_POLL_WEIGHT (Campaign2.Product.snapshot w)
          w prepared after (fun _ => rfl) hp endpoint eqPrepared).2,?_⟩
        exact pollInitialPrefix_head pid NAPI_POLL_WEIGHT (Campaign2.Product.snapshot w)
          w prepared after rfl hp endpoint eqPrepared


end Leanux.Proofs.WG.Roaming
