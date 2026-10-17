import Leanux.Proofs.WG.Config.CursorCallbackModel
import Leanux.Proofs.WG.Config.CursorCallbackSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Successful release supplies positivity and the actual no-refusal outcome. -/
theorem cursorPut_normal (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (peerPut (some pid)) (fun g => g.dev = some d)
      (fun _ g => g.dev = some (Index.releasedPeerDevice d pid p) ∧
        0 < p.refcount ∧ Index.peerReleaseRefusal pid p = none) := by
  intro g ambient value final after device run
  by_cases zero : p.refcount = 0
  · simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,device,resident,
      zero,refcountDecAndTest,branch,branchCmp,AmbientM.branch,AmbientM.branchCmp,
      unsupported,AmbientM.unsupported] at run
    cases run
  · have positive : 0 < p.refcount := Nat.pos_of_ne_zero zero
    have outcome := Index.peerPut_exact pid d p resident positive g ambient device
    change (match Index.peerReleaseRefusal pid p with
      | some stop => Campaign2.observeResult (((peerPut (some pid)).run g).run ambient) = .error stop
      | none => ∃ observed, Campaign2.observeResult (((peerPut (some pid)).run g).run ambient) =
          .ok ((), observed) ∧ observed.wg.device = some (Index.releasedPeerDevice d pid p)) at outcome
    rw [run] at outcome
    cases refused : Index.peerReleaseRefusal pid p
    · rw [refused] at outcome
      obtain ⟨observed,returned,post⟩ := outcome
      simp only [Campaign2.observeResult,Except.map,Except.ok.injEq,Prod.mk.injEq] at returned
      obtain ⟨_,rfl⟩ := returned
      exact ⟨post,positive,rfl⟩
    · rw [refused] at outcome
      cases outcome

/-- NULL or successful resident release, including actual last-reference deletion. -/
theorem cursorPut_option_normal (d : Device) (old : Option PeerId)
    (resident : ∀ pid, old = some pid → ∃ p, d.peers[pid]? = some p) :
    Ensures (peerPut old) (fun g => g.dev = some d)
      (fun _ g => g.dev = some (cursorReleased d old)) := by
  cases old with
  | none =>
    intro g ambient value final after device run
    simp [peerPut,branch,AmbientM.branch] at run
    obtain ⟨rfl,rfl⟩ := run
    exact device
  | some pid =>
    obtain ⟨p,hp⟩ := resident pid rfl
    intro g ambient value final after device run
    have effect := cursorPut_normal pid d p hp g ambient value final after device run
    simpa [cursorReleased,hp] using effect.1

/-- Ordered normal handoff; the old peer is read after the optional acquire. -/
theorem cursorHandoff_normal (d : Device) (acquire old : Option PeerId)
    (newResident : ∀ pid, acquire = some pid → ∃ p, d.peers[pid]? = some p)
    (oldResident : ∀ pid, old = some pid → ∃ p, d.peers[pid]? = some p) :
    Ensures (do
      match acquire with
      | none => pure ()
      | some pid => peerGet pid
      peerPut old)
      (fun g => g.dev = some d)
      (fun _ g => g.dev = some (cursorReleased (cursorAcquired d acquire) old)) := by
  have getEffect : Ensures (match acquire with | none => pure () | some pid => peerGet pid)
      (fun g => g.dev = some d) (fun _ g => g.dev = some (cursorAcquired d acquire)) := by
    cases acquire with
    | none =>
      intro g ambient value final after device run
      cases run
      exact device
    | some pid =>
      obtain ⟨p,hp⟩ := newResident pid rfl
      intro g ambient value final after device run
      have effect := ((ensures_iff _ _ _).mpr (peerGet_exact pid d p hp))
        g ambient value final after device run
      simpa [cursorAcquired,hp,withPeer] using effect.1
  have hp : ∀ pid, old = some pid → ∃ p, (cursorAcquired d acquire).peers[pid]? = some p := by
    intro pid ho
    obtain ⟨p,hp⟩ := oldResident pid ho
    cases acquire with
    | none => exact ⟨p,hp⟩
    | some id =>
      obtain ⟨q,hq⟩ := newResident id rfl
      by_cases same : id = pid
      · subst id
        exact ⟨{q with refcount := q.refcount+1},by simp [cursorAcquired,hq]⟩
      · exact ⟨p,by simp [cursorAcquired,hq,Std.TreeMap.getElem?_insert,same,hp]⟩
  cases acquire with
  | none => exact cursorPut_option_normal d old oldResident
  | some pid => exact ensures_bind (peerGet pid) (fun _ => peerPut old) getEffect (fun _ => cursorPut_option_normal _ old hp)

/-- Normal effects of the actual handoff finalizer, without release readiness. -/
theorem cursorDumpFinish_normal (d : Device) (flags : Nat) (attrs : List (String × Json))
    (ctx : DumpCtx) (cursor : Option PeerId) (skb : NlSkb) (done : Bool)
    (parts : Option (Array PeerDumpAttrs))
    (newResident : ∀ pid, cursor = some pid → ∃ p, d.peers[pid]? = some p)
    (oldResident : ∀ pid, ctx.nextPeer = some pid → ∃ p, d.peers[pid]? = some p) :
    Ensures (cursorDumpFinish d flags attrs ctx cursor skb done parts)
      (fun g => g.dev = some d)
      (fun result g => result = cursorCallResult d flags attrs ctx cursor skb done parts ∧
        g.dev = some (cursorReleased (cursorAcquired d (if done then none else cursor)) ctx.nextPeer)) := by
  intro g ambient result final after device run
  let mark (a : Ambient) (site : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision := site,outcome,netRx := a.netRxSection}}
  cases hd : done with
  | true =>
    let before := mark (mark ambient .dumpOutRetZero true) .dumpOutNotDone false
    have body := cursorPut_option_normal d ctx.nextPeer oldResident
    simp [cursorDumpFinish,hd,WG.andM,branch,AmbientM.branch] at run
    change (((peerPut ctx.nextPeer).run g).run before >>= _) = _ at run
    cases h : ((peerPut ctx.nextPeer).run g).run before with
    | error stop => rw [h] at run; cases run
    | ok out =>
      obtain ⟨⟨u,middle⟩,remaining⟩ := out
      have effect := body g before u middle remaining device h
      rw [h] at run
      obtain ⟨⟨rfl,rfl⟩,_⟩ := run
      exact ⟨rfl,effect⟩
  | false =>
    cases hc : cursor with
    | none =>
      let before := mark (mark (mark ambient .dumpOutRetZero true) .dumpOutNotDone true) .dumpOutHasCursor false
      have body := cursorPut_option_normal d ctx.nextPeer oldResident
      simp [cursorDumpFinish,hd,hc,WG.andM,branch,AmbientM.branch] at run
      change (((peerPut ctx.nextPeer).run g).run before >>= _) = _ at run
      cases h : ((peerPut ctx.nextPeer).run g).run before with
      | error stop => rw [h] at run; cases run
      | ok out =>
        obtain ⟨⟨u,middle⟩,remaining⟩ := out
        have effect := body g before u middle remaining device h
        rw [h] at run
        obtain ⟨⟨rfl,rfl⟩,_⟩ := run
        exact ⟨rfl,effect⟩
    | some pid =>
      let before := mark (mark (mark ambient .dumpOutRetZero true) .dumpOutNotDone true) .dumpOutHasCursor true
      have body := cursorHandoff_normal d (some pid) ctx.nextPeer
        (fun id eq => newResident id (hc.trans eq)) oldResident
      simp [cursorDumpFinish,hd,hc,WG.andM,branch,AmbientM.branch] at run
      change (((peerGet pid).run g).run before >>= _) = _ at run
      cases hg : ((peerGet pid).run g).run before with
      | error stop => rw [hg] at run; cases run
      | ok acquired =>
        obtain ⟨⟨u,middle⟩,remaining⟩ := acquired
        rw [hg] at run
        change ((fun a : (Unit × WGWorld) × Ambient =>
          ((cursorCallResult d flags attrs ctx (some pid) skb false parts,a.1.2),
            mark (mark a.2 .dumpRetErr false) .dumpDone false)) <$>
          ((peerPut ctx.nextPeer).run middle).run remaining) = .ok ((result,final),after) at run
        cases hp : ((peerPut ctx.nextPeer).run middle).run remaining with
        | error stop => rw [hp] at run; cases run
        | ok released =>
          obtain ⟨⟨v,last⟩,inputs⟩ := released
          have combined : ((do peerGet pid; peerPut ctx.nextPeer : WG.M Unit).run g).run before =
              .ok ((v,last),inputs) := by
            change (((peerGet pid).run g).run before >>= _) = _
            rw [hg]
            exact hp
          have effect := body g before v last inputs device combined
          rw [hp] at run
          obtain ⟨⟨rfl,rfl⟩,_⟩ := run
          exact ⟨rfl,effect⟩

end Leanux.Proofs.WG.Config
