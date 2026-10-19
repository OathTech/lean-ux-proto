import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWheelPointSource

/-! The actual first read supplies the cached peer's packet fields. They remain
true across ambient guards and timer-only writes, including writes followed by Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Wheel.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity CausalJournal

structure Cache (pid : PeerId) (saved : Peer) (w : WGWorld) : Prop where
  resident : ∃ d peer, w.dev = some d ∧ d.peers[pid]? = some peer ∧
    peer.internalId = saved.internalId ∧ peer.staged = saved.staged ∧ peer.txQueue = saved.txQueue

theorem Cache.same_dev (before : Cache pid saved w) (same : v.dev = w.dev) : Cache pid saved v := by
  obtain ⟨d,p,device,resident,fields⟩ := before.resident
  exact ⟨d,p,same.trans device,resident,fields⟩

theorem read_cache (run : ((getPeer pid).run w).run a = .ok ((p,v),b)) :
    v = w ∧ Cache pid p v := by
  have same := (Peers.getPeer_current pid w v p a b run).1
  subst v
  cases device : w.dev with
  | none => simp [getPeer,getDev,device,invariant,AmbientM.invariant] at run; cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none => simp [getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run; cases run
    | some peer =>
      simp [getPeer,getDev,device,resident] at run
      obtain ⟨rfl,rfl⟩ := run
      exact ⟨rfl,⟨d,peer,device,resident,rfl,rfl,rfl⟩⟩

theorem install_frame (cache : Cache pid saved w)
    (fields : q.internalId = saved.internalId ∧ q.staged = saved.staged ∧ q.txQueue = saved.txQueue)
    (run : ((setPeer pid q).run w).run a = .ok ((value,v),b)) :
    StagedEntry.view v = StagedEntry.view w ∧ Cache pid saved v := by
  obtain ⟨d,p,device,resident,stamp,staged,queue⟩ := cache.resident
  simp [setPeer,modifyDev,device] at run
  rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
  refine ⟨Queued.replace_peer device resident (fields.1.trans stamp.symm)
    (fields.2.1.trans staged.symm) (fields.2.2.trans queue.symm),?_⟩
  exact ⟨{d with peers := d.peers.insert pid q},q,rfl,by simp,fields⟩

theorem Native.frame (token : Native pid saved) {value : token.Result} (cache : Cache pid saved w)
    (run : ((token.body.run w).run a) = .ok ((value,v),b)) :
    StagedEntry.view v = StagedEntry.view w ∧ Cache pid saved v := by
  cases token with
  | ambient action =>
    have same : v = w := (ProjectedAction.iff_run_ambient _ _ _).mp
      (show SameView id (monadLift action : WG.M _) from fun initial =>
        hoare_liftAmbient action (fun w => w = initial)) w a value v b run
    subst v; exact ⟨rfl,cache⟩
  | world => cases run; exact ⟨rfl,cache⟩
  | peer id =>
    have same := (Peers.getPeer_current id w v value a b run).1
    subst v; exact ⟨rfl,cache⟩
  | stamp number => cases run; exact ⟨rfl,cache.same_dev rfl⟩
  | install peer fields => exact install_frame cache fields run
  | failure reason => cases run

theorem native_run (action : WG.M α) (w : World) (h : History) :
    runPrefix (wg action) w h =
      match ((action.run w.wg).run w.ambient) with
      | .error stop => (.error stop,h)
      | .ok ((value,v),b) => (.ok (value,{w with wg := v,ambient := b}),h) := by
  rw [liftWGObserver_run,runWGPrefix_lift]
  cases ((action.run w.wg).run w.ambient) <;> rfl

theorem Native.normal (token : Native pid saved) {value : token.Result} (cache : Cache pid saved w.wg)
    (run : runPrefix token.action w h = (.ok (value,v),last)) :
    last = h ∧ StagedEntry.view v.wg = StagedEntry.view w.wg ∧ Cache pid saved v.wg := by
  rw [native_run] at run
  cases actual : ((token.body.run w.wg).run w.ambient) with
  | error reason => simp only [actual] at run; cases run
  | ok out =>
    obtain ⟨⟨x,u⟩,b⟩ := out
    simp only [actual,Prod.mk.injEq,Except.ok.injEq] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    exact ⟨rfl,token.frame cache actual⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Wheel.Points
