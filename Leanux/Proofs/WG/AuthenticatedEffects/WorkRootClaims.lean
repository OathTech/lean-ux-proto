import Leanux.Proofs.WG.AuthenticatedEffects.WorkRootFacts

/-! Exact native work-creation receipts have authenticated causes in the same
complete receiver call, before the work can later run. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.WorkRoot
open Leanux Leanux.WG Leanux.Proofs.Logged TimerRoot

private theorem lookup_position {α : Type} (xs : List α) (index : Nat) (value : α)
    (found : xs[index]? = some value) :
    ∃ pre post, xs = pre ++ value :: post ∧ pre.length = index := by
  induction xs generalizing index with
  | nil => simp at found
  | cons x xs ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at found
      subst x
      exact ⟨[],xs,rfl,rfl⟩
    | succ index =>
      obtain ⟨pre,post,position,length⟩ := ih index (by simpa using found)
      exact ⟨x :: pre,post,by simp [position],by simp [length]⟩

def AuthenticatedAt (pre : List Event) (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) : Prop :=
  ∃ before after,
    history pre = before ++ .callback kind pid :: after ∧ before.length = origin ∧
      ∃ admission ∈ HandshakeCausal.roots before, admission.Valid ∧ admission.ForPeer pid

private theorem callback_from_index (msg : Key) (src : SkbSource) (w : WGWorld) (a : Ambient)
    (pre post : List Event) (event : Event) (quiet : base event = none)
    (position : (runWGPrefix (receive msg src) w a []).2 = pre ++ event :: post)
    (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (seen : Seen origin kind pid pre) :
    AuthenticatedAt pre origin kind pid := by
  obtain ⟨before,after,splitHistory,index⟩ := lookup_position (history pre) origin (.callback kind pid) seen
  have projected := congrArg Prod.snd (receive_projects msg src w a [])
  rw [position] at projected
  have whole : (runWGPrefix (HandshakeCausal.receive msg src) w a []).2 =
      history pre ++ history post := by
    simpa only [history,List.filterMap_nil,List.filterMap_append,List.filterMap_cons,quiet] using projected
  have callback : (runWGPrefix (HandshakeCausal.receive msg src) w a []).2 =
      before ++ .callback kind pid :: (after ++ history post) := by
    rw [whole,splitHistory]
    simp only [List.append_assoc,List.cons_append]
  exact ⟨before,after,splitHistory,index,
    HandshakeCausal.callback_cause msg src w a before (after ++ history post) kind pid callback⟩

private theorem empty_safe : Safe [] := by
  intro before event after position
  have lengths := congrArg List.length position
  simp only [List.length_nil,List.length_append,List.length_cons] at lengths
  omega

theorem queued_authenticated (msg : Key) (src : SkbSource) (w : WGWorld) (a : Ambient)
    (pre post : List Event) (r : Queued)
    (position : (runWGPrefix (receive msg src) w a []).2 = pre ++ .queued r :: post) :
    r.Native ∧ AuthenticatedAt pre r.origin r.kind r.peer := by
  obtain ⟨suffix,full,safe,_⟩ := receive_safe msg src w a [] empty_safe
  obtain ⟨seen,native⟩ := safe pre (.queued r) post position
  exact ⟨native,callback_from_index msg src w a pre post (.queued r) rfl position
    r.origin r.kind r.peer seen⟩

theorem submitted_authenticated (msg : Key) (src : SkbSource) (w : WGWorld) (a : Ambient)
    (pre post : List Event) (r : Submitted)
    (position : (runWGPrefix (receive msg src) w a []).2 = pre ++ .submitted r :: post) :
    r.Native ∧ AuthenticatedAt pre r.origin r.kind r.peer := by
  obtain ⟨suffix,full,safe,_⟩ := receive_safe msg src w a [] empty_safe
  obtain ⟨seen,native⟩ := safe pre (.submitted r) post position
  exact ⟨native,callback_from_index msg src w a pre post (.submitted r) rfl position
    r.origin r.kind r.peer seen⟩

theorem queued_native_append (r : Queued) (native : r.Native) :
    r.run.after.dev = r.run.before.dev.map
      (fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [r.peer]}) := by
  rcases r with ⟨origin,kind,pid,⟨value,w,v,a,b⟩⟩
  change ((modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}).run w).run a =
    .ok ((value,v),b) at native
  have states := congrArg (fun z => z.toOption.map (fun x => x.1.2.dev)) native
  exact (Option.some.inj states).symm

end Leanux.Proofs.WG.AuthenticatedEffects.WorkRoot
