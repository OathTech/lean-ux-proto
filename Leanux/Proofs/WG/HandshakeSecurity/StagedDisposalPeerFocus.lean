import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalPeerObserved
import Leanux.Proofs.Logged.FocusComposition
import Leanux.Proofs.WG.AuthenticatedEffects.LifetimeEffectsFocus

/-! Embed the exact peer-access observer inside a larger journal while
retaining its native release cut. Focus distributes over the actual appended
history, including the first Stop; no history-independent callback is assumed. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.PeerSource
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

structure Ops.Appends (o : Ops (WGPrefix E)) : Prop where
  step : ∀ {α} (action : WG.M α), StateAppends (o.step action)
  read : ∀ pid, StateAppends (o.read pid)
  write : ∀ pid p, StateAppends (o.write pid p)
  erase : ∀ pid dropped, StateAppends (o.erase pid dropped)

def Ops.focus (encode : E → F) (decode : F → Option E) (o : Ops (WGPrefix E)) : Ops (WGPrefix F) where
  step := fun a => focusStatePrefix encode decode (o.step a)
  read := fun pid => focusStatePrefix encode decode (o.read pid)
  write := fun pid p => focusStatePrefix encode decode (o.write pid p)
  erase := fun pid dropped => focusStatePrefix encode decode (o.erase pid dropped)

private def Aligned (encode : E → F) (decode : F → Option E)
    (g : WGPrefix F α) (t : WGPrefix E α) : Prop :=
  StateAppends t ∧ g = focusStatePrefix encode decode t

private theorem aligned_native (encode : E → F) (decode : F → Option E)
    (t : WGPrefix E α) (ht : StateAppends t) :
    Aligned encode decode (focusStatePrefix encode decode t) t := ⟨ht,rfl⟩

private theorem aligned_pure (encode : E → F) (decode : F → Option E) (x : α) :
    Aligned encode decode (pure x) (pure x) := by
  refine ⟨StateAppends.pure x,?_⟩
  funext w a h
  change (Except.ok (ε := Stop) ((x,w),a),h) = (Except.ok (ε := Stop) ((x,w),a),h ++ ((h.filterMap decode).drop (h.filterMap decode).length).map encode)
  simp

private theorem aligned_bind (encode : E → F) (decode : F → Option E)
    (inverse : ∀ e, decode (encode e) = some e)
    {g : WGPrefix F α} {t : WGPrefix E α} {f : α → WGPrefix F β} {b : α → WGPrefix E β}
    (hg : Aligned encode decode g t) (hf : ∀ x, Aligned encode decode (f x) (b x)) :
    Aligned encode decode (g >>= f) (t >>= b) := by
  refine ⟨hg.1.bind (fun x => (hf x).1),?_⟩
  rw [hg.2]
  have same : f = fun x => focusStatePrefix encode decode (b x) := funext (fun x => (hf x).2)
  rw [same]
  funext w a h
  exact focusPrefix_bind_appends encode decode inverse (hg.1 w)
    (fun out => (hf out.1).1 out.2) a h

private theorem aligned_choice (encode : E → F) (decode : F → Option E) (p : Prop) [Decidable p]
    {g k : WGPrefix F α} {t b : WGPrefix E α}
    (hg : p → Aligned encode decode g t) (hk : ¬p → Aligned encode decode k b) :
    Aligned encode decode (if p then g else k) (if p then t else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact hg hp
  · exact hk hp


macro "disposal_peer_align " enc:ident dec:ident inv:ident h:ident : tactic => `(tactic| first
  | with_reducible exact aligned_native $enc $dec _ (Ops.Appends.step $h _)
  | with_reducible exact aligned_native $enc $dec _ (Ops.Appends.read $h _)
  | with_reducible exact aligned_native $enc $dec _ (Ops.Appends.write $h _ _)
  | with_reducible exact aligned_native $enc $dec _ (Ops.Appends.erase $h _ _)
  | (maintenance_head Pure.pure; exact aligned_pure $enc $dec _)
  | (maintenance_head Bind.bind; apply aligned_bind $enc $dec $inv)
  | (maintenance_head ite; apply aligned_choice $enc $dec)
  | (maintenance_intro; try dsimp only)
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

variable (encode : E → F) (decode : F → Option E) (inverse : ∀ e, decode (encode e) = some e)
  (o : Ops (WGPrefix E)) (h : Ops.Appends o)
include inverse h

private theorem cut_aligned (peer : Option PeerId) :
    Aligned encode decode (cutWith (Ops.focus encode decode o) peer) (cutWith o peer) := by
  unfold cutWith
  simp only [Ops.focus]
  repeat' disposal_peer_align encode decode inverse h

theorem cut_focus (peer : Option PeerId) :
    cutWith (Ops.focus encode decode o) peer = focusStatePrefix encode decode (cutWith o peer) :=
  (cut_aligned encode decode inverse o h peer).2

private theorem put_aligned (peer : Option PeerId) :
    Aligned encode decode (putWith (Ops.focus encode decode o) peer) (putWith o peer) := by
  unfold putWith
  repeat' first
    | exact cut_aligned encode decode inverse o h peer
    | disposal_peer_align encode decode inverse h
  exact aligned_native encode decode _ (h.step _)

theorem put_focus (peer : Option PeerId) :
    putWith (Ops.focus encode decode o) peer = focusStatePrefix encode decode (putWith o peer) :=
  (put_aligned encode decode inverse o h peer).2

omit inverse h o in
theorem peers_appends : Ops.Appends peers where
  step := StateAppends.lift
  read := by
    intro pid w a hist
    change ∃ suffix, (runStatePrefix (Peers.getPeerPrefix pid) w a hist).2 = hist ++ suffix
    rw [Peers.getPeerPrefix_run]
    cases run : ((getPeer pid).run w).run a with
    | error err => exact ⟨[], by simp⟩
    | ok out => rcases out with ⟨⟨p,v⟩,b⟩; exact ⟨[.read pid p.internalId],rfl⟩
  write := by
    intro pid p w a hist
    change ∃ suffix, (runStatePrefix (Peers.setPeerPrefix pid p) w a hist).2 = hist ++ suffix
    rw [Peers.setPeerPrefix_run]
    split
    · exact ⟨[.write pid p.internalId],rfl⟩
    · exact ⟨[], by simp⟩
  erase := by
    intro pid dropped w a hist
    change ∃ suffix, (runStatePrefix (Peers.erasePeerPrefix pid dropped) w a hist).2 = hist ++ suffix
    rw [Peers.erasePeerPrefix_run]
    split
    · exact ⟨[], by simp⟩
    · exact ⟨[_],rfl⟩

omit encode decode inverse o h in
theorem put_focused_peers (encode : Peers.PeerEvent → F) (decode : F → Option Peers.PeerEvent)
    (inverse : ∀ e, decode (encode e) = some e) (peer : Option PeerId) :
    putWith (Ops.focus encode decode peers) peer =
      focusStatePrefix encode decode (Peers.peerPutPrefix peer) := by
  rw [put_focus encode decode inverse peers peers_appends,put_peers]

omit encode decode inverse o h in
theorem observed_focused_peers_projects {g : Ops (WGPrefix E)}
    (ρ : E → Option F) (encode : Peers.PeerEvent → F) (decode : F → Option Peers.PeerEvent)
    (inverse : ∀ e, decode (encode e) = some e)
    (project : Ops.Projects ρ g (Ops.focus encode decode peers))
    (record : Event → E) (quiet : ∀ event, ρ (record event) = none) (peer : Option PeerId) :
    StateProjectsPrefix ρ id (observed g record peer)
      (focusStatePrefix encode decode (Peers.peerPutPrefix peer)) := by
  rw [← put_focused_peers encode decode inverse]
  exact observed_projects ρ project record quiet peer

omit encode decode inverse o h in
/-- The actual mixed lifetime callback is recovered without dropping its
peer-read, peer-write, or peer-release events. The new disposal receipt is the
only event removed by the stated selector. -/
theorem observed_mixed_projects {g : Ops (WGPrefix E)}
    (ρ : E → Option Lifetimes.LifetimeEvent)
    (project : Ops.Projects ρ g
      (Ops.focus Lifetimes.LifetimeEvent.peer Lifetimes.LifetimeEvent.peer? peers))
    (record : Event → E) (quiet : ∀ event, ρ (record event) = none) (peer : Option PeerId) :
    StateProjectsPrefix ρ id (observed g record peer) (Lifetimes.peerPutMixed peer) :=
  observed_focused_peers_projects ρ _ _ (fun _ => rfl) project record quiet peer

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.PeerSource
