import Leanux.Proofs.WG.AuthenticatedEffects.TimerCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.ProtocolFrames
import Leanux.Proofs.WG.Queues.NapiFrames

/-! Native timer provenance frames permit deletion but cannot manufacture a
resident timer observation. Every saved peer write is justified by its source
getter; the incarnation, expiry and entire wheel entry remain together. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TimerSlots
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

abbrev Snapshot := PeerId → PeerTimer → Option (Nat × Option UInt64 × Option WheelEntry)
def Retained (initial : Snapshot) (w : WGWorld) : Prop :=
  ∀ pid timer token, view w pid timer = some token → initial pid timer = some token

theorem retained_refl (w : WGWorld) : Retained (view w) w := fun _ _ _ same => same

theorem Carrier.retain (carrier : Carrier h w) (retained : Retained (view w) v) : Carrier h v :=
  fun pid timer stamp expires entry pending => carrier pid timer stamp expires entry
    (retained pid timer _ pending)

theorem retained_exact {action : WG.M α} (frame : SameView view action) (initial) :
    Preserves (Retained initial) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp frame w a result v b run
  simpa only [Retained,same] using hi

theorem retained_store {action : WG.M α} (frame : SameWGStore action) (initial) :
    Preserves (Retained initial) action :=
  retained_exact (frame.of_factor
    (fun store pid timer => (store.dev.bind fun d => d.peers[pid]?).map
      (fun p => (p.internalId,p.timer timer,p.wheel timer))) view (fun _ => rfl)) initial

theorem retained_read (initial) (pid : PeerId) (next : Peer → WG.M α)
    (tail : ∀ p, (∀ t, initial pid t = some (p.internalId,p.timer t,p.wheel t)) →
      Preserves (Retained initial) (next p)) :
    Preserves (Retained initial) (getPeer pid >>= next) := by
  apply hoare_bind _ _ (show Hoare (getPeer pid) (Retained initial)
    (fun p w => Retained initial w ∧ ∀ t, initial pid t = some (p.internalId,p.timer t,p.wheel t)) from ?_)
  · intro p
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi run
    exact (hoare_iff_run_ambient _ _ _).mp (tail p hi.2) w a result v b hi.1 run
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b hi run
    obtain ⟨rfl,_,d,hd,hp⟩ := Queues.getPeer_normal pid w v p a b run
    exact ⟨hi,fun t => hi pid t _ (by simp only [view,hd,Option.bind_some,hp,Option.map_some])⟩

theorem retained_write (initial) (pid : PeerId) (p : Peer)
    (known : ∀ t, initial pid t = some (p.internalId,p.timer t,p.wheel t)) :
    Preserves (Retained initial) (setPeer pid p) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases run
  intro q t token found
  cases hd : w.dev with
  | none => simp [view,hd] at found
  | some d =>
    simp only [view,hd,Option.map_some,Option.bind_some,Std.TreeMap.getElem?_insert,
      Std.LawfulEqOrd.compare_eq_iff_eq] at found
    by_cases same : pid = q
    · subst q
      simp only [ite_true,Option.map_some,Option.some.injEq] at found
      exact found ▸ known t
    · simp only [ite_eq_right same] at found
      exact hi q t token (by simpa only [view,hd,Option.bind_some] using found)

theorem retained_device (f : Device → Device) (peers : ∀ d, (f d).peers = d.peers) (initial) :
    Preserves (Retained initial) (modifyDev f) := by
  apply retained_exact
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases run
  funext pid t
  change ((w.dev.map f).bind fun d => d.peers[pid]?).map _ = _
  simp only [Option.bind_map,Function.comp_def,peers]
  rfl

theorem retained_erase (pid : PeerId) (f : Device → Device)
    (peers : ∀ d, (f d).peers = d.peers.erase pid) (initial) :
    Preserves (Retained initial) (modifyDev f) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases run
  intro q t token found
  cases hd : w.dev with
  | none => simp [view,hd] at found
  | some d =>
    simp only [view,hd,Option.map_some,Option.bind_some,peers,
      Std.TreeMap.getElem?_erase,Std.LawfulEqOrd.compare_eq_iff_eq] at found
    by_cases same : pid = q
    · simp [same] at found
    · simp only [ite_eq_right same] at found
      exact hi q t token (by simpa only [view,hd,Option.bind_some] using found)

theorem retained_index (action : IndexM α) (initial) :
    Preserves (Retained initial) (monadLift action : WG.M α) := by
  apply hoare_liftIndex action
  intro w d table hi hd
  intro pid t token found
  exact hi pid t token (by simpa only [view,Option.bind_some,hd] using found)

macro "timer_retention_step " initial:term : tactic => `(tactic| first
  | (env_bind_head getPeer; apply retained_read $initial; intro p hp)
  | (rx_retention_head setPeer; apply retained_write $initial; assumption)
  | (rx_retention_head getPeer
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a p v b hi run
     simpa only [(Queues.getPeer_normal _ w v p a b run).1] using hi)
  | (rx_retention_head getDev; exact retained_store getDev_sameWGStore $initial)
  | (rx_retention_head getKeypair
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a k v b hi run
     simpa only [(KeyTimes.getKeypair_return _ w v k a b run).1] using hi)
  | (rx_retention_head setKeypair; unfold setKeypair)
  | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (Retained $initial))
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (rx_retention_head IndexOwner.peerWord; exact indexOwner_peerWord_preserves _ _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (allocation_release_lift_from IndexM; exact retained_index _ $initial)
  | (rx_retention_head get; exact hoare_consequence (hoare_get _)
      (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head modifyDev; apply retained_device; intro d; rfl)
  | (rx_retention_head modify; apply hoare_modify; intro w hi; exact hi)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (Retained $initial)
     intro x state
     change Preserves (Retained $initial) _)
  | (rx_retention_head Functor.discard
     apply discard_view_spec id (Retained $initial)
     change Preserves (Retained $initial) _)
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b hi run
     cases run)
  | rx_retention_step)

theorem peerGet_retained (pid : PeerId) (initial) : Preserves (Retained initial) (peerGet pid) := by
  unfold peerGet refcountInc
  simp (config := {zeta := false}) only [requireNotPending,branch,branchCmp,unsupported]
  repeat' timer_retention_step initial

theorem peerPut_retained (pid : Option PeerId) (initial) : Preserves (Retained initial) (peerPut pid) := by
  unfold peerPut refcountDecAndTest retirePeerUnits
  simp (config := {zeta := false}) only [requireNotPending,branch,branchCmp,invariant,unsupported,modifyAmbient]
  repeat' first
    | (rx_retention_head modifyDev; apply retained_erase; intro d; rfl)
    | timer_retention_step initial

theorem keypairPut_retained (id : Option KeypairId) (now : Bool) (initial) :
    Preserves (Retained initial) (keypairPut id now) := by
  unfold keypairPut refcountDecAndTest
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,unsupported]
  repeat' timer_retention_step initial

theorem protocol_retained {action : WG.M α} (frame : SameView peerProtocolView action) (initial) :
    Preserves (Retained initial) action := by
  apply retained_exact
  apply frame.of_factor (fun peers pid t => (peers pid).map (fun p => (p.internalId,p.timer t,p.wheel t))) view
  intro w
  funext pid t
  simp only [peerProtocolView,Option.map_map,Function.comp_def,view]
  congr 1

theorem peerGetMaybeZero_retained (pid : Option PeerId) (initial) :
    Preserves (Retained initial) (peerGetMaybeZero pid) :=
  protocol_retained (peerGetMaybeZero_protocol pid) initial

theorem indexLookup_retained (kinds : List IndexKind) (index : Nat) (initial) :
    Preserves (Retained initial) (indexLookup kinds index) :=
  protocol_retained (indexLookup_protocol kinds index) initial

theorem pubkeyLookup_retained (key : Key) (initial) : Preserves (Retained initial) (pubkeyLookup key) := by
  unfold pubkeyLookup
  simp only [branch]
  repeat' first
    | (rx_retention_head peerGetMaybeZero; exact peerGetMaybeZero_retained _ initial)
    | timer_retention_step initial

end Leanux.Proofs.WG.AuthenticatedEffects.TimerSlots
