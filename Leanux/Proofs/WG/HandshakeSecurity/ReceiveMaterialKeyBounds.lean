import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialNativeFrames

/-! Only resident numeric key-slot bounds accompany RX material. These state
facts follow native creation and survivor frames and carry no authorization,
funding or independent observer-history premise. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Responder Origins

theorem KeyBounds.retains (before : KeyBounds w)
    (keys : Responder.Retains (pool w) (pool v))
    (frontier : ∀ d e, w.dev = some d → v.dev = some e → d.nextKeypairId ≤ e.nextKeypairId) :
    KeyBounds v := by
  intro e he slot key stored
  have prior := keys slot (keyCore key) (by simp only [pool,he,Option.bind_some,stored,Option.map_some])
  obtain ⟨old,present,_⟩ := Option.map_eq_some_iff.mp prior
  obtain ⟨d,hd,hk⟩ := Option.bind_eq_some_iff.mp present
  exact Nat.lt_of_lt_of_le (before d hd slot old hk) (frontier d e hd he)

theorem key_bounds_frame {action : WG.M α} (keys : CoreRetains action)
    (frontier : ∀ bound, Preserves (ResidentMaterial.Lower bound) action) : Preserves KeyBounds action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  apply before.retains ((ProjectedAction.iff_run_ambient _ _ _).mp keys w a result v b run)
  intro d e hd he
  have lower := (hoare_iff_run_ambient _ _ _).mp (frontier d.nextKeypairId)
    w a result v b (by simp [ResidentMaterial.Lower,ResidentMaterial.cursor,hd]) run
  simpa [ResidentMaterial.Lower,ResidentMaterial.cursor,he] using lower

theorem key_bounds_front (pid : PeerId) : Preserves KeyBounds (SessionOrigin.front pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result with
  | none => exact Origins.front_none pid w v a b run ▸ before
  | some context =>
    obtain ⟨d,key,hd,_,_,_,slot,view,_⟩ := Origins.front_effect pid context w v a b run
    obtain ⟨old,current,oldDev,newDev,_,frontier,_⟩ :=
      (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCreation.«0».Leanux.Proofs.WG.OwnerCreation.front_device)
        pid context w v a b run
    have equal : old = d := Option.some.inj (oldDev.symm.trans hd)
    subst old
    have keys : (fun q => current.keypairs[q]?) =
        (fun q => if context.slot = q then some key else d.keypairs[q]?) :=
      congrArg Prod.snd (Option.some.inj (by simpa only [Origins.view,newDev,Option.map_some] using view))
    intro after device id value resident
    have same : after = current := Option.some.inj (device.symm.trans newDev)
    subst after
    rw [frontier]
    by_cases fresh : context.slot = id
    · rw [←fresh,slot]
      exact Nat.lt_succ_self _
    · have old : d.keypairs[id]? = some value := by
        simpa only [fresh,↓reduceIte] using (congrFun keys id).symm.trans resident
      exact Nat.lt_trans (before d hd id value old) (Nat.lt_succ_self _)

theorem lower_session_tail (pid : PeerId) (kid : KeypairId) :
    Preserves (ResidentMaterial.Lower bound) (SessionOrigin.tail pid kid) := by
  unfold SessionOrigin.tail SessionOrigin.tailWith
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' first
    | (allocation_release_head handshakeZero; exact ResidentMaterial.lower_zero _)
    | (allocation_release_head addNewKeypair; exact ResidentMaterial.lower_rotation _ _)
    | material_cursor_step

theorem key_bounds_session (pid : PeerId) : Preserves KeyBounds (beginSession pid) := by
  rw [SessionOrigin.factor]
  apply preserves_bind (key_bounds_front pid)
  intro result
  cases result with
  | none => exact preserves_pure _
  | some context =>
    exact key_bounds_frame (ResidentMaterial.session_tail_core pid context.slot)
      (fun _ => lower_session_tail pid context.slot)

def Bounded (h : List AuthenticatedEffects.TransportDriver.OriginEvent) (w : WGWorld) : Prop :=
  Inv h w ∧ KeyBounds w

theorem bounded_initial (net bare : Bool) : Bounded [] (Runner.initialWG net bare) :=
  ⟨initial net bare,(allocation_initial net bare _ rfl).keySlots⟩

theorem bounded_frame {action : WG.M α}
    (packets : SameView RxDisposition.nativeRxStore action) (keys : CoreRetains action)
    (frontier : ∀ bound, Preserves (ResidentMaterial.Lower bound) action) :
    Preserves (Bounded h) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (frame packets keys frontier) w a result v b before.1 run,
    (hoare_iff_run_ambient _ _ _).mp (key_bounds_frame keys frontier) w a result v b before.2 run⟩

theorem bounded_session (pid : PeerId) : Preserves (Bounded h) (beginSession pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (session pid) w a result v b before.1 run,
    (hoare_iff_run_ambient _ _ _).mp (key_bounds_session pid) w a result v b before.2 run⟩

theorem bounded_prepare :
    StatePrefixPreserves (fun h w _ => Bounded h w) (fun _ => True) RxOrigin.prepare := by
  intro w a h before
  obtain ⟨suffix,appended⟩ := AuthenticatedEffects.TransportDriver.native_prepare_appends w a h
  refine ⟨suffix,appended,True.intro,?_⟩
  cases result : (runPrefix (RxOrigin.prepare.run w) a h).1 with
  | error err => trivial
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    have native := (RxOrigin.prepare_erases w a h).symm.trans result
    exact ⟨prepare_normal w v a b h _ value before.1 before.2 (Prod.ext result rfl),
      (hoare_iff_run_ambient _ _ _).mp (key_bounds_frame
        (ResidentMaterial.core_of_same prepare_core) (fun _ => prepare_lower _))
        w a value v b before.2 native⟩

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
