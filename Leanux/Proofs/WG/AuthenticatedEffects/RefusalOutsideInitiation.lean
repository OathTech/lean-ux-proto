import Leanux.Proofs.WG.AuthenticatedEffects.RefusalOutsideFrames

/-! Failed native initiations retain all WG fields outside their resident maps,
including outer timer/work scheduling state. The actual pubkey loan excludes a
final peer release at repayment. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.RefusalOutside
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.CounterWindow
open Leanux.Proofs.WG.Queues.RxCredits.HandshakeLoans
open Leanux.Proofs.WG.Cookies
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem pubkey_lookup (key : Key) : SameView view (pubkeyLookup key) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  have read : Preserves (fun w => view w = initial) getDev := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a d v b hi run
    exact (Queues.RxCredits.DecryptCarrier.getDev_current a b run).1 ▸ hi
  unfold pubkeyLookup
  simp only [branch]
  repeat' first
    | (cookie_source_head getDev; exact read)
    | (cookie_source_head peerGetMaybeZero; exact (maybe _).wp (fun v => v = initial))
    | (cookie_source_lift AmbientM; exact hoare_liftAmbient _ _)
    | cookie_source_step

theorem borrowed_safe (initial : WGStoreView) (pid : PeerId) (w : WGWorld)
    (borrowed : PeerBorrow.Borrowed initial (some pid) (wgStoreView w)) : RepaySafe pid w := by
  obtain ⟨d,p,hd,hp,positive,same⟩ := borrowed
  have resident := congrArg WGStoreView.dev same
  change w.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}} at resident
  exact ⟨_,{p with refcount := p.refcount + 1},resident,by simp,by dsimp; omega⟩

private def Refused (initial : WGWorld) (result : Option PeerId) (w : WGWorld) : Prop :=
  result = none → view w = initial

private theorem chain {α β : Type} (P : WGWorld → Prop) (Q : β → WGWorld → Prop)
    (action : WG.M α) (next : α → WG.M β) (ha : Preserves P action)
    (tail : ∀ x, Hoare (next x) P Q) : Hoare (action >>= next) P Q :=
  hoare_bind action next ha tail

theorem initiation_tail (msg e ck hash : Key) (pid : PeerId) (initial : WGWorld) :
    Hoare (initiationTail msg e ck hash (some pid) pid)
      (fun w => view w = initial ∧ RepaySafe pid w) (Refused initial) := by
  let P := fun w => view w = initial ∧ RepaySafe pid w
  have success (ck hash t : Key) (p : Peer) :
      Hoare (initiationSuccess msg e ck hash t (some pid) pid p) P (Refused initial) := by
    apply hoare_consequence (initiationSuccess_some msg e ck hash t (some pid) pid p)
    · exact fun _ _ => True.intro
    · intro result w same none
      rw [same] at none
      cases none
  have out : Hoare (initiationOut (some pid) none) P (Refused initial) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi run _
    change ((peerPut (some pid) >>= fun _ => pure (none : Option PeerId)).run w).run
      (record a .consumeFailedPut true) = _ at run
    rw [MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨doneUnit,u,c,paid,returned⟩ := run
    cases doneUnit
    have same := (repay pid w u _ c hi.2 paid).trans hi.1
    cases returned
    exact same
  have ambient {α : Type} (action : AmbientM α) : Preserves P (monadLift action : WG.M α) :=
    hoare_liftAmbient action P
  have precomputed (ck key : Key) : Preserves P (mixPrecomputedDh ck key) :=
    (mixPrecomputedDh_sameWGWorld ck key).wp P
  have decrypt (sealed key hash : Key) : Preserves P (messageDecrypt sealed key hash) :=
    (messageDecrypt_sameWGWorld sealed key hash).wp P
  have stop (message : String) : Hoare (invariant message : WG.M (Option PeerId)) P (Refused initial) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi run
    cases run
  rw [initiationTail_success_factor]
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64,WG.orM]
  repeat' first
    | with_reducible exact success _ _ _ _
    | with_reducible exact out
    | with_reducible exact stop _
    | with_reducible exact get_peer _ _
    | with_reducible exact precomputed _ _
    | with_reducible exact decrypt _ _ _
    | with_reducible exact ambient _
    | with_reducible exact preserves_pure _
    | cookie_source_step
    | with_reducible apply chain P
    | (session_origin_intro_forall; try dsimp only)
    | split

theorem initiation (msg : List UInt8) (w v : WGWorld) (a b : Ambient)
    (run : ((consumeInitiation msg).run w).run a = .ok ((none,v),b)) : view v = view w := by
  rw [initiationAuthFront_factor,native_bind_run] at run
  cases front : ((initiationAuthFront msg).run w).run a with
  | error err => simp [front] at run
  | ok out =>
    rcases out with ⟨⟨payload,u⟩,c⟩
    rw [front] at run
    have same := (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
      (initiationAuthFront_same_world msg) w a payload u c front
    change u = w at same
    subst u
    cases payload with
    | none =>
      change Except.ok ((none,w),record (record c .consumeFailedPut true) .peerPutNull true) = _ at run
      cases run
      rfl
    | some payload =>
      rcases payload with ⟨e,ck,s,hash⟩
      dsimp only at run
      rw [native_bind_run] at run
      cases lookup : ((pubkeyLookup s).run w).run c with
      | error err => simp [lookup] at run
      | ok out =>
        rcases out with ⟨⟨peer,q⟩,d⟩
        rw [lookup] at run
        have same := (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
          (pubkey_lookup s) w c peer q d lookup
        have borrowed := (hoare_iff_run_ambient _ _ _).mp
          (Leanux.Proofs.WG.AllowedIps.pubkeyLookup_borrowed_spec s (wgStoreView w))
          w c peer q d rfl lookup
        cases peer with
        | none =>
          change Except.ok ((none,q),record (record (record d .consumeNoPeer true)
            .consumeFailedPut true) .peerPutNull true) = _ at run
          cases run
          exact same
        | some pid =>
          change ((initiationTail msg e ck hash (some pid) pid).run q).run
            (record d .consumeNoPeer false) = _ at run
          exact (hoare_iff_run_ambient _ _ _).mp
            (initiation_tail msg e ck hash pid (view w)) q _ none v b
            ⟨same,borrowed_safe _ pid q borrowed⟩ run rfl

end Leanux.Proofs.WG.AuthenticatedEffects.RefusalOutside
