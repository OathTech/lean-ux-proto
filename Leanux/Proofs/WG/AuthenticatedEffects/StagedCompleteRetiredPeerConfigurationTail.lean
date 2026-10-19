import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerAllowedIps
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTimerCallbacks
import Leanux.Proofs.WG.Queues.HolderConfigTail

/-! Configuration retains its actual acquired loan until the native out path.
Normal early errors pay the loan exactly once; queued work retains its own delta. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders
namespace ConfigurationTail

theorem pay (owner : Owner) : Hoare (peerPut (some owner.slot))
    (ExactBoundary cs (owner::loans)) (fun _ => ExactBoundary cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  rintro w a result v b ⟨holders,account⟩ run
  cases result
  exact ⟨holders,account.payment run⟩

def setup (pid : PeerId) (interval : Nat) (running : Bool) : WG.M Bool := do
  let p ← getPeer pid
  let send ← WG.andM (branch .peerKeepaliveWasZero (p.persistentKeepaliveInterval == 0))
    (WG.andM (branch .peerKeepaliveNonzero (interval != 0))
      (branch .peerKeepaliveRunning running))
  setPeer pid {p with persistentKeepaliveInterval := interval}
  pure send

theorem setup_boundary (pid : PeerId) (interval : Nat) (running : Bool) :
    Preserves (ExactBoundary cs loans) (setup pid interval running) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  unfold setup at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,read,ar,getter,run⟩ := run
  obtain ⟨same,time,d,hd,hp⟩ := getPeer_normal pid w read p a ar getter
  subst read
  subst ar
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨send,guarded,ag,guard,run⟩ := run
  have ambient : Preserves (· = w) (WG.andM
      (branch .peerKeepaliveWasZero (p.persistentKeepaliveInterval == 0))
      (WG.andM (branch .peerKeepaliveNonzero (interval != 0))
        (branch .peerKeepaliveRunning running))) := by
    unfold WG.andM
    simp only [branch]
    repeat' first
      | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
      | rx_retention_step
  have same := (hoare_iff_run_ambient _ _ _).mp ambient w a send guarded ag rfl guard
  subst guarded
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨value,after,aa,write,done⟩ := run
  have kept := TimerFrames.source_modify
    hi hd hp (fun p => {p with persistentKeepaliveInterval:=interval})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ h => h) (fun _ => rfl) ag aa write
  cases done
  exact kept

theorem out (a : PeerAttrs) (o : Owner) (ret : Int) :
    Hoare (do peerPut (some o.slot); _ ← branch .peerZeroPsk a.presharedKey.isSome; pure ret)
      (ExactBoundary cs (o::loans)) (fun _ => ExactBoundary cs loans) := by
  apply hoare_bind _ _ (pay o)
  intro _
  exact preserves_bind (hoare_liftAmbient (AmbientM.branch .peerZeroPsk a.presharedKey.isSome) _)
    (fun _ => preserves_pure ret)

theorem finish_factor (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    Configuration.peerTailFinishSource a peer pid ret = (do
      let running := (← getDev).running
      if ← branch .peerHasKeepalive a.keepalive.isSome then
        if ← branch .peerSendKeepalive (← setup pid (a.keepalive.getD 0) running) then
          sendKeepalive pid
      if ← branch .peerRunning running then sendStagedPackets pid
      peerPut peer
      _ ← branch .peerZeroPsk a.presharedKey.isSome
      pure ret) := by
  simp only [Configuration.peerTailFinishSource,setup,bind_assoc,pure_bind]

/-- Successful staging and keepalive work stays charged before the acquired
caller reference is paid. No running/readiness or successful-send premise. -/
theorem finish (a : PeerAttrs) (o : Owner) (ret : Int) :
    Hoare (Configuration.peerTailFinishSource a (some o.slot) o.slot ret)
      (ExactBoundary cs (o::loans)) (fun _ => ExactBoundary cs loans) := by
  rw [finish_factor]
  apply hoare_bind _ _ (ExactBoundary.native_fields (HolderEncrypt.store_fields getDev_sameWGStore))
  intro d
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .peerHasKeepalive a.keepalive.isSome) _)
  intro keep
  have tail : Hoare (do
      if ← branch .peerRunning d.running then sendStagedPackets o.slot
      peerPut (some o.slot)
      _ ← branch .peerZeroPsk a.presharedKey.isSome
      pure ret) (ExactBoundary cs (o::loans)) (fun _ => ExactBoundary cs loans) := by
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .peerRunning d.running) _)
    intro running
    cases running with
    | false => exact out a o ret
    | true => exact hoare_bind _ _ (ExactBoundary.staged o.slot) (fun _ => out a o ret)
  cases keep with
  | false => exact tail
  | true =>
    apply hoare_bind _ _ (setup_boundary o.slot (a.keepalive.getD 0) d.running)
    intro send
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .peerSendKeepalive send) _)
    intro sendKeep
    cases sendKeep with
    | false => exact tail
    | true => exact hoare_bind _ _ (TimerCallbacks.keepalive_boundary o.slot) (fun _ => tail)

def LoopState (cs : Ledger) (o : Owner) (loans : Reservations)
    (acc : Option Int × Int) (w : WGWorld) : Prop :=
  match acc.1 with
  | none => ExactBoundary cs (o::loans) w
  | some _ => ExactBoundary cs loans w

def StepState (cs : Ledger) (o : Owner) (loans : Reservations)
    (step : ForInStep (Option Int × Int)) (w : WGWorld) : Prop :=
  match step with
  | .done acc => LoopState cs o loans acc w
  | .yield acc => acc.1=none ∧ ExactBoundary cs (o::loans) w

private theorem pure_post {P : WGWorld → Prop} {Q : α → WGWorld → Prop}
    (value : α) (post : ∀ w, P w → Q value w) : Hoare (pure value : WG.M α) P Q :=
  hoare_consequence (hoare_pure value P) (fun _ h => h)
    (fun _ w h => by rcases h with ⟨rfl,h⟩; exact post w h)

/-- The early-return accumulator records whether the actual out path has
already paid the caller's loan. Only a yielding step can enter another iteration. -/
theorem forIn_early (xs : List α) (ret : Int)
    (g : α → (Option Int × Int) → WG.M (ForInStep (Option Int × Int)))
    (step : ∀ x ∈ xs, ∀ ret, Hoare (g x (none,ret))
      (ExactBoundary cs (o::loans)) (StepState cs o loans)) :
    Hoare (forIn xs (none,ret) g) (ExactBoundary cs (o::loans)) (LoopState cs o loans) := by
  induction xs generalizing ret with
  | nil =>
    rw [List.forIn_nil]
    exact pure_post _ (fun _ h => h)
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply hoare_bind _ _ (step x (by simp) ret)
    intro result
    cases result with
    | done acc => exact pure_post _ (fun _ h => h)
    | yield acc =>
      rcases acc with ⟨early,ret⟩
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w a result v b hi run
      have eq : early=none := hi.1
      subst early
      exact (hoare_iff_run_ambient _ _ _).mp
        (ih ret (fun y hy => step y (by simp [hy]))) w a result v b hi.2 run

/-- Both malformed entries and negative original insertion returns take the
source cleanup exactly once; exhausting the loop passes the still-charged loan. -/
theorem allowedIps (a : PeerAttrs) (o : Owner) (next : Int → WG.M Int)
    (keeps : ∀ ret, Hoare (next ret) (ExactBoundary cs (o::loans)) (fun _ => ExactBoundary cs loans)) :
    Hoare (Configuration.peerAllowedIpsSource a (some o.slot) o.slot next)
      (ExactBoundary cs (o::loans)) (fun _ => ExactBoundary cs loans) := by
  have record (d : Decision) (value : Bool) :
      Preserves (ExactBoundary cs (o::loans)) (branch d value : WG.M Bool) :=
    hoare_liftAmbient (AmbientM.branch d value) _
  unfold Configuration.peerAllowedIpsSource Configuration.peerAllowedIpsWith
  apply hoare_bind _ _ (record _ _)
  intro has
  split
  · dsimp only
    change Hoare (_ >>= _) (ExactBoundary cs (o::loans)) _
    refine hoare_bind _ _ (forIn_early _ _ _ ?_) ?_
    · intro entry _ ret
      dsimp only
      apply hoare_bind _ _ (record _ _)
      intro _
      cases entry with
      | malformed =>
        apply hoare_bind _ _ (record _ _)
        intro _
        apply hoare_bind _ _ (out a o (-EINVAL))
        intro result
        exact pure_post _ (fun _ h => h)
      | attrs ip =>
        apply hoare_bind _ _ (record _ _)
        intro _
        apply hoare_bind _ _ (AllowedIps.setAllowedip_boundary o.slot ip)
        intro result
        apply hoare_bind _ _ (record _ _)
        intro bad
        split
        · apply hoare_bind _ _ (out a o result)
          intro result'
          exact pure_post _ (fun _ h => h)
        · exact pure_post _ (fun _ h => ⟨rfl,h⟩)
    · intro acc
      rcases acc with ⟨early,ret⟩
      cases early with
      | some result => exact pure_post _ (fun _ h => h)
      | none =>
        apply hoare_bind _ _ (record _ _)
        intro _
        exact keeps ret
  · exact keeps 0

/-- Complete original acquired-peer configuration tail. Every normal return
pays its caller loan, while all newly queued work remains in the funded account. -/
theorem tail (a : PeerAttrs) (o : Owner) :
    Hoare (Configuration.peerConfigTailSource a (some o.slot) o.slot)
      (ExactBoundary cs (o::loans)) (fun _ => ExactBoundary cs loans) := by
  rw [Configuration.peerConfigTailSource_factor]
  exact allowedIps a o _ (finish a o)

end ConfigurationTail
end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
