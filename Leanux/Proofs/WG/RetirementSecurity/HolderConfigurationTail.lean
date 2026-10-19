import Leanux.Proofs.WG.RetirementSecurity.HolderConfigurationFrames

/-! Ordinary native configuration retains the acquired peer until its one
source cleanup, including early allowed-IP errors and keepalive/TX staging.
The early-return accumulator records whether that payment has occurred. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderConfiguration
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open HolderKeepalive
variable {selected : PeerId}

theorem setup (pid : PeerId) (interval : Nat) (running : Bool) :
    Preserves (Selected temporary selected) (HolderConfigTail.setup pid interval running) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  unfold HolderConfigTail.setup at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,read,c,getter,run⟩ := run
  obtain ⟨same,time,d,device,resident⟩ := getPeer_normal pid w read p a c getter
  subst read
  subst c
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨send,guarded,e,guard,run⟩ := run
  have ambient : Preserves (·=w) (WG.andM
      (branch .peerKeepaliveWasZero (p.persistentKeepaliveInterval == 0))
      (WG.andM (branch .peerKeepaliveNonzero (interval != 0))
        (branch .peerKeepaliveRunning running))) := by
    unfold WG.andM
    simp only [branch]
    repeat' first
      | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
      | rx_retention_step
  have same := (hoare_iff_run_ambient _ _ _).mp ambient w a send guarded e rfl guard
  subst guarded
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ignored,written,f,write,done⟩ := run
  have pair : ((getPeer pid >>= fun q => setPeer pid {q with persistentKeepaliveInterval:=interval}).run w).run e =
      .ok ((ignored,written),f) := by
    rw [MaterialOrigin.bind_ok_ambient]
    exact ⟨p,w,e,by simp [getPeer,getDev,device,resident],write⟩
  have kept := (hoare_iff_run_ambient _ _ _).mp
    (update_selected pid (fun q => {q with persistentKeepaliveInterval:=interval})
      (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)) w e ignored written f before pair
  cases done
  exact kept

theorem out (attrs : PeerAttrs) (pid : PeerId) (ret : Int) :
    Hoare (do peerPut (some pid); _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
      (Selected temporary pid) (fun _ => HolderAccount temporary) := by
  apply hoare_bind _ _ (hoare_consequence (HolderConsume.payment pid)
    (fun _ before => ⟨before.1.1,before.2⟩) (fun _ _ h=>h))
  intro _
  exact preserves_bind (hoare_liftAmbient (AmbientM.branch .peerZeroPsk attrs.presharedKey.isSome) _)
    (fun _=>preserves_pure ret)

theorem finish (attrs : PeerAttrs) (pid : PeerId) (ret : Int) :
    Hoare (Configuration.peerTailFinishSource attrs (some pid) pid ret)
      (Selected temporary pid) (fun _=>HolderAccount temporary) := by
  rw [HolderConfigTail.finish_factor]
  apply hoare_bind _ _ (store getDev_sameWGStore)
  intro d
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .peerHasKeepalive attrs.keepalive.isSome) _)
  intro keep
  have tail : Hoare (do
      if ← branch .peerRunning d.running then sendStagedPackets pid
      peerPut (some pid)
      _ ← branch .peerZeroPsk attrs.presharedKey.isSome
      pure ret) (Selected temporary pid) (fun _=>HolderAccount temporary) := by
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .peerRunning d.running) _)
    intro running
    cases running with
    | false => exact out attrs pid ret
    | true => exact hoare_bind _ _ (staged_selected pid) (fun _=>out attrs pid ret)
  cases keep with
  | false => exact tail
  | true =>
    apply hoare_bind _ _ (setup pid (attrs.keepalive.getD 0) d.running)
    intro send
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .peerSendKeepalive send) _)
    intro sendKeep
    cases sendKeep with
    | false => exact tail
    | true => exact hoare_bind _ _ (keepalive_selected pid) (fun _=>tail)

def LoopState (temporary : Credits.Ledger) (pid : PeerId) (acc : Option Int × Int) (w : WGWorld) : Prop :=
  match acc.1 with
  | none => Selected temporary pid w
  | some _ => HolderAccount temporary w

def StepState (temporary : Credits.Ledger) (pid : PeerId) (step : ForInStep (Option Int × Int)) (w : WGWorld) : Prop :=
  match step with
  | .done acc => LoopState temporary pid acc w
  | .yield acc => acc.1=none ∧ Selected temporary pid w

private theorem pure_post {P : WGWorld → Prop} {Q : α → WGWorld → Prop}
    (value : α) (post : ∀w,P w → Q value w) : Hoare (pure value : WG.M α) P Q :=
  hoare_consequence (hoare_pure value P) (fun _ h=>h)
    (fun _ w h=>by rcases h with ⟨rfl,h⟩; exact post w h)

theorem forIn_early (xs : List α) (ret : Int)
    (g : α → (Option Int × Int) → WG.M (ForInStep (Option Int × Int)))
    (step : ∀x ∈ xs,∀ret,Hoare (g x (none,ret))
      (Selected temporary pid) (StepState temporary pid)) :
    Hoare (forIn xs (none,ret) g) (Selected temporary pid) (LoopState temporary pid) := by
  induction xs generalizing ret with
  | nil => rw [List.forIn_nil]; exact pure_post _ (fun _ h=>h)
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply hoare_bind _ _ (step x (by simp) ret)
    intro result
    cases result with
    | done acc => exact pure_post _ (fun _ h=>h)
    | yield acc =>
      rcases acc with ⟨early,ret⟩
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w a result v b hi run
      have eq : early=none := hi.1
      subst early
      exact (hoare_iff_run_ambient _ _ _).mp
        (ih ret (fun y hy=>step y (by simp [hy]))) w a result v b hi.2 run

theorem allowedIps (attrs : PeerAttrs) (pid : PeerId) (next : Int → WG.M Int)
    (keeps : ∀ret,Hoare (next ret) (Selected temporary pid) (fun _=>HolderAccount temporary)) :
    Hoare (Configuration.peerAllowedIpsSource attrs (some pid) pid next)
      (Selected temporary pid) (fun _=>HolderAccount temporary) := by
  have record (d : Decision) (value : Bool) :
      Preserves (Selected temporary pid) (branch d value : WG.M Bool) :=
    hoare_liftAmbient (AmbientM.branch d value) _
  unfold Configuration.peerAllowedIpsSource Configuration.peerAllowedIpsWith
  apply hoare_bind _ _ (record _ _)
  intro has
  split
  · dsimp only
    change Hoare (_ >>= _) (Selected temporary pid) _
    refine hoare_bind _ _ (forIn_early _ _ _ ?_) ?_
    · intro entry _ ret
      dsimp only
      apply hoare_bind _ _ (record _ _)
      intro _
      cases entry with
      | malformed =>
        apply hoare_bind _ _ (record _ _)
        intro _
        apply hoare_bind _ _ (out attrs pid (-EINVAL))
        intro result
        exact pure_post _ (fun _ h=>h)
      | attrs ip =>
        apply hoare_bind _ _ (record _ _)
        intro _
        apply hoare_bind _ _ (allowedip pid ip)
        intro result
        apply hoare_bind _ _ (record _ _)
        intro bad
        split
        · apply hoare_bind _ _ (out attrs pid result)
          intro result'
          exact pure_post _ (fun _ h=>h)
        · exact pure_post _ (fun _ h=>⟨rfl,h⟩)
    · intro acc
      rcases acc with ⟨early,ret⟩
      cases early with
      | some result => exact pure_post _ (fun _ h=>h)
      | none =>
        apply hoare_bind _ _ (record _ _)
        intro _
        exact keeps ret
  · exact keeps 0

theorem tail (attrs : PeerAttrs) (pid : PeerId) :
    Hoare (Configuration.peerConfigTailSource attrs (some pid) pid)
      (Selected temporary pid) (fun _=>HolderAccount temporary) := by
  rw [Configuration.peerConfigTailSource_factor]
  exact allowedIps attrs pid _ (finish attrs pid)

end Leanux.Proofs.WG.RetirementSecurity.HolderConfiguration
