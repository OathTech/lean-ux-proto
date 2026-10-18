import Leanux.Proofs.WG.Index.PollCoreNativeSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.PollCore
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem native_absent {α : Type} (pid : PeerId) (action : WG.M α)
    (tags : ∀entry, Preserves (DriverTags.Silent.Retained entry) action) :
    Preserves (Absent pid) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  exact absent_retained ((hoare_iff_run_ambient _ _ _).mp (tags (responseTagMap w.dev))
    w a result v b (TagsRetained.refl _) run) pre

theorem native_loop {α : Type} (pid : PeerId) (action : WG.M α)
    (ready : Preserves TimerCore.Ready action)
    (tags : ∀entry, Preserves (DriverTags.Silent.Retained entry) action) :
    Preserves (Loop pid) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  rcases pre with pre|pre
  · exact Or.inl ((hoare_iff_run_ambient _ _ _).mp ready w a result v b pre run)
  · exact Or.inr ((hoare_iff_run_ambient _ _ _).mp (native_absent pid action tags) w a result v b pre run)

theorem keypair_ready (key : Option KeypairId) (now : Bool) :
    Preserves TimerCore.Ready (keypairPut key now) :=
  ReceiveCompletion.ready_join _ (CurrentSlots.keypairPut_preserves key now)
    (CryptCore.key_release_core key now)

theorem peer_loop (pid : PeerId) : Preserves (Loop pid) (peerPut (some pid)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  cases result
  rcases pre with pre|absent
  · cases device:w.dev with
    | none=>
      simp [peerPut,requireNotPending,branch,AmbientM.branch,getPeer,getDev,device,invariant,AmbientM.invariant] at run
      cases run
    | some d=>
      cases resident:d.peers[pid]? with
      | none=>
        simp [peerPut,requireNotPending,branch,AmbientM.branch,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
        cases run
      | some p=>
        have positive := (RxCredits.peerPut_effect pid w v d p a b device resident run).1
        have effect := peerPut_normal_device pid d p resident positive w v a b () device run
        by_cases last:p.refcount=1
        · right
          simp [Absent,effect,responseTagMap,releasedPeer_peer,last]
        · left
          refine ⟨(hoare_iff_run_ambient _ _ _).mp (CurrentSlots.peerPut_preserves (some pid))
            w a () v b pre.1 run,?_⟩
          have tables := (ensures_iff _ _ _).mpr (peerPut_tables (some pid)) w a () v b
            (fun d hd=>(pre.2 d hd).1) run
          intro f present
          rw [effect] at present
          cases present
          exact ⟨tables _ effect,
            nonlastPeerRelease_hashSlotCoverage d pid p resident last (pre.2 d device).2.1,
            nonlastPeerRelease_coherent d pid p resident (by omega) (pre.2 d device).2.2.1,
            releasedPeer_deadHashedReserved [] d pid p resident (pre.2 d device).2.2.2⟩
  · right
    exact (hoare_iff_run_ambient _ _ _).mp
      (native_absent pid _ (fun entry=>DriverTags.Silent.peerPut entry (some pid))) w a () v b absent run

theorem complete_exit (pid : PeerId) :
    Hoare (completeRxQueue pid) (Loop pid) (fun _=>TimerCore.Ready) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  rcases pre with pre|absent
  · exact (hoare_iff_run_ambient _ _ _).mp (complete_ready pid) w a result v b pre run
  · change (((getPeer pid >>= fun p=>setPeer pid {p with napiScheduled:=false}).run w).run a)=_ at run
    rw [MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨p,u,c,read,_⟩ := run
    obtain ⟨_,_,d,device,resident⟩ := getPeer_normal pid w u p a c read
    simp [Absent,responseTagMap,device,resident] at absent

end Leanux.Proofs.WG.Index.PollCore
