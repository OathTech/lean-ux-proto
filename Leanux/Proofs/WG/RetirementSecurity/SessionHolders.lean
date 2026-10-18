import Leanux.Proofs.WG.RetirementSecurity.SessionPerimeter

/-! Complete original session preservation of the concrete holder account,
including allocation failure and source rejection. R2 allocation safety is
kept as a named incoming premise; deriving both invariants for every initialized
caller remains outside this local source-group theorem. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem HolderAccount.session (account : HolderAccount temporary w)
    (allocation : AllocationInv history w) (pid : PeerId) (a b : Ambient)
    (run : ((beginSession pid).run w).run a = .ok ((result,v),b)) :
    HolderAccount temporary v := by
  have source := run
  rw [SessionOrigin.factor,MaterialOrigin.bind_ok_ambient] at source
  obtain ⟨context,middle,middleAmbient,frontRun,_⟩ := source
  rw [SessionOrigin.front,SessionOrigin.frontWith,MaterialOrigin.bind_ok_ambient] at frontRun
  obtain ⟨p,u,c,readRun,_⟩ := frontRun
  obtain ⟨_,_,d,device,peer⟩ := Origins.getPeer_return pid w u p a c readRun
  have found : peerAt w pid = some p := by simp [peerAt,device,peer]
  obtain ⟨entry⟩ := account.split_peer found
  obtain ⟨parts⟩ := peer_parts entry.named
  let remaining := (parts.tx ++ parts.rx).map (·.allocation) ++
    (entry.rest.flatten.map (·.allocation) ++ temporary)
  have funded : PeerAccount pid p (parts.slots.credits ++ remaining) w :=
    ⟨found,by simpa only [parts.credits,List.append_assoc] using entry.credits⟩
  cases result with
  | false =>
    have same := (session_refused_account pid p parts.slots remaining w v a b
      parts.aligned funded allocation run).1
    exact same ▸ account
  | true =>
    obtain ⟨ctx,created,createdAmbient,k,_,_,_,completed⟩ :=
      session_account pid p parts.slots remaining w v a b parts.aligned funded allocation run
    have perimeter := (ProjectedAction.iff_run_ambient _ _ _).mp
      (session_perimeter pid) w a true v b run
    apply entry.finish_slots parts (rotatedPeer (zeroedPeer p) ctx.slot k.iAmTheInitiator)
      (parts.slots.rotate ⟨ctx.slot,w.keypairCounter + 1⟩ k.iAmTheInitiator p.keypairNext.isSome)
      completed.1
      (SlotLoans.rotate_aligned (p := zeroedPeer p) parts.aligned
        ⟨ctx.slot,w.keypairCounter + 1⟩ k.iAmTheInitiator)
      ?_ ?_ perimeter completed.2
    all_goals cases k.iAmTheInitiator <;> cases h : p.keypairNext.isSome <;>
      simp [rotatedPeer,zeroedPeer,h]

end Leanux.Proofs.WG.RetirementSecurity
