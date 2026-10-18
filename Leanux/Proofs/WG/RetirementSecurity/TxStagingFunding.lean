import Leanux.Proofs.WG.RetirementSecurity.TxStagingFundingLoop
import Leanux.Proofs.WG.RetirementSecurity.TxStagedHolders
import Leanux.Proofs.WG.RetirementSecurity.TxAcquireHolders

/-! Native staged send acquires the actual current-slot reference and
discharges it on every normal path: no-key/rejection repayment, or transfer
into the actual queued batch followed by original refusal/disposal behavior.
Current-slot affiliation remains a separately named incoming invariant. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

namespace StagingFunding

theorem key_source_factor (pid kid : Nat) (packets : List WG.Packet) :
    stagedKeySource pid kid packets = (do
      let k ← getKeypair kid
      if ← branch .stagedKeyInvalid !k.sending.isValid then
        return ← stagedOutNokey pid packets (some kid) false
      if ← branchExpired .stagedBirthdateExpired k.sending.birthdate REJECT_AFTER_TIME then
        return ← stagedOutNokey pid packets (some kid) true
      let state ← forIn packets (none,[]) (body pid kid packets)
      match state.1 with
      | some stopped => pure stopped
      | none => do
        _ ← branch .stagedNonceIterate false
        stagedSubmit pid kid state.2) := by
  unfold stagedKeySource body reserveSource
  simp only [bind_assoc,pure_bind]
  apply bind_congr_source
  intro k
  apply bind_congr_source
  intro invalid
  split
  · rfl
  · apply bind_congr_source
    intro expired
    split
    · rfl
    · congr 1
      funext state
      obtain ⟨flag,accumulated⟩ := state
      cases flag <;> rfl

theorem submit_funding (before : Borrowed allocation pid temporary w)
    (keys : ∀ packet ∈ packets, packet.keypair = allocation.slot) (a b : Ambient)
    (run : ((stagedSubmit pid allocation.slot packets).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := by
  cases packets with
  | nil =>
    simp only [stagedSubmit,List.mapM_nil,pure_bind,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨_,u,c,_,tail⟩ := run
    cases tail
  | cons packet rest =>
    exact before.1.staged_submit before.2.1 before.2.2 packet rest
      (keys packet (by simp)) a b run

theorem key_source_funding (before : Borrowed allocation pid temporary w)
    (packets : List WG.Packet) (a b : Ambient)
    (run : ((stagedKeySource pid allocation.slot packets).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := by
  rw [key_source_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨k,u,c,readRun,tail⟩ := run
  obtain ⟨same,clock,_,_,_⟩ := KeyTimes.getKeypair_return allocation.slot w u k a c readRun
  subst u
  subst c
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨invalid,u,c,branchRun,tail⟩ := tail
  have same : u = w := by cases branchRun; rfl
  subst u
  cases invalid with
  | true =>
    simp only [ite_true] at tail
    exact HolderAccount.no_key (some allocation) before.1 pid packets false c b tail
  | false =>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨expired,u,e,expiryRun,tail⟩ := tail
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp
      (branchExpired_sameWGWorld .stagedBirthdateExpired k.sending.birthdate REJECT_AFTER_TIME)
      w c expired u e expiryRun
    change u = w at same
    subst u
    cases expired with
    | true =>
      simp only [ite_true] at tail
      exact HolderAccount.no_key (some allocation) before.1 pid packets true e b tail
    | false =>
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨state,u,f,loopRun,tail⟩ := tail
      have funded := loop_funding packets before (by simp) packets e f loopRun
      obtain ⟨flag,accumulated⟩ := state
      cases flag with
      | some stopped => cases tail; exact funded
      | none =>
        rw [MaterialOrigin.bind_ok_ambient] at tail
        obtain ⟨_,t,g,branchRun,submitRun⟩ := tail
        have same : t = u := by cases branchRun; rfl
        subst t
        exact submit_funding funded.1 funded.2 g b submitRun

end StagingFunding

/-- Full native staging consumes its one acquired key reference by exactly
the original rejection or publication path. Packet boundedness and current
key affiliation are visible independent inputs, not consequences of credit. -/
theorem HolderAccount.staged (account : HolderAccount temporary w)
    (bounded : Packets.Inv w) (compatible : CurrentCompatible pid w) (a b : Ambient)
    (run : ((sendStagedPackets pid).run w).run a = .ok (((),v),b)) : HolderAccount temporary v := by
  rw [← stagedFullSource_eq] at run
  simp only [stagedFullSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,readRun,empty,t,e,branchRun,tail⟩ := run
  obtain ⟨same,clock,d,device,stored⟩ := Origins.getPeer_return pid w u p a c readRun
  subst u
  subst c
  have pending := (hoare_iff_run_ambient _ _ _).mp (select_getPeer w pid)
    w a p w a ⟨Transfer.refl w,compatible⟩ readRun
  have same : t = w := by cases branchRun; rfl
  subst t
  cases empty with
  | true => simp only [ite_true] at tail; cases tail; exact account
  | false =>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,u,c,setRun,kp,t,f,getRun,missing,s,g,branchRun,tail⟩ := tail
    have after : u = replacePeer w d pid {p with staged := []} := by
      have equal : replacePeer w d pid {p with staged := []} = u ∧ e = c := by
        simpa [setPeer,modifyDev,replacePeer,device] using setRun
      exact equal.1.symm
    have selected := (hoare_iff_run_ambient _ _ _).mp (select_setPeer w pid p)
      w e () u c pending setRun
    have affiliation := (hoare_iff_run_ambient _ _ _).mp (select_keyGet w pid p.keypairCurrent)
      u c kp t f selected getRun
    have acquiredAccount : HolderAccount temporary u := account.points
      (after ▸ ownershipPoint_replace device stored rfl)
    have resident : peerAt u pid = some {p with staged := []} := by simp [peerAt,after,replacePeer]
    obtain ⟨saved,_,named,acquired⟩ := acquiredAccount.current_get resident c f getRun
    have boundU : Packets.Inv u := by
      simpa [Packets.Inv,Packets.snapshot,Packets.deviceStore,after,replacePeer,device] using bounded
    have shape := (ProjectedAction.iff_run_ambient _ _ _).mp
      (StagingOccurrences.key_get_geometry p.keypairCurrent) u c kp t f getRun
    have boundT : Packets.Inv t := by
      unfold Packets.Inv
      rw [show Packets.snapshot t = Packets.snapshot u from congrArg Prod.fst shape]
      exact boundU
    have same : s = t := by cases branchRun; rfl
    subst s
    cases missing with
    | true =>
      simp only [ite_true] at tail
      rw [← named] at tail
      exact HolderAccount.no_key saved acquired pid p.staged false g b tail
    | false =>
      simp only [Bool.false_eq_true,ite_false] at tail
      cases kp with
      | none => cases tail
      | some kid =>
        cases saved with
        | none => cases named
        | some allocation =>
          have key : allocation.slot = kid := Option.some.inj named
          subst kid
          exact StagingFunding.key_source_funding ⟨acquired,boundT,affiliation.2 allocation.slot rfl⟩
            p.staged g b tail

end Leanux.Proofs.WG.RetirementSecurity
