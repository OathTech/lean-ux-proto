import Leanux.Proofs.WG.TransmitSecurity.BatchNativeKeySource

/-! Full native staging derives homogeneous queue admission from its concrete
nonce loop. It carries the original empty, no-key, age and nonce refusal arms. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits
set_option pp.structureInstances false

theorem replace_peer (before : Inv w) (device : w.dev = some d)
    (found : d.peers[pid]? = some p) (same : q.txQueue.all = p.txQueue.all) :
    Inv (replacePeer w d pid q) := by
  apply before.frame
  dsimp only [view]
  apply Prod.ext
  · funext other
    by_cases equal : pid = other
    · subst other
      simp [handoffTxView,replacePeer,device,found,same]
    · simp [handoffTxView,replacePeer,device,Std.TreeMap.getElem?_insert,equal]
  · funext id
    simp [PacketMaterial.view,TxDisposition.txPackets,replacePeer,device]

theorem send (before : Ready locals w) (pid : PeerId) (a b : Ambient)
    (run : ((sendStagedPackets pid).run w).run a = .ok (((),v),b)) : Inv v := by
  rw [← stagedFullSource_eq] at run
  simp only [stagedFullSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,readRun,empty,t,e,branchRun,tail⟩ := run
  obtain ⟨same,clock,d,device,stored⟩ := Origins.getPeer_return pid w u p a c readRun
  subst u
  subst c
  have same : t = w := by cases branchRun; rfl
  subst t
  cases empty with
  | true => simp only [ite_true] at tail; cases tail; exact before.2
  | false =>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,u,c,setRun,kp,t,f,getRun,missing,s,g,branchRun,tail⟩ := tail
    have after : u = replacePeer w d pid {p with staged := []} := by
      have equal : replacePeer w d pid {p with staged := []} = u ∧ e = c := by
        simpa [setPeer,modifyDev,replacePeer,device] using setRun
      exact equal.1.symm
    have hu : Ready locals u := by
      rw [after]
      exact ⟨⟨by simpa [Packets.Inv,Packets.snapshot,Packets.deviceStore,replacePeer,device] using before.1.1,
        before.1.2.exchange device stored _ (List.Perm.refl _)⟩,
        replace_peer before.2 device stored rfl⟩
    have ht := (hoare_iff_run_ambient _ _ _).mp (ready_key_get (locals := locals) p.keypairCurrent)
      u c kp t f hu getRun
    have same : s = t := by cases branchRun; rfl
    subst s
    cases missing with
    | true =>
      simp only [ite_true] at tail
      exact ((hoare_iff_run_ambient _ _ _).mp (ready_no_key pid p.staged kp false)
        t g () v b ht tail).2
    | false =>
      simp only [Bool.false_eq_true,ite_false] at tail
      cases kp with
      | none => cases tail
      | some kid =>
        exact (hoare_iff_run_ambient _ _ _).mp (key_source locals pid kid p.staged)
          t g () v b ht tail

abbrev Coherent (locals : List TxLocalBatch) (active : List (List SkbId)) (w : WGWorld) : Prop :=
  OccurrenceStack.Ready locals active w ∧ Inv w

theorem send_coherent (pid : PeerId) : Preserves (Coherent locals active) (sendStagedPackets pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (OccurrenceConfiguration.staged pid) w a () v b before.1 run,
    send ⟨⟨before.1.1.bounded,before.1.2.1⟩,before.2⟩ pid a b run⟩

end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
