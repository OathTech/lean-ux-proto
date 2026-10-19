import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseBirthFrames

/-! Preparation distinguishes queue reuse, allocation refusal and the silent
singleton insertion before its existing birth receipt. The pending phase
names the original invocation and its literal hidden-choice prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier Staging.Points StagingInterior
set_option maxHeartbeats 600000
attribute [local implicit_reducible] Native.action RetirementSecurity.OccurrenceHandshake.keepalivePrepare

inductive PreparationPhase (history : List Event) (ledger : Ledger)
    (debts : List AllocatedObligation.CleanupDebt) (locals : List RetirementSecurity.TxLocalBatch)
    (pid : PeerId) (w : WGWorld) (a : Ambient) : List Event → WGWorld → Ambient → Prop where
  | idle (before : Accounted history ledger debts locals w) :
      PreparationPhase history ledger debts locals pid w a history w b
  | pending (before : Accounted history ledger debts locals w)
      (device : w.dev=some d) (resident : d.peers[pid]?=some peer) (empty : peer.staged.isEmpty=true)
      (allocated : keepaliveAllocation.run (clock a .keepaliveStagedEmpty true)=.ok (false,b)) :
      PreparationPhase history ledger debts locals pid w a history
        (queueWorld pid peer (peer.staged++[{mtu:=d.mtu}]) d w) b
  | recorded (ready : Bool) (after : Ledger)
      (native : ((RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid).run w).run a=.ok ((ready,v),b))
      (account : Accounted (history++[keepaliveEvent pid ready w v a b]) after debts locals v)
      (change : KeepaliveChange history ledger pid ⟨ready,w,v,a,b⟩ after) :
      PreparationPhase history ledger debts locals pid w a
        (history++[keepaliveEvent pid ready w v a b]) v b

theorem preparation_covers (before : Accounted h ledger debts locals w) (pid : PeerId) (a : Ambient) :
    Covers (PreparationPhase h ledger debts locals pid w a) (preparationShape pid) w a h := by
  unfold preparationShape
  change Covers _ (.receipt _ _) w a h
  constructor
  · erw [covers_mpr (by simp only [RetirementSecurity.OccurrenceHandshake.keepalivePrepare,lift_bind]; rfl)]
    have read : Covers (PreparationPhase h ledger debts locals pid w a) (.native (.peer pid)) w a h := by
      refine ⟨.idle before,?_⟩
      intro peer u b middle run
      obtain ⟨rfl,rfl,rfl,_⟩:=peer_success run
      exact .idle before
    apply covers_bind read
    intro peer u b middle readRun
    obtain ⟨worldEq,clockEq,historyEq,d,device,resident⟩:=peer_success readRun
    subst u
    subst b
    subst middle
    have guard : Covers (PreparationPhase h ledger debts locals pid w a)
        (.native (.branch .keepaliveStagedEmpty peer.staged.isEmpty)) w a h := by
      refine ⟨.idle before,?_⟩
      intro value u b middle run
      obtain ⟨_,rfl,_,rfl⟩:=branch_success run
      exact .idle before
    apply covers_bind guard
    intro empty u b middle tested
    cases empty <;> dsimp only
    · exact guard.normal tested
    · obtain ⟨isEmpty,worldEq,clockEq,historyEq⟩:=branch_success tested
      subst u
      subst b
      subst middle
      have empty : peer.staged.isEmpty=true:=isEmpty.symm
      rw [empty]
      have allocation : Covers (PreparationPhase h ledger debts locals pid w a) (.native .allocation)
          w (clock a .keepaliveStagedEmpty true) h := by
        refine ⟨.idle before,?_⟩
        intro value u b middle run
        obtain ⟨rfl,rfl,_⟩:=ambient_success run
        exact .idle before
      repeat' erw [covers_mpr (by first | rfl | (simp only [lift_bind] <;> rfl))]
      apply covers_bind allocation
      intro allocated u b middle chosen
      obtain ⟨worldEq,historyEq,choiceRun⟩:=ambient_success chosen
      subst u
      subst middle
      have refusal : Covers (PreparationPhase h ledger debts locals pid w a)
          (.native (.branch .keepaliveNoMem (!allocated))) w b h := by
        refine ⟨.idle before,?_⟩
        intro value u c middle run
        obtain ⟨_,rfl,_,rfl⟩:=branch_success run
        exact .idle before
      apply covers_bind refusal
      intro refused u c middle refusedRun
      cases refused <;> dsimp only
      · obtain ⟨worldEq,historyEq,refusalRun⟩:=ambient_success refusedRun
        subst u
        subst middle
        have allocationRun:=allocation_choice choiceRun refusalRun
        have readDev : Covers (PreparationPhase h ledger debts locals pid w a) (.native .device) w c h := by
          refine ⟨.idle before,?_⟩
          intro found u b middle run
          obtain ⟨rfl,rfl,rfl,_⟩:=device_success run
          exact .idle before
        repeat' erw [covers_mpr (by first | rfl | (simp only [lift_bind] <;> rfl))]
        apply covers_bind readDev
        intro found u e middle foundRun
        obtain ⟨worldEq,clockEq,historyEq,foundEq⟩:=device_success foundRun
        subst u
        subst e
        subst middle
        have eqDevice : found=d:=Option.some.inj (foundEq.symm.trans device)
        subst found
        have written : Covers (PreparationPhase h ledger debts locals pid w a)
            (.native (.setPeer pid {peer with staged:=peer.staged++[{mtu:=d.mtu}]})) w c h := by
          refine ⟨.idle before,?_⟩
          intro value v f last run
          obtain ⟨native,rfl⟩:=lift_success run
          have actual:=keepalive_write (pid:=pid) (p:=peer) (a:=c) device
          change ((WG.setPeer pid {peer with staged:=peer.staged++[{mtu:=d.mtu}]}).run w).run c=_ at actual
          erw [actual] at native
          cases native
          exact .pending before device resident empty allocationRun
        exact covers_bind written (fun _ _ _ _ run=>written.normal run)
      · exact refusal.normal refusedRun
  · intro ready v b middle performed
    obtain ⟨native,sameHistory⟩:=lift_success performed
    subst middle
    have recorded:=StagingInterior.keepalive_recorded (h:=h) native
    obtain ⟨_,_,after,account,change⟩:=CompleteKeepalive.normal pid before a b v _ ready recorded
    exact .recorded ready after native account change

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
