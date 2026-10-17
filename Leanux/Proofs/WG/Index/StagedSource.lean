import Leanux.Proofs.WG.Index.StagedFrames
import Leanux.Proofs.WG.Index.SendSource
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do
theorem keypairPut_tables (key : Option KeypairId) (now : Bool) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ keypairPut key now ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) : Ensures (branchCmp site value lhs rhs : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.hiddenClock64 site)
  have hpeek (kind : Worker) (pid : PeerId) : Ensures (peekQueuedUnit kind pid : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.peekQueuedUnit kind pid)
  have hqueue (kind : Worker) (pid : PeerId) : Ensures (recordQueued kind pid : WG.M Unit) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.recordQueued kind pid)
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run; cases run
  have hreadPeer (pid : PeerId) : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG) g a r f b pre run).1
  have hreadDev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hreadKey (id : KeypairId) : Ensures (getKeypair id) TablesSafeWG (fun _ => TablesSafeWG) := by
    unfold getKeypair
    refine ensures_bind _ _ hreadDev ?_
    intro d
    split
    · exact hpure _
    · exact hstop _
  have hmodify (f : Device → Device) (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d) :
      Ensures (modifyDev f) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r final b pre run
    cases run
    exact tablesSafe_of_cursor g _ (by simp [Option.map_map, Function.comp_def, same]) pre
  have hif {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
      (hy : Ensures yes TablesSafeWG (fun _ => TablesSafeWG))
      (hn : Ensures no TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (if p then yes else no) TablesSafeWG (fun _ => TablesSafeWG) := by split <;> assumption
  have hword (owner : IndexOwner) : Ensures owner.peerDeref TablesSafeWG (fun _ => TablesSafeWG) := by
    unfold IndexOwner.peerDeref
    have hr : Ensures owner.peerWord TablesSafeWG (fun _ => TablesSafeWG) := by
      cases owner with
      | handshake pid => exact ensures_bind _ _ (hreadPeer pid) (fun p => hpure p.handshakeEntryPeer)
      | keypair kid => exact ensures_bind _ _ (hreadKey kid) (fun k => hpure k.peer)
    refine ensures_bind _ _ hr ?_
    intro word
    cases word with
    | none => exact hambient (AmbientM.unsupported _)
    | some pid => exact hpure pid
  have href (n : Nat) : Ensures (refcountDecAndTest n : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run
    by_cases zero : n = 0
    · simp [refcountDecAndTest, zero, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
        unsupported, AmbientM.unsupported] at run
      cases run
    · by_cases one : n = 1
      · simp [refcountDecAndTest, one, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp] at run
        rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
      · have positive : 0 < n := by omega
        have noUnderflow : ¬ n < 1 := by omega
        simp [refcountDecAndTest, zero, one, positive, noUnderflow, branch, branchCmp,
          AmbientM.branch, AmbientM.branchCmp] at run
        rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  apply (ensures_iff _ _ _).mp
  unfold keypairPut
  dsimp only
  repeat' first
    | with_reducible exact hpure _
    | with_reducible exact hbranch _ _
    | with_reducible exact hcmp _ _ _ _
    | with_reducible exact hclock _
    | with_reducible exact hpeek _ _
    | with_reducible exact hqueue _ _
    | with_reducible exact hstop _
    | with_reducible exact hreadKey _
    | with_reducible exact hword _
    | with_reducible exact href _
    | with_reducible exact hmodify _ (fun _ => rfl)
    | with_reducible exact (ensures_iff _ _ _).mpr (setKeypair_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (indexRemove_tables _)
    | (with_reducible refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | split
theorem sendQueuedHandshakeInitiation_tables (pid : PeerId) (retry : Bool) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ sendQueuedHandshakeInitiation pid retry ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) : Ensures (branchCmp site value lhs rhs : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.hiddenClock64 site)
  have hpeek (kind : Worker) (pid : PeerId) : Ensures (peekQueuedUnit kind pid : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.peekQueuedUnit kind pid)
  have hqueue (kind : Worker) (pid : PeerId) : Ensures (recordQueued kind pid : WG.M Unit) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.recordQueued kind pid)
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run; cases run
  have hreadPeer (pid : PeerId) : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG) g a r f b pre run).1
  have hreadDev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hreadKey (id : KeypairId) : Ensures (getKeypair id) TablesSafeWG (fun _ => TablesSafeWG) := by
    unfold getKeypair
    refine ensures_bind _ _ hreadDev ?_
    intro d
    split
    · exact hpure _
    · exact hstop _
  have hmodify (f : Device → Device) (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d) :
      Ensures (modifyDev f) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r final b pre run
    cases run
    exact tablesSafe_of_cursor g _ (by simp [Option.map_map, Function.comp_def, same]) pre
  have hif {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
      (hy : Ensures yes TablesSafeWG (fun _ => TablesSafeWG))
      (hn : Ensures no TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (if p then yes else no) TablesSafeWG (fun _ => TablesSafeWG) := by split <;> assumption
  apply (ensures_iff _ _ _).mp
  unfold sendQueuedHandshakeInitiation
  simp only [branchExpired, birthdateTest, bind_assoc, pure_bind]
  all_goals repeat' first
    | with_reducible exact hpure _
    | with_reducible exact hbranch _ _
    | with_reducible exact hcmp _ _ _ _
    | with_reducible exact hclock _
    | with_reducible exact hpeek _ _
    | with_reducible exact hqueue _ _
    | with_reducible exact hstop _
    | with_reducible exact hreadPeer _
    | with_reducible exact hreadDev
    | with_reducible exact hreadKey _
    | with_reducible exact hmodify _ (fun _ => rfl)
    | with_reducible exact (ensures_iff _ _ _).mpr (setPeer_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (setKeypair_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (peerGet_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (peerPut_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (indexRemove_tables _)
    | (with_reducible refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | split
theorem enqueuePerPeerTx_tables (item : List SkbId) (state : PacketState) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ enqueuePerPeerTx item state ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) : Ensures (branchCmp site value lhs rhs : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.hiddenClock64 site)
  have hpeek (kind : Worker) (pid : PeerId) : Ensures (peekQueuedUnit kind pid : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.peekQueuedUnit kind pid)
  have hqueue (kind : Worker) (pid : PeerId) : Ensures (recordQueued kind pid : WG.M Unit) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.recordQueued kind pid)
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run; cases run
  have hreadPeer (pid : PeerId) : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG) g a r f b pre run).1
  have hreadDev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hreadKey (id : KeypairId) : Ensures (getKeypair id) TablesSafeWG (fun _ => TablesSafeWG) := by
    unfold getKeypair
    refine ensures_bind _ _ hreadDev ?_
    intro d
    split
    · exact hpure _
    · exact hstop _
  have hmodify (f : Device → Device) (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d) :
      Ensures (modifyDev f) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r final b pre run
    cases run
    exact tablesSafe_of_cursor g _ (by simp [Option.map_map, Function.comp_def, same]) pre
  have hif {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
      (hy : Ensures yes TablesSafeWG (fun _ => TablesSafeWG))
      (hn : Ensures no TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (if p then yes else no) TablesSafeWG (fun _ => TablesSafeWG) := by split <;> assumption
  have hword (owner : IndexOwner) : Ensures owner.peerDeref TablesSafeWG (fun _ => TablesSafeWG) := by
    unfold IndexOwner.peerDeref
    have hr : Ensures owner.peerWord TablesSafeWG (fun _ => TablesSafeWG) := by
      cases owner with
      | handshake pid => exact ensures_bind _ _ (hreadPeer pid) (fun p => hpure p.handshakeEntryPeer)
      | keypair kid => exact ensures_bind _ _ (hreadKey kid) (fun k => hpure k.peer)
    refine ensures_bind _ _ hr ?_
    intro word
    cases word with
    | none => exact hambient (AmbientM.unsupported _)
    | some pid => exact hpure pid
  have hreadTx (id : SkbId) : Ensures (getTxSkb id) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none =>
      simp [getTxSkb, liftSkb, getDev, device, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      cases executed : ((SkbStore.getTx id).run {txSkbs := d.txSkbs, rxSkbs := d.rxSkbs, nextSkb := d.nextSkb}).run ambient with
      | error err =>
        simp [getTxSkb, liftSkb, getDev, device, executed] at run
        cases run
      | ok pair =>
        obtain ⟨⟨value, store⟩, inputs⟩ := pair
        simp [getTxSkb, liftSkb, getDev, modifyDev, device, executed] at run
        rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        intro next present
        cases present
        exact pre d device
  have hloop {α β : Type} (xs : List α) (state : β) (step : α → β → WG.M (ForInStep β))
      (preserve : ∀ x state, Ensures (step x state) TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (forIn xs state step) TablesSafeWG (fun _ => TablesSafeWG) := by
    induction xs generalizing state with
    | nil => exact hpure _
    | cons x xs ih =>
      rw [List.forIn_cons]
      refine ensures_bind _ _ (preserve x state) ?_
      intro out
      cases out with
      | done v => exact hpure _
      | yield v => exact ih v
  apply (ensures_iff _ _ _).mp
  unfold enqueuePerPeerTx
  all_goals repeat' first
    | with_reducible exact hpure _
    | with_reducible exact hbranch _ _
    | with_reducible exact hcmp _ _ _ _
    | with_reducible exact hclock _
    | with_reducible exact hpeek _ _
    | with_reducible exact hqueue _ _
    | with_reducible exact hstop _
    | with_reducible exact hreadPeer _
    | with_reducible exact hreadDev
    | with_reducible exact hreadKey _
    | with_reducible exact hreadTx _
    | with_reducible exact hword _
    | with_reducible exact hmodify _ (fun _ => rfl)
    | with_reducible exact (ensures_iff _ _ _).mpr (setPeer_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (setKeypair_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (peerGet_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (peerPut_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (setTxSkb_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (freeTxSkb_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (cpumaskChooseOnline_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (enqueuePerDeviceAndPeer_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (keypairPut_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (sendQueuedHandshakeInitiation_tables _ _)
    | (with_reducible refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | (with_reducible refine hloop _ _ _ ?_; intro _ _)
    | split
theorem createData_tables (pid : PeerId) (item : List SkbId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ createData pid item ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) : Ensures (branchCmp site value lhs rhs : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.hiddenClock64 site)
  have hpeek (kind : Worker) (pid : PeerId) : Ensures (peekQueuedUnit kind pid : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.peekQueuedUnit kind pid)
  have hqueue (kind : Worker) (pid : PeerId) : Ensures (recordQueued kind pid : WG.M Unit) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.recordQueued kind pid)
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run; cases run
  have hreadPeer (pid : PeerId) : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG) g a r f b pre run).1
  have hreadDev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hreadKey (id : KeypairId) : Ensures (getKeypair id) TablesSafeWG (fun _ => TablesSafeWG) := by
    unfold getKeypair
    refine ensures_bind _ _ hreadDev ?_
    intro d
    split
    · exact hpure _
    · exact hstop _
  have hmodify (f : Device → Device) (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d) :
      Ensures (modifyDev f) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r final b pre run
    cases run
    exact tablesSafe_of_cursor g _ (by simp [Option.map_map, Function.comp_def, same]) pre
  have hif {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
      (hy : Ensures yes TablesSafeWG (fun _ => TablesSafeWG))
      (hn : Ensures no TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (if p then yes else no) TablesSafeWG (fun _ => TablesSafeWG) := by split <;> assumption
  have hword (owner : IndexOwner) : Ensures owner.peerDeref TablesSafeWG (fun _ => TablesSafeWG) := by
    unfold IndexOwner.peerDeref
    have hr : Ensures owner.peerWord TablesSafeWG (fun _ => TablesSafeWG) := by
      cases owner with
      | handshake pid => exact ensures_bind _ _ (hreadPeer pid) (fun p => hpure p.handshakeEntryPeer)
      | keypair kid => exact ensures_bind _ _ (hreadKey kid) (fun k => hpure k.peer)
    refine ensures_bind _ _ hr ?_
    intro word
    cases word with
    | none => exact hambient (AmbientM.unsupported _)
    | some pid => exact hpure pid
  have hreadTx (id : SkbId) : Ensures (getTxSkb id) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none =>
      simp [getTxSkb, liftSkb, getDev, device, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      cases executed : ((SkbStore.getTx id).run {txSkbs := d.txSkbs, rxSkbs := d.rxSkbs, nextSkb := d.nextSkb}).run ambient with
      | error err =>
        simp [getTxSkb, liftSkb, getDev, device, executed] at run
        cases run
      | ok pair =>
        obtain ⟨⟨value, store⟩, inputs⟩ := pair
        simp [getTxSkb, liftSkb, getDev, modifyDev, device, executed] at run
        rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        intro next present
        cases present
        exact pre d device
  have hloop {α β : Type} (xs : List α) (state : β) (step : α → β → WG.M (ForInStep β))
      (preserve : ∀ x state, Ensures (step x state) TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (forIn xs state step) TablesSafeWG (fun _ => TablesSafeWG) := by
    induction xs generalizing state with
    | nil => exact hpure _
    | cons x xs ih =>
      rw [List.forIn_cons]
      refine ensures_bind _ _ (preserve x state) ?_
      intro out
      cases out with
      | done v => exact hpure _
      | yield v => exact ih v
  apply (ensures_iff _ _ _).mp
  unfold createData
  simp only [pure_bind]
  all_goals repeat' first
    | with_reducible exact hpure _
    | with_reducible exact hbranch _ _
    | with_reducible exact hcmp _ _ _ _
    | with_reducible exact hclock _
    | with_reducible exact hpeek _ _
    | with_reducible exact hqueue _ _
    | with_reducible exact hstop _
    | with_reducible exact hreadPeer _
    | with_reducible exact hreadDev
    | with_reducible exact hreadKey _
    | with_reducible exact hreadTx _
    | with_reducible exact hword _
    | with_reducible exact hmodify _ (fun _ => rfl)
    | with_reducible exact (ensures_iff _ _ _).mpr (setPeer_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (setKeypair_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (peerGet_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (peerPut_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (setTxSkb_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (freeTxSkb_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (cpumaskChooseOnline_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (enqueuePerDeviceAndPeer_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (keypairPut_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (sendQueuedHandshakeInitiation_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (enqueuePerPeerTx_tables _ _)
    | (with_reducible refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | (with_reducible refine hloop _ _ _ ?_; intro _ _)
    | split
theorem stagedFallback_tables (pid : PeerId) (packets : List Packet) (key : Option KeypairId) (invalid : Bool) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ Config.stagedFallback pid packets key invalid ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) : Ensures (branchCmp site value lhs rhs : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.hiddenClock64 site)
  have hpeek (kind : Worker) (pid : PeerId) : Ensures (peekQueuedUnit kind pid : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.peekQueuedUnit kind pid)
  have hqueue (kind : Worker) (pid : PeerId) : Ensures (recordQueued kind pid : WG.M Unit) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.recordQueued kind pid)
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run; cases run
  have hreadPeer (pid : PeerId) : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG) g a r f b pre run).1
  have hreadDev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hreadKey (id : KeypairId) : Ensures (getKeypair id) TablesSafeWG (fun _ => TablesSafeWG) := by
    unfold getKeypair
    refine ensures_bind _ _ hreadDev ?_
    intro d
    split
    · exact hpure _
    · exact hstop _
  have hmodify (f : Device → Device) (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d) :
      Ensures (modifyDev f) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r final b pre run
    cases run
    exact tablesSafe_of_cursor g _ (by simp [Option.map_map, Function.comp_def, same]) pre
  have hif {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
      (hy : Ensures yes TablesSafeWG (fun _ => TablesSafeWG))
      (hn : Ensures no TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (if p then yes else no) TablesSafeWG (fun _ => TablesSafeWG) := by split <;> assumption
  have hword (owner : IndexOwner) : Ensures owner.peerDeref TablesSafeWG (fun _ => TablesSafeWG) := by
    unfold IndexOwner.peerDeref
    have hr : Ensures owner.peerWord TablesSafeWG (fun _ => TablesSafeWG) := by
      cases owner with
      | handshake pid => exact ensures_bind _ _ (hreadPeer pid) (fun p => hpure p.handshakeEntryPeer)
      | keypair kid => exact ensures_bind _ _ (hreadKey kid) (fun k => hpure k.peer)
    refine ensures_bind _ _ hr ?_
    intro word
    cases word with
    | none => exact hambient (AmbientM.unsupported _)
    | some pid => exact hpure pid
  have hreadTx (id : SkbId) : Ensures (getTxSkb id) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none =>
      simp [getTxSkb, liftSkb, getDev, device, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      cases executed : ((SkbStore.getTx id).run {txSkbs := d.txSkbs, rxSkbs := d.rxSkbs, nextSkb := d.nextSkb}).run ambient with
      | error err =>
        simp [getTxSkb, liftSkb, getDev, device, executed] at run
        cases run
      | ok pair =>
        obtain ⟨⟨value, store⟩, inputs⟩ := pair
        simp [getTxSkb, liftSkb, getDev, modifyDev, device, executed] at run
        rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        intro next present
        cases present
        exact pre d device
  have hloop {α β : Type} (xs : List α) (state : β) (step : α → β → WG.M (ForInStep β))
      (preserve : ∀ x state, Ensures (step x state) TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (forIn xs state step) TablesSafeWG (fun _ => TablesSafeWG) := by
    induction xs generalizing state with
    | nil => exact hpure _
    | cons x xs ih =>
      rw [List.forIn_cons]
      refine ensures_bind _ _ (preserve x state) ?_
      intro out
      cases out with
      | done v => exact hpure _
      | yield v => exact ih v
  apply (ensures_iff _ _ _).mp
  unfold Config.stagedFallback
  all_goals repeat' first
    | with_reducible exact hpure _
    | with_reducible exact hbranch _ _
    | with_reducible exact hcmp _ _ _ _
    | with_reducible exact hclock _
    | with_reducible exact hpeek _ _
    | with_reducible exact hqueue _ _
    | with_reducible exact hstop _
    | with_reducible exact hreadPeer _
    | with_reducible exact hreadDev
    | with_reducible exact hreadKey _
    | with_reducible exact hreadTx _
    | with_reducible exact hword _
    | with_reducible exact hmodify _ (fun _ => rfl)
    | with_reducible exact (ensures_iff _ _ _).mpr (setPeer_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (setKeypair_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (peerGet_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (peerPut_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (setTxSkb_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (freeTxSkb_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (cpumaskChooseOnline_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (enqueuePerDeviceAndPeer_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (keypairPut_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (sendQueuedHandshakeInitiation_tables _ _)
    | (with_reducible refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | (with_reducible refine hloop _ _ _ ?_; intro _ _)
    | split
theorem stagedAfterGet_tables (pid : PeerId) (packets : List Packet) (key : Option KeypairId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ Config.stagedAfterGet pid packets key ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) : Ensures (branchCmp site value lhs rhs : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.hiddenClock64 site)
  have hpeek (kind : Worker) (pid : PeerId) : Ensures (peekQueuedUnit kind pid : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.peekQueuedUnit kind pid)
  have hqueue (kind : Worker) (pid : PeerId) : Ensures (recordQueued kind pid : WG.M Unit) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.recordQueued kind pid)
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run; cases run
  have hreadPeer (pid : PeerId) : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG) g a r f b pre run).1
  have hreadDev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hreadKey (id : KeypairId) : Ensures (getKeypair id) TablesSafeWG (fun _ => TablesSafeWG) := by
    unfold getKeypair
    refine ensures_bind _ _ hreadDev ?_
    intro d
    split
    · exact hpure _
    · exact hstop _
  have hmodify (f : Device → Device) (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d) :
      Ensures (modifyDev f) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r final b pre run
    cases run
    exact tablesSafe_of_cursor g _ (by simp [Option.map_map, Function.comp_def, same]) pre
  have hif {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
      (hy : Ensures yes TablesSafeWG (fun _ => TablesSafeWG))
      (hn : Ensures no TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (if p then yes else no) TablesSafeWG (fun _ => TablesSafeWG) := by split <;> assumption
  have hword (owner : IndexOwner) : Ensures owner.peerDeref TablesSafeWG (fun _ => TablesSafeWG) := by
    unfold IndexOwner.peerDeref
    have hr : Ensures owner.peerWord TablesSafeWG (fun _ => TablesSafeWG) := by
      cases owner with
      | handshake pid => exact ensures_bind _ _ (hreadPeer pid) (fun p => hpure p.handshakeEntryPeer)
      | keypair kid => exact ensures_bind _ _ (hreadKey kid) (fun k => hpure k.peer)
    refine ensures_bind _ _ hr ?_
    intro word
    cases word with
    | none => exact hambient (AmbientM.unsupported _)
    | some pid => exact hpure pid
  have hreadTx (id : SkbId) : Ensures (getTxSkb id) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none =>
      simp [getTxSkb, liftSkb, getDev, device, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      cases executed : ((SkbStore.getTx id).run {txSkbs := d.txSkbs, rxSkbs := d.rxSkbs, nextSkb := d.nextSkb}).run ambient with
      | error err =>
        simp [getTxSkb, liftSkb, getDev, device, executed] at run
        cases run
      | ok pair =>
        obtain ⟨⟨value, store⟩, inputs⟩ := pair
        simp [getTxSkb, liftSkb, getDev, modifyDev, device, executed] at run
        rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        intro next present
        cases present
        exact pre d device
  have hloop {α β : Type} (xs : List α) (state : β) (step : α → β → WG.M (ForInStep β))
      (preserve : ∀ x state, Ensures (step x state) TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (forIn xs state step) TablesSafeWG (fun _ => TablesSafeWG) := by
    induction xs generalizing state with
    | nil => exact hpure _
    | cons x xs ih =>
      rw [List.forIn_cons]
      refine ensures_bind _ _ (preserve x state) ?_
      intro out
      cases out with
      | done v => exact hpure _
      | yield v => exact ih v
  apply (ensures_iff _ _ _).mp
  unfold Config.stagedAfterGet
  simp only [branchExpired, birthdateTest, bind_assoc, pure_bind]
  all_goals repeat' first
    | with_reducible exact hpure _
    | with_reducible exact hbranch _ _
    | with_reducible exact hcmp _ _ _ _
    | with_reducible exact hclock _
    | with_reducible exact hpeek _ _
    | with_reducible exact hqueue _ _
    | with_reducible exact hstop _
    | with_reducible exact hreadPeer _
    | with_reducible exact hreadDev
    | with_reducible exact hreadKey _
    | with_reducible exact hreadTx _
    | with_reducible exact hword _
    | with_reducible exact hmodify _ (fun _ => rfl)
    | with_reducible exact (ensures_iff _ _ _).mpr (setPeer_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (setKeypair_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (peerGet_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (peerPut_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (setTxSkb_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (freeTxSkb_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (cpumaskChooseOnline_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (enqueuePerDeviceAndPeer_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (keypairPut_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (sendQueuedHandshakeInitiation_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (stagedFallback_tables _ _ _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (ipTunnelEcnEncap_wg_variant TablesSafeWG _)
    | with_reducible exact (ensures_iff _ _ _).mpr (newTxSkbs_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (createData_tables _ _)
    | (with_reducible refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | (with_reducible refine hloop _ _ _ ?_; intro _ _)
    | split
theorem sendStagedPackets_tables (pid : PeerId) :
    Ensures (sendStagedPackets pid) TablesSafeWG (fun _ => TablesSafeWG) := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) : Ensures (branchCmp site value lhs rhs : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.hiddenClock64 site)
  have hpeek (kind : Worker) (pid : PeerId) : Ensures (peekQueuedUnit kind pid : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.peekQueuedUnit kind pid)
  have hqueue (kind : Worker) (pid : PeerId) : Ensures (recordQueued kind pid : WG.M Unit) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.recordQueued kind pid)
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run; cases run
  have hreadPeer (pid : PeerId) : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG) g a r f b pre run).1
  have hreadDev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hreadKey (id : KeypairId) : Ensures (getKeypair id) TablesSafeWG (fun _ => TablesSafeWG) := by
    unfold getKeypair
    refine ensures_bind _ _ hreadDev ?_
    intro d
    split
    · exact hpure _
    · exact hstop _
  have hmodify (f : Device → Device) (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d) :
      Ensures (modifyDev f) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r final b pre run
    cases run
    exact tablesSafe_of_cursor g _ (by simp [Option.map_map, Function.comp_def, same]) pre
  have hif {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
      (hy : Ensures yes TablesSafeWG (fun _ => TablesSafeWG))
      (hn : Ensures no TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (if p then yes else no) TablesSafeWG (fun _ => TablesSafeWG) := by split <;> assumption
  rw [← Config.sendStaged_source]
  unfold Config.stagedSource
  repeat' first
    | with_reducible exact hpure _
    | with_reducible exact hbranch _ _
    | with_reducible exact hreadPeer _
    | with_reducible exact (ensures_iff _ _ _).mpr (setPeer_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (keypairGet_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (stagedAfterGet_tables _ _ _)
    | (with_reducible refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
theorem sendKeepalive_tables (pid : PeerId) :
    Ensures (sendKeepalive pid) TablesSafeWG (fun _ => TablesSafeWG) := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) : Ensures (branchCmp site value lhs rhs : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.hiddenClock64 site)
  have hpeek (kind : Worker) (pid : PeerId) : Ensures (peekQueuedUnit kind pid : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.peekQueuedUnit kind pid)
  have hqueue (kind : Worker) (pid : PeerId) : Ensures (recordQueued kind pid : WG.M Unit) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.recordQueued kind pid)
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run; cases run
  have hreadPeer (pid : PeerId) : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG) g a r f b pre run).1
  have hreadDev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r f b pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hreadKey (id : KeypairId) : Ensures (getKeypair id) TablesSafeWG (fun _ => TablesSafeWG) := by
    unfold getKeypair
    refine ensures_bind _ _ hreadDev ?_
    intro d
    split
    · exact hpure _
    · exact hstop _
  have hmodify (f : Device → Device) (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d) :
      Ensures (modifyDev f) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r final b pre run
    cases run
    exact tablesSafe_of_cursor g _ (by simp [Option.map_map, Function.comp_def, same]) pre
  have hif {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
      (hy : Ensures yes TablesSafeWG (fun _ => TablesSafeWG))
      (hn : Ensures no TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (if p then yes else no) TablesSafeWG (fun _ => TablesSafeWG) := by split <;> assumption
  have halloc (site : AllocSite) : Ensures (hiddenAlloc site : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.hiddenAlloc site)
  unfold sendKeepalive
  repeat' first
    | with_reducible exact hpure _
    | with_reducible exact hbranch _ _
    | with_reducible exact hreadPeer _
    | with_reducible exact hreadDev
    | with_reducible exact halloc _
    | with_reducible exact (ensures_iff _ _ _).mpr (setPeer_tables _ _)
    | with_reducible exact sendStagedPackets_tables _
    | (with_reducible refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
end Leanux.Proofs.WG.Index
