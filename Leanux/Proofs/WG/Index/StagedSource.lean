import Leanux.Proofs.WG.Index.StagedFrames
import Leanux.Proofs.WG.Index.SendSource
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do
theorem keypairPut_staging (key : Option KeypairId) (now : Bool) (entry : WGWorld) :
    ⦃fun g => ⌜(StagingFrame entry) g⌝⦄ keypairPut key now ⦃⇓? _ g => ⌜(StagingFrame entry) g⌝⦄ := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action (StagingFrame entry))
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) : Ensures (branchCmp site value lhs rhs : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.hiddenClock64 site)
  have hpeek (kind : Worker) (pid : PeerId) : Ensures (peekQueuedUnit kind pid : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.peekQueuedUnit kind pid)
  have hqueue (kind : Worker) (pid : PeerId) : Ensures (recordQueued kind pid : WG.M Unit) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.recordQueued kind pid)
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run; cases run
  have hreadPeer (pid : PeerId) : Ensures (getPeer pid) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid (StagingFrame entry)) g a r f b pre run).1
  have hreadDev : Ensures getDev (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hreadKey (id : KeypairId) : Ensures (getKeypair id) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    unfold getKeypair
    refine ensures_bind _ _ hreadDev ?_
    intro d
    split
    · exact hpure _
    · exact hstop _
  have hmodify (f : Device → Device)
      (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d)
      (peers : ∀ d, (f d).peers = d.peers) :
      Ensures (modifyDev f) (StagingFrame entry) (fun _ => StagingFrame entry) :=
    staging_modifyDev entry f same peers
  have hindex (owner : IndexOwner) :
      Ensures (liftM (indexRemove owner) : WG.M Unit) (StagingFrame entry)
        (fun _ => StagingFrame entry) := staging_indexRemove entry owner
  have hif {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
      (hy : Ensures yes (StagingFrame entry) (fun _ => (StagingFrame entry)))
      (hn : Ensures no (StagingFrame entry) (fun _ => (StagingFrame entry))) :
      Ensures (if p then yes else no) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by split <;> assumption
  have hword (owner : IndexOwner) : Ensures owner.peerDeref (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    unfold IndexOwner.peerDeref
    have hr : Ensures owner.peerWord (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
      cases owner with
      | handshake pid => exact ensures_bind _ _ (hreadPeer pid) (fun p => hpure p.handshakeEntryPeer)
      | keypair kid => exact ensures_bind _ _ (hreadKey kid) (fun k => hpure k.peer)
    refine ensures_bind _ _ hr ?_
    intro word
    cases word with
    | none => exact hambient (AmbientM.unsupported _)
    | some pid => exact hpure pid
  have href (n : Nat) : Ensures (refcountDecAndTest n : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
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
    | with_reducible exact hmodify _ (fun _ => rfl) (fun _ => rfl)
    | with_reducible exact setKeypair_staging _ _ entry
    | with_reducible exact hindex _
    | (staging_getPeer_bind; refine staging_read_bind entry _ _ _ ?_; intro p tag)
    | (with_reducible refine ensures_bind (Q := fun _ => (StagingFrame entry)) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | split
theorem sendQueuedHandshakeInitiation_staging (pid : PeerId) (retry : Bool) (entry : WGWorld) :
    ⦃fun g => ⌜(StagingFrame entry) g⌝⦄ sendQueuedHandshakeInitiation pid retry ⦃⇓? _ g => ⌜(StagingFrame entry) g⌝⦄ := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action (StagingFrame entry))
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) : Ensures (branchCmp site value lhs rhs : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.hiddenClock64 site)
  have hpeek (kind : Worker) (pid : PeerId) : Ensures (peekQueuedUnit kind pid : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.peekQueuedUnit kind pid)
  have hqueue (kind : Worker) (pid : PeerId) : Ensures (recordQueued kind pid : WG.M Unit) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.recordQueued kind pid)
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run; cases run
  have hreadPeer (pid : PeerId) : Ensures (getPeer pid) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid (StagingFrame entry)) g a r f b pre run).1
  have hreadDev : Ensures getDev (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hreadKey (id : KeypairId) : Ensures (getKeypair id) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    unfold getKeypair
    refine ensures_bind _ _ hreadDev ?_
    intro d
    split
    · exact hpure _
    · exact hstop _
  have hmodify (f : Device → Device)
      (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d)
      (peers : ∀ d, (f d).peers = d.peers) :
      Ensures (modifyDev f) (StagingFrame entry) (fun _ => StagingFrame entry) :=
    staging_modifyDev entry f same peers
  have hindex (owner : IndexOwner) :
      Ensures (liftM (indexRemove owner) : WG.M Unit) (StagingFrame entry)
        (fun _ => StagingFrame entry) := staging_indexRemove entry owner
  have hif {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
      (hy : Ensures yes (StagingFrame entry) (fun _ => (StagingFrame entry)))
      (hn : Ensures no (StagingFrame entry) (fun _ => (StagingFrame entry))) :
      Ensures (if p then yes else no) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by split <;> assumption
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
    | with_reducible exact hmodify _ (fun _ => rfl) (fun _ => rfl)
    | with_reducible exact staging_setPeer entry _ _ (by assumption)
    | with_reducible exact setKeypair_staging _ _ entry
    | with_reducible exact peerGet_staging _ entry
    | with_reducible exact staging_peerPut entry _
    | with_reducible exact hindex _
    | (staging_getPeer_bind; refine staging_read_bind entry _ _ _ ?_; intro p tag)
    | (with_reducible refine ensures_bind (Q := fun _ => (StagingFrame entry)) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | split
theorem enqueuePerPeerTx_staging (item : List SkbId) (state : PacketState) (entry : WGWorld) :
    ⦃fun g => ⌜(StagingFrame entry) g⌝⦄ enqueuePerPeerTx item state ⦃⇓? _ g => ⌜(StagingFrame entry) g⌝⦄ := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action (StagingFrame entry))
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) : Ensures (branchCmp site value lhs rhs : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.hiddenClock64 site)
  have hpeek (kind : Worker) (pid : PeerId) : Ensures (peekQueuedUnit kind pid : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.peekQueuedUnit kind pid)
  have hqueue (kind : Worker) (pid : PeerId) : Ensures (recordQueued kind pid : WG.M Unit) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.recordQueued kind pid)
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run; cases run
  have hreadPeer (pid : PeerId) : Ensures (getPeer pid) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid (StagingFrame entry)) g a r f b pre run).1
  have hreadDev : Ensures getDev (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hreadKey (id : KeypairId) : Ensures (getKeypair id) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    unfold getKeypair
    refine ensures_bind _ _ hreadDev ?_
    intro d
    split
    · exact hpure _
    · exact hstop _
  have hmodify (f : Device → Device)
      (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d)
      (peers : ∀ d, (f d).peers = d.peers) :
      Ensures (modifyDev f) (StagingFrame entry) (fun _ => StagingFrame entry) :=
    staging_modifyDev entry f same peers
  have hindex (owner : IndexOwner) :
      Ensures (liftM (indexRemove owner) : WG.M Unit) (StagingFrame entry)
        (fun _ => StagingFrame entry) := staging_indexRemove entry owner
  have hif {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
      (hy : Ensures yes (StagingFrame entry) (fun _ => (StagingFrame entry)))
      (hn : Ensures no (StagingFrame entry) (fun _ => (StagingFrame entry))) :
      Ensures (if p then yes else no) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by split <;> assumption
  have hword (owner : IndexOwner) : Ensures owner.peerDeref (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    unfold IndexOwner.peerDeref
    have hr : Ensures owner.peerWord (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
      cases owner with
      | handshake pid => exact ensures_bind _ _ (hreadPeer pid) (fun p => hpure p.handshakeEntryPeer)
      | keypair kid => exact ensures_bind _ _ (hreadKey kid) (fun k => hpure k.peer)
    refine ensures_bind _ _ hr ?_
    intro word
    cases word with
    | none => exact hambient (AmbientM.unsupported _)
    | some pid => exact hpure pid
  have hreadTx (id : SkbId) :
      Ensures (getTxSkb id) (StagingFrame entry) (fun _ => StagingFrame entry) :=
    liftSkb_staging (SkbStore.getTx id) entry
  have hloop {α β : Type} (xs : List α) (state : β) (step : α → β → WG.M (ForInStep β))
      (preserve : ∀ x state, Ensures (step x state) (StagingFrame entry) (fun _ => (StagingFrame entry))) :
      Ensures (forIn xs state step) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
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
    | with_reducible exact hmodify _ (fun _ => rfl) (fun _ => rfl)
    | with_reducible exact staging_setPeer entry _ _ (by assumption)
    | with_reducible exact setKeypair_staging _ _ entry
    | with_reducible exact peerGet_staging _ entry
    | with_reducible exact staging_peerPut entry _
    | with_reducible exact setTxSkb_staging _ _ entry
    | with_reducible exact freeTxSkb_staging _ entry
    | with_reducible exact cpumaskChooseOnline_staging _ entry
    | with_reducible exact enqueuePerDeviceAndPeer_staging _ _ entry
    | with_reducible exact (ensures_iff _ _ _).mpr (keypairPut_staging _ _ entry)
    | with_reducible exact (ensures_iff _ _ _).mpr (sendQueuedHandshakeInitiation_staging _ _ entry)
    | (staging_getPeer_bind; refine staging_read_bind entry _ _ _ ?_; intro p tag)
    | (with_reducible refine ensures_bind (Q := fun _ => (StagingFrame entry)) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | (with_reducible refine hloop _ _ _ ?_; intro _ _)
    | split
theorem createData_staging (pid : PeerId) (item : List SkbId) (entry : WGWorld) :
    ⦃fun g => ⌜(StagingFrame entry) g⌝⦄ createData pid item ⦃⇓? _ g => ⌜(StagingFrame entry) g⌝⦄ := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action (StagingFrame entry))
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) : Ensures (branchCmp site value lhs rhs : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.hiddenClock64 site)
  have hpeek (kind : Worker) (pid : PeerId) : Ensures (peekQueuedUnit kind pid : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.peekQueuedUnit kind pid)
  have hqueue (kind : Worker) (pid : PeerId) : Ensures (recordQueued kind pid : WG.M Unit) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.recordQueued kind pid)
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run; cases run
  have hreadPeer (pid : PeerId) : Ensures (getPeer pid) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid (StagingFrame entry)) g a r f b pre run).1
  have hreadDev : Ensures getDev (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hreadKey (id : KeypairId) : Ensures (getKeypair id) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    unfold getKeypair
    refine ensures_bind _ _ hreadDev ?_
    intro d
    split
    · exact hpure _
    · exact hstop _
  have hmodify (f : Device → Device)
      (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d)
      (peers : ∀ d, (f d).peers = d.peers) :
      Ensures (modifyDev f) (StagingFrame entry) (fun _ => StagingFrame entry) :=
    staging_modifyDev entry f same peers
  have hindex (owner : IndexOwner) :
      Ensures (liftM (indexRemove owner) : WG.M Unit) (StagingFrame entry)
        (fun _ => StagingFrame entry) := staging_indexRemove entry owner
  have hif {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
      (hy : Ensures yes (StagingFrame entry) (fun _ => (StagingFrame entry)))
      (hn : Ensures no (StagingFrame entry) (fun _ => (StagingFrame entry))) :
      Ensures (if p then yes else no) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by split <;> assumption
  have hword (owner : IndexOwner) : Ensures owner.peerDeref (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    unfold IndexOwner.peerDeref
    have hr : Ensures owner.peerWord (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
      cases owner with
      | handshake pid => exact ensures_bind _ _ (hreadPeer pid) (fun p => hpure p.handshakeEntryPeer)
      | keypair kid => exact ensures_bind _ _ (hreadKey kid) (fun k => hpure k.peer)
    refine ensures_bind _ _ hr ?_
    intro word
    cases word with
    | none => exact hambient (AmbientM.unsupported _)
    | some pid => exact hpure pid
  have hreadTx (id : SkbId) :
      Ensures (getTxSkb id) (StagingFrame entry) (fun _ => StagingFrame entry) :=
    liftSkb_staging (SkbStore.getTx id) entry
  have hloop {α β : Type} (xs : List α) (state : β) (step : α → β → WG.M (ForInStep β))
      (preserve : ∀ x state, Ensures (step x state) (StagingFrame entry) (fun _ => (StagingFrame entry))) :
      Ensures (forIn xs state step) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
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
    | with_reducible exact hmodify _ (fun _ => rfl) (fun _ => rfl)
    | with_reducible exact staging_setPeer entry _ _ (by assumption)
    | with_reducible exact setKeypair_staging _ _ entry
    | with_reducible exact peerGet_staging _ entry
    | with_reducible exact staging_peerPut entry _
    | with_reducible exact setTxSkb_staging _ _ entry
    | with_reducible exact freeTxSkb_staging _ entry
    | with_reducible exact cpumaskChooseOnline_staging _ entry
    | with_reducible exact enqueuePerDeviceAndPeer_staging _ _ entry
    | with_reducible exact (ensures_iff _ _ _).mpr (keypairPut_staging _ _ entry)
    | with_reducible exact (ensures_iff _ _ _).mpr (sendQueuedHandshakeInitiation_staging _ _ entry)
    | with_reducible exact (ensures_iff _ _ _).mpr (enqueuePerPeerTx_staging _ _ entry)
    | (staging_getPeer_bind; refine staging_read_bind entry _ _ _ ?_; intro p tag)
    | (with_reducible refine ensures_bind (Q := fun _ => (StagingFrame entry)) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | (with_reducible refine hloop _ _ _ ?_; intro _ _)
    | split
theorem stagedFallback_staging (pid : PeerId) (packets : List Packet) (key : Option KeypairId) (invalid : Bool) (entry : WGWorld) :
    ⦃fun g => ⌜(StagingFrame entry) g⌝⦄ Config.stagedFallback pid packets key invalid ⦃⇓? _ g => ⌜(StagingFrame entry) g⌝⦄ := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action (StagingFrame entry))
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) : Ensures (branchCmp site value lhs rhs : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.hiddenClock64 site)
  have hpeek (kind : Worker) (pid : PeerId) : Ensures (peekQueuedUnit kind pid : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.peekQueuedUnit kind pid)
  have hqueue (kind : Worker) (pid : PeerId) : Ensures (recordQueued kind pid : WG.M Unit) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.recordQueued kind pid)
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run; cases run
  have hreadPeer (pid : PeerId) : Ensures (getPeer pid) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid (StagingFrame entry)) g a r f b pre run).1
  have hreadDev : Ensures getDev (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hreadKey (id : KeypairId) : Ensures (getKeypair id) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    unfold getKeypair
    refine ensures_bind _ _ hreadDev ?_
    intro d
    split
    · exact hpure _
    · exact hstop _
  have hmodify (f : Device → Device)
      (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d)
      (peers : ∀ d, (f d).peers = d.peers) :
      Ensures (modifyDev f) (StagingFrame entry) (fun _ => StagingFrame entry) :=
    staging_modifyDev entry f same peers
  have hindex (owner : IndexOwner) :
      Ensures (liftM (indexRemove owner) : WG.M Unit) (StagingFrame entry)
        (fun _ => StagingFrame entry) := staging_indexRemove entry owner
  have hif {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
      (hy : Ensures yes (StagingFrame entry) (fun _ => (StagingFrame entry)))
      (hn : Ensures no (StagingFrame entry) (fun _ => (StagingFrame entry))) :
      Ensures (if p then yes else no) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by split <;> assumption
  have hword (owner : IndexOwner) : Ensures owner.peerDeref (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    unfold IndexOwner.peerDeref
    have hr : Ensures owner.peerWord (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
      cases owner with
      | handshake pid => exact ensures_bind _ _ (hreadPeer pid) (fun p => hpure p.handshakeEntryPeer)
      | keypair kid => exact ensures_bind _ _ (hreadKey kid) (fun k => hpure k.peer)
    refine ensures_bind _ _ hr ?_
    intro word
    cases word with
    | none => exact hambient (AmbientM.unsupported _)
    | some pid => exact hpure pid
  have hreadTx (id : SkbId) :
      Ensures (getTxSkb id) (StagingFrame entry) (fun _ => StagingFrame entry) :=
    liftSkb_staging (SkbStore.getTx id) entry
  have hloop {α β : Type} (xs : List α) (state : β) (step : α → β → WG.M (ForInStep β))
      (preserve : ∀ x state, Ensures (step x state) (StagingFrame entry) (fun _ => (StagingFrame entry))) :
      Ensures (forIn xs state step) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
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
  dsimp only
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
    | with_reducible exact hmodify _ (fun _ => rfl) (fun _ => rfl)
    | with_reducible exact staging_setPeer entry _ _ (by assumption)
    | with_reducible exact setKeypair_staging _ _ entry
    | with_reducible exact peerGet_staging _ entry
    | with_reducible exact staging_peerPut entry _
    | with_reducible exact setTxSkb_staging _ _ entry
    | with_reducible exact freeTxSkb_staging _ entry
    | with_reducible exact cpumaskChooseOnline_staging _ entry
    | with_reducible exact enqueuePerDeviceAndPeer_staging _ _ entry
    | with_reducible exact (ensures_iff _ _ _).mpr (keypairPut_staging _ _ entry)
    | with_reducible exact (ensures_iff _ _ _).mpr (sendQueuedHandshakeInitiation_staging _ _ entry)
    | (staging_getPeer_bind; refine staging_read_bind entry _ _ _ ?_; intro p tag)
    | (with_reducible refine ensures_bind (Q := fun _ => (StagingFrame entry)) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | (with_reducible refine hloop _ _ _ ?_; intro _ _)
    | split
theorem stagedAfterGet_staging (pid : PeerId) (packets : List Packet) (key : Option KeypairId) (entry : WGWorld) :
    ⦃fun g => ⌜(StagingFrame entry) g⌝⦄ Config.stagedAfterGet pid packets key ⦃⇓? _ g => ⌜(StagingFrame entry) g⌝⦄ := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action (StagingFrame entry))
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) : Ensures (branchCmp site value lhs rhs : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.hiddenClock64 site)
  have hpeek (kind : Worker) (pid : PeerId) : Ensures (peekQueuedUnit kind pid : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.peekQueuedUnit kind pid)
  have hqueue (kind : Worker) (pid : PeerId) : Ensures (recordQueued kind pid : WG.M Unit) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.recordQueued kind pid)
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run; cases run
  have hreadPeer (pid : PeerId) : Ensures (getPeer pid) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid (StagingFrame entry)) g a r f b pre run).1
  have hreadDev : Ensures getDev (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hreadKey (id : KeypairId) : Ensures (getKeypair id) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    unfold getKeypair
    refine ensures_bind _ _ hreadDev ?_
    intro d
    split
    · exact hpure _
    · exact hstop _
  have hmodify (f : Device → Device)
      (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d)
      (peers : ∀ d, (f d).peers = d.peers) :
      Ensures (modifyDev f) (StagingFrame entry) (fun _ => StagingFrame entry) :=
    staging_modifyDev entry f same peers
  have hindex (owner : IndexOwner) :
      Ensures (liftM (indexRemove owner) : WG.M Unit) (StagingFrame entry)
        (fun _ => StagingFrame entry) := staging_indexRemove entry owner
  have hif {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
      (hy : Ensures yes (StagingFrame entry) (fun _ => (StagingFrame entry)))
      (hn : Ensures no (StagingFrame entry) (fun _ => (StagingFrame entry))) :
      Ensures (if p then yes else no) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by split <;> assumption
  have hword (owner : IndexOwner) : Ensures owner.peerDeref (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    unfold IndexOwner.peerDeref
    have hr : Ensures owner.peerWord (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
      cases owner with
      | handshake pid => exact ensures_bind _ _ (hreadPeer pid) (fun p => hpure p.handshakeEntryPeer)
      | keypair kid => exact ensures_bind _ _ (hreadKey kid) (fun k => hpure k.peer)
    refine ensures_bind _ _ hr ?_
    intro word
    cases word with
    | none => exact hambient (AmbientM.unsupported _)
    | some pid => exact hpure pid
  have hreadTx (id : SkbId) :
      Ensures (getTxSkb id) (StagingFrame entry) (fun _ => StagingFrame entry) :=
    liftSkb_staging (SkbStore.getTx id) entry
  have hloop {α β : Type} (xs : List α) (state : β) (step : α → β → WG.M (ForInStep β))
      (preserve : ∀ x state, Ensures (step x state) (StagingFrame entry) (fun _ => (StagingFrame entry))) :
      Ensures (forIn xs state step) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
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
    | with_reducible exact hmodify _ (fun _ => rfl) (fun _ => rfl)
    | with_reducible exact staging_setPeer entry _ _ (by assumption)
    | with_reducible exact setKeypair_staging _ _ entry
    | with_reducible exact peerGet_staging _ entry
    | with_reducible exact staging_peerPut entry _
    | with_reducible exact setTxSkb_staging _ _ entry
    | with_reducible exact freeTxSkb_staging _ entry
    | with_reducible exact cpumaskChooseOnline_staging _ entry
    | with_reducible exact enqueuePerDeviceAndPeer_staging _ _ entry
    | with_reducible exact (ensures_iff _ _ _).mpr (keypairPut_staging _ _ entry)
    | with_reducible exact (ensures_iff _ _ _).mpr (sendQueuedHandshakeInitiation_staging _ _ entry)
    | with_reducible exact (ensures_iff _ _ _).mpr (stagedFallback_staging _ _ _ _ entry)
    | with_reducible exact (ensures_iff _ _ _).mpr (ipTunnelEcnEncap_wg_variant (StagingFrame entry) _)
    | with_reducible exact newTxSkbs_staging _ entry
    | with_reducible exact (ensures_iff _ _ _).mpr (createData_staging _ _ entry)
    | (staging_getPeer_bind; refine staging_read_bind entry _ _ _ ?_; intro p tag)
    | (with_reducible refine ensures_bind (Q := fun _ => (StagingFrame entry)) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | (with_reducible refine hloop _ _ _ ?_; intro _ _)
    | split
theorem sendStagedPackets_staging (pid : PeerId) (entry : WGWorld) :
    Ensures (sendStagedPackets pid) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action (StagingFrame entry))
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) : Ensures (branchCmp site value lhs rhs : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.hiddenClock64 site)
  have hpeek (kind : Worker) (pid : PeerId) : Ensures (peekQueuedUnit kind pid : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.peekQueuedUnit kind pid)
  have hqueue (kind : Worker) (pid : PeerId) : Ensures (recordQueued kind pid : WG.M Unit) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.recordQueued kind pid)
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run; cases run
  have hreadPeer (pid : PeerId) : Ensures (getPeer pid) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid (StagingFrame entry)) g a r f b pre run).1
  have hreadDev : Ensures getDev (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hreadKey (id : KeypairId) : Ensures (getKeypair id) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    unfold getKeypair
    refine ensures_bind _ _ hreadDev ?_
    intro d
    split
    · exact hpure _
    · exact hstop _
  have hmodify (f : Device → Device)
      (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d)
      (peers : ∀ d, (f d).peers = d.peers) :
      Ensures (modifyDev f) (StagingFrame entry) (fun _ => StagingFrame entry) :=
    staging_modifyDev entry f same peers
  have hindex (owner : IndexOwner) :
      Ensures (liftM (indexRemove owner) : WG.M Unit) (StagingFrame entry)
        (fun _ => StagingFrame entry) := staging_indexRemove entry owner
  have hif {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
      (hy : Ensures yes (StagingFrame entry) (fun _ => (StagingFrame entry)))
      (hn : Ensures no (StagingFrame entry) (fun _ => (StagingFrame entry))) :
      Ensures (if p then yes else no) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by split <;> assumption
  rw [← Config.sendStaged_source]
  unfold Config.stagedSource
  repeat' first
    | with_reducible exact hpure _
    | with_reducible exact hbranch _ _
    | with_reducible exact hreadPeer _
    | with_reducible exact staging_setPeer entry _ _ (by assumption)
    | with_reducible exact keypairGet_staging _ entry
    | with_reducible exact (ensures_iff _ _ _).mpr (stagedAfterGet_staging _ _ _ entry)
    | (staging_getPeer_bind; refine staging_read_bind entry _ _ _ ?_; intro p tag)
    | (with_reducible refine ensures_bind (Q := fun _ => (StagingFrame entry)) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
theorem sendKeepalive_staging (pid : PeerId) (entry : WGWorld) :
    Ensures (sendKeepalive pid) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action (StagingFrame entry))
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) : Ensures (branchCmp site value lhs rhs : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.hiddenClock64 site)
  have hpeek (kind : Worker) (pid : PeerId) : Ensures (peekQueuedUnit kind pid : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.peekQueuedUnit kind pid)
  have hqueue (kind : Worker) (pid : PeerId) : Ensures (recordQueued kind pid : WG.M Unit) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.recordQueued kind pid)
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run; cases run
  have hreadPeer (pid : PeerId) : Ensures (getPeer pid) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid (StagingFrame entry)) g a r f b pre run).1
  have hreadDev : Ensures getDev (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    intro g a r f b pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hreadKey (id : KeypairId) : Ensures (getKeypair id) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by
    unfold getKeypair
    refine ensures_bind _ _ hreadDev ?_
    intro d
    split
    · exact hpure _
    · exact hstop _
  have hmodify (f : Device → Device)
      (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d)
      (peers : ∀ d, (f d).peers = d.peers) :
      Ensures (modifyDev f) (StagingFrame entry) (fun _ => StagingFrame entry) :=
    staging_modifyDev entry f same peers
  have hindex (owner : IndexOwner) :
      Ensures (liftM (indexRemove owner) : WG.M Unit) (StagingFrame entry)
        (fun _ => StagingFrame entry) := staging_indexRemove entry owner
  have hif {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
      (hy : Ensures yes (StagingFrame entry) (fun _ => (StagingFrame entry)))
      (hn : Ensures no (StagingFrame entry) (fun _ => (StagingFrame entry))) :
      Ensures (if p then yes else no) (StagingFrame entry) (fun _ => (StagingFrame entry)) := by split <;> assumption
  have halloc (site : AllocSite) : Ensures (hiddenAlloc site : WG.M Bool) (StagingFrame entry) (fun _ => (StagingFrame entry)) :=
    hambient (AmbientM.hiddenAlloc site)
  unfold sendKeepalive
  repeat' first
    | with_reducible exact hpure _
    | with_reducible exact hbranch _ _
    | with_reducible exact hreadPeer _
    | with_reducible exact hreadDev
    | with_reducible exact halloc _
    | with_reducible exact staging_setPeer entry _ _ (by assumption)
    | with_reducible exact sendStagedPackets_staging _ entry
    | (staging_getPeer_bind; refine staging_read_bind entry _ _ _ ?_; intro p tag)
    | (with_reducible refine ensures_bind (Q := fun _ => (StagingFrame entry)) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)


theorem keypairPut_tables (key : Option KeypairId) (now : Bool) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ keypairPut key now ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (fun entry =>
    (ensures_iff _ _ _).mpr (keypairPut_staging key now entry)))

theorem sendQueuedHandshakeInitiation_tables (pid : PeerId) (retry : Bool) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ sendQueuedHandshakeInitiation pid retry ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (fun entry =>
    (ensures_iff _ _ _).mpr (sendQueuedHandshakeInitiation_staging pid retry entry)))

theorem enqueuePerPeerTx_tables (item : List SkbId) (state : PacketState) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ enqueuePerPeerTx item state ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (fun entry =>
    (ensures_iff _ _ _).mpr (enqueuePerPeerTx_staging item state entry)))

theorem createData_tables (pid : PeerId) (item : List SkbId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ createData pid item ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (fun entry =>
    (ensures_iff _ _ _).mpr (createData_staging pid item entry)))

theorem stagedFallback_tables (pid : PeerId) (packets : List Packet) (key : Option KeypairId) (invalid : Bool) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ Config.stagedFallback pid packets key invalid ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (fun entry =>
    (ensures_iff _ _ _).mpr (stagedFallback_staging pid packets key invalid entry)))

theorem stagedAfterGet_tables (pid : PeerId) (packets : List Packet) (key : Option KeypairId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ Config.stagedAfterGet pid packets key ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (fun entry =>
    (ensures_iff _ _ _).mpr (stagedAfterGet_staging pid packets key entry)))

theorem sendStagedPackets_tables (pid : PeerId) :
    Ensures (sendStagedPackets pid) TablesSafeWG (fun _ => TablesSafeWG) :=
  staging_tables _ (sendStagedPackets_staging pid)

theorem sendKeepalive_tables (pid : PeerId) :
    Ensures (sendKeepalive pid) TablesSafeWG (fun _ => TablesSafeWG) :=
  staging_tables _ (sendKeepalive_staging pid)


/-- Staging may delete a peer through its actual release paths. Every surviving
tag is retained, with no table-safety or reference-count precondition. -/
theorem sendStagedPackets_tags_retained (pid : PeerId) :
    ∀ g ambient result final after,
      (((sendStagedPackets pid).run g).run ambient = .ok ((result,final),after)) →
      TagsRetained (responseTagMap g.dev) (responseTagMap final.dev) :=
  staging_tags _ (sendStagedPackets_staging pid)

/-- The original keepalive wrapper performs allocation and staging, and does
not silently create a handshake state edge. Normal deletion remains allowed. -/
theorem sendKeepalive_tags_retained (pid : PeerId) :
    ∀ g ambient result final after,
      (((sendKeepalive pid).run g).run ambient = .ok ((result,final),after)) →
      TagsRetained (responseTagMap g.dev) (responseTagMap final.dev) :=
  staging_tags _ (sendKeepalive_staging pid)

end Leanux.Proofs.WG.Index
