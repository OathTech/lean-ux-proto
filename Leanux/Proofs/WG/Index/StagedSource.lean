import Leanux.Proofs.WG.Index.StagedFrames
import Leanux.Proofs.WG.Index.SendSource
import Leanux.Proofs.WG.Queues.DecryptCarrier

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do
namespace StagingRich

theorem newTxSkbs_rich (packets : List DataPacket) (entry : WGWorld) :
    Ensures (packets.mapM newTxSkb) (Frame entry) (fun _ => Frame entry) := by
  have loop (xs : List DataPacket) (acc : List SkbId) :
      Ensures (List.mapM.loop newTxSkb xs acc) (Frame entry) (fun _ => Frame entry) := by
    induction xs generalizing acc with
    | nil => intro _ _ _ _ _ pre run; cases run; exact pre
    | cons x xs ih =>
      unfold List.mapM.loop
      exact ensures_bind _ _ (newTxSkb_rich x entry) (fun id => ih (id::acc))
  exact loop packets []

theorem enqueuePerDeviceAndPeer_rich (pid : PeerId) (item : List SkbId) (entry : WGWorld) :
    Ensures (enqueuePerDeviceAndPeer pid item) (Frame entry) (fun _ => Frame entry) := by
  let P := Frame entry
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro _ _ _ _ _ pre run; cases run; exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have hdev : Ensures getDev P (fun _ => P) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [getDev,device,invariant,AmbientM.invariant] at run; cases run
    | some d => simp [getDev,device] at run; obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run; exact pre
  have hcpu (last : Int) : Ensures (cpumaskNextOnlineFrom last) P (fun _ => P) := by
    unfold cpumaskNextOnlineFrom
    refine ensures_bind _ _ (hbranch _ _) ?_
    intro wrap
    cases wrap <;> exact hpure _
  have hqueue : Ensures (queueDeviceWork .encryptWorker : WG.M Unit) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.queueDeviceWork .encryptWorker) P)
  unfold enqueuePerDeviceAndPeer
  cases first : item.head? with
  | none => intro _ _ _ _ _ _ run; cases run
  | some id =>
    refine ensures_bind _ _ (setTxSkb_rich id _ entry) ?_
    intro _
    refine readPeer entry pid _ _ ?_
    intro peer tag
    refine ensures_bind _ _ (hbranch _ _) ?_
    intro full
    cases full with
    | true => exact hpure _
    | false =>
      refine ensures_bind _ _ (setPeer_rich entry pid _ tag) ?_
      intro _
      refine ensures_bind _ _ hdev ?_
      intro device
      refine ensures_bind _ _ (hcpu _) ?_
      intro cpu
      refine ensures_bind _ _ (modifyDev_rich entry _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)) ?_
      intro _
      refine ensures_bind _ _ (hbranch _ _) ?_
      intro full
      cases full with
      | true => exact hpure _
      | false =>
        refine ensures_bind _ _ hqueue ?_
        intro _
        exact ensures_bind _ _ (modifyDev_rich entry _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
          (fun _ => hpure _)

-- Retained limits for the six existing staging traversals.
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
theorem sendQueuedHandshakeInitiation_rich (pid : PeerId) (retry : Bool) (entry : WGWorld) :
    ⦃fun g => ⌜(Frame entry) g⌝⦄ sendQueuedHandshakeInitiation pid retry ⦃⇓? _ g => ⌜(Frame entry) g⌝⦄ := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) (Frame entry) (fun _ => (Frame entry)) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action (Frame entry))
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) : Ensures (branchCmp site value lhs rhs : WG.M Bool) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.hiddenClock64 site)
  have hpeek (kind : Worker) (pid : PeerId) : Ensures (peekQueuedUnit kind pid : WG.M Bool) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.peekQueuedUnit kind pid)
  have hqueue (kind : Worker) (pid : PeerId) : Ensures (recordQueued kind pid : WG.M Unit) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.recordQueued kind pid)
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run; cases run
  have hreadPeer (pid : PeerId) : Ensures (getPeer pid) (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid (Frame entry)) g a r f b pre run).1
  have hreadDev : Ensures getDev (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hreadKey (id : KeypairId) : Ensures (getKeypair id) (Frame entry) (fun _ => (Frame entry)) := by
    unfold getKeypair
    refine ensures_bind _ _ hreadDev ?_
    intro d
    split
    · exact hpure _
    · exact hstop _
  have hmodify (f : Device → Device)
      (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d)
      (peers : ∀ d, (f d).peers = d.peers)
      (keys : ∀ d, (f d).keypairs = d.keypairs) :
      Ensures (modifyDev f) (Frame entry) (fun _ => Frame entry) :=
    modifyDev_rich entry f same peers keys
  have hif {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
      (hy : Ensures yes (Frame entry) (fun _ => (Frame entry)))
      (hn : Ensures no (Frame entry) (fun _ => (Frame entry))) :
      Ensures (if p then yes else no) (Frame entry) (fun _ => (Frame entry)) := by split <;> assumption
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
    | with_reducible exact hmodify _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    | with_reducible exact setPeer_rich entry _ _ (by assumption)
    | with_reducible exact setKey entry _ _ (by assumption)
    | with_reducible exact peerGet_rich _ entry
    | with_reducible exact peerPut_rich entry _
    | (staging_getPeer_bind; refine readPeer entry _ _ _ ?_; intro p tag)
    | (rich_getKey_bind; refine readKey entry _ _ _ ?_; intro key keyCell)
    | (with_reducible refine ensures_bind (Q := fun _ => (Frame entry)) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | split

theorem enqueuePerPeerTx_rich (item : List SkbId) (state : PacketState) (entry : WGWorld) :
    ⦃fun g => ⌜(Frame entry) g⌝⦄ enqueuePerPeerTx item state ⦃⇓? _ g => ⌜(Frame entry) g⌝⦄ := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) (Frame entry) (fun _ => (Frame entry)) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action (Frame entry))
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) : Ensures (branchCmp site value lhs rhs : WG.M Bool) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.hiddenClock64 site)
  have hpeek (kind : Worker) (pid : PeerId) : Ensures (peekQueuedUnit kind pid : WG.M Bool) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.peekQueuedUnit kind pid)
  have hqueue (kind : Worker) (pid : PeerId) : Ensures (recordQueued kind pid : WG.M Unit) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.recordQueued kind pid)
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run; cases run
  have hreadPeer (pid : PeerId) : Ensures (getPeer pid) (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid (Frame entry)) g a r f b pre run).1
  have hreadDev : Ensures getDev (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hreadKey (id : KeypairId) : Ensures (getKeypair id) (Frame entry) (fun _ => (Frame entry)) := by
    unfold getKeypair
    refine ensures_bind _ _ hreadDev ?_
    intro d
    split
    · exact hpure _
    · exact hstop _
  have hmodify (f : Device → Device)
      (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d)
      (peers : ∀ d, (f d).peers = d.peers)
      (keys : ∀ d, (f d).keypairs = d.keypairs) :
      Ensures (modifyDev f) (Frame entry) (fun _ => Frame entry) :=
    modifyDev_rich entry f same peers keys
  have hif {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
      (hy : Ensures yes (Frame entry) (fun _ => (Frame entry)))
      (hn : Ensures no (Frame entry) (fun _ => (Frame entry))) :
      Ensures (if p then yes else no) (Frame entry) (fun _ => (Frame entry)) := by split <;> assumption
  have hword (owner : IndexOwner) : Ensures owner.peerDeref (Frame entry) (fun _ => (Frame entry)) := by
    unfold IndexOwner.peerDeref
    have hr : Ensures owner.peerWord (Frame entry) (fun _ => (Frame entry)) := by
      cases owner with
      | handshake pid => exact ensures_bind _ _ (hreadPeer pid) (fun p => hpure p.handshakeEntryPeer)
      | keypair kid => exact ensures_bind _ _ (hreadKey kid) (fun k => hpure k.peer)
    refine ensures_bind _ _ hr ?_
    intro word
    cases word with
    | none => exact hambient (AmbientM.unsupported _)
    | some pid => exact hpure pid
  have hreadTx (id : SkbId) :
      Ensures (getTxSkb id) (Frame entry) (fun _ => Frame entry) :=
    liftSkb_rich (SkbStore.getTx id) entry
  have hloop {α β : Type} (xs : List α) (state : β) (step : α → β → WG.M (ForInStep β))
      (preserve : ∀ x state, Ensures (step x state) (Frame entry) (fun _ => (Frame entry))) :
      Ensures (forIn xs state step) (Frame entry) (fun _ => (Frame entry)) := by
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
    | with_reducible exact hmodify _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    | with_reducible exact setPeer_rich entry _ _ (by assumption)
    | with_reducible exact setKey entry _ _ (by assumption)
    | with_reducible exact peerGet_rich _ entry
    | with_reducible exact peerPut_rich entry _
    | with_reducible exact setTxSkb_rich _ _ entry
    | with_reducible exact freeTxSkb_rich _ entry
    | with_reducible exact cpumaskChooseOnline_rich _ entry
    | with_reducible exact enqueuePerDeviceAndPeer_rich _ _ entry
    | with_reducible exact release entry _ _
    | with_reducible exact (ensures_iff _ _ _).mpr (sendQueuedHandshakeInitiation_rich _ _ entry)
    | (staging_getPeer_bind; refine readPeer entry _ _ _ ?_; intro p tag)
    | (rich_getKey_bind; refine readKey entry _ _ _ ?_; intro key keyCell)
    | (with_reducible refine ensures_bind (Q := fun _ => (Frame entry)) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | (with_reducible refine hloop _ _ _ ?_; intro _ _)
    | split

theorem createData_rich (pid : PeerId) (item : List SkbId) (entry : WGWorld) :
    ⦃fun g => ⌜(Frame entry) g⌝⦄ createData pid item ⦃⇓? _ g => ⌜(Frame entry) g⌝⦄ := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) (Frame entry) (fun _ => (Frame entry)) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action (Frame entry))
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) : Ensures (branchCmp site value lhs rhs : WG.M Bool) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.hiddenClock64 site)
  have hpeek (kind : Worker) (pid : PeerId) : Ensures (peekQueuedUnit kind pid : WG.M Bool) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.peekQueuedUnit kind pid)
  have hqueue (kind : Worker) (pid : PeerId) : Ensures (recordQueued kind pid : WG.M Unit) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.recordQueued kind pid)
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run; cases run
  have hreadPeer (pid : PeerId) : Ensures (getPeer pid) (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid (Frame entry)) g a r f b pre run).1
  have hreadDev : Ensures getDev (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hreadKey (id : KeypairId) : Ensures (getKeypair id) (Frame entry) (fun _ => (Frame entry)) := by
    unfold getKeypair
    refine ensures_bind _ _ hreadDev ?_
    intro d
    split
    · exact hpure _
    · exact hstop _
  have hmodify (f : Device → Device)
      (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d)
      (peers : ∀ d, (f d).peers = d.peers)
      (keys : ∀ d, (f d).keypairs = d.keypairs) :
      Ensures (modifyDev f) (Frame entry) (fun _ => Frame entry) :=
    modifyDev_rich entry f same peers keys
  have hif {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
      (hy : Ensures yes (Frame entry) (fun _ => (Frame entry)))
      (hn : Ensures no (Frame entry) (fun _ => (Frame entry))) :
      Ensures (if p then yes else no) (Frame entry) (fun _ => (Frame entry)) := by split <;> assumption
  have hword (owner : IndexOwner) : Ensures owner.peerDeref (Frame entry) (fun _ => (Frame entry)) := by
    unfold IndexOwner.peerDeref
    have hr : Ensures owner.peerWord (Frame entry) (fun _ => (Frame entry)) := by
      cases owner with
      | handshake pid => exact ensures_bind _ _ (hreadPeer pid) (fun p => hpure p.handshakeEntryPeer)
      | keypair kid => exact ensures_bind _ _ (hreadKey kid) (fun k => hpure k.peer)
    refine ensures_bind _ _ hr ?_
    intro word
    cases word with
    | none => exact hambient (AmbientM.unsupported _)
    | some pid => exact hpure pid
  have hreadTx (id : SkbId) :
      Ensures (getTxSkb id) (Frame entry) (fun _ => Frame entry) :=
    liftSkb_rich (SkbStore.getTx id) entry
  have hloop {α β : Type} (xs : List α) (state : β) (step : α → β → WG.M (ForInStep β))
      (preserve : ∀ x state, Ensures (step x state) (Frame entry) (fun _ => (Frame entry))) :
      Ensures (forIn xs state step) (Frame entry) (fun _ => (Frame entry)) := by
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
    | with_reducible exact hmodify _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    | with_reducible exact setPeer_rich entry _ _ (by assumption)
    | with_reducible exact setKey entry _ _ (by assumption)
    | with_reducible exact peerGet_rich _ entry
    | with_reducible exact peerPut_rich entry _
    | with_reducible exact setTxSkb_rich _ _ entry
    | with_reducible exact freeTxSkb_rich _ entry
    | with_reducible exact cpumaskChooseOnline_rich _ entry
    | with_reducible exact enqueuePerDeviceAndPeer_rich _ _ entry
    | with_reducible exact release entry _ _
    | with_reducible exact (ensures_iff _ _ _).mpr (sendQueuedHandshakeInitiation_rich _ _ entry)
    | with_reducible exact (ensures_iff _ _ _).mpr (enqueuePerPeerTx_rich _ _ entry)
    | (staging_getPeer_bind; refine readPeer entry _ _ _ ?_; intro p tag)
    | (rich_getKey_bind; refine readKey entry _ _ _ ?_; intro key keyCell)
    | (with_reducible refine ensures_bind (Q := fun _ => (Frame entry)) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | (with_reducible refine hloop _ _ _ ?_; intro _ _)
    | split

theorem stagedFallback_rich (pid : PeerId) (packets : List Packet) (key : Option KeypairId) (invalid : Bool) (entry : WGWorld) :
    ⦃fun g => ⌜(Frame entry) g⌝⦄ Config.stagedFallback pid packets key invalid ⦃⇓? _ g => ⌜(Frame entry) g⌝⦄ := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) (Frame entry) (fun _ => (Frame entry)) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action (Frame entry))
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) : Ensures (branchCmp site value lhs rhs : WG.M Bool) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.hiddenClock64 site)
  have hpeek (kind : Worker) (pid : PeerId) : Ensures (peekQueuedUnit kind pid : WG.M Bool) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.peekQueuedUnit kind pid)
  have hqueue (kind : Worker) (pid : PeerId) : Ensures (recordQueued kind pid : WG.M Unit) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.recordQueued kind pid)
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run; cases run
  have hreadPeer (pid : PeerId) : Ensures (getPeer pid) (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid (Frame entry)) g a r f b pre run).1
  have hreadDev : Ensures getDev (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hreadKey (id : KeypairId) : Ensures (getKeypair id) (Frame entry) (fun _ => (Frame entry)) := by
    unfold getKeypair
    refine ensures_bind _ _ hreadDev ?_
    intro d
    split
    · exact hpure _
    · exact hstop _
  have hmodify (f : Device → Device)
      (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d)
      (peers : ∀ d, (f d).peers = d.peers)
      (keys : ∀ d, (f d).keypairs = d.keypairs) :
      Ensures (modifyDev f) (Frame entry) (fun _ => Frame entry) :=
    modifyDev_rich entry f same peers keys
  have hif {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
      (hy : Ensures yes (Frame entry) (fun _ => (Frame entry)))
      (hn : Ensures no (Frame entry) (fun _ => (Frame entry))) :
      Ensures (if p then yes else no) (Frame entry) (fun _ => (Frame entry)) := by split <;> assumption
  have hword (owner : IndexOwner) : Ensures owner.peerDeref (Frame entry) (fun _ => (Frame entry)) := by
    unfold IndexOwner.peerDeref
    have hr : Ensures owner.peerWord (Frame entry) (fun _ => (Frame entry)) := by
      cases owner with
      | handshake pid => exact ensures_bind _ _ (hreadPeer pid) (fun p => hpure p.handshakeEntryPeer)
      | keypair kid => exact ensures_bind _ _ (hreadKey kid) (fun k => hpure k.peer)
    refine ensures_bind _ _ hr ?_
    intro word
    cases word with
    | none => exact hambient (AmbientM.unsupported _)
    | some pid => exact hpure pid
  have hreadTx (id : SkbId) :
      Ensures (getTxSkb id) (Frame entry) (fun _ => Frame entry) :=
    liftSkb_rich (SkbStore.getTx id) entry
  have hloop {α β : Type} (xs : List α) (state : β) (step : α → β → WG.M (ForInStep β))
      (preserve : ∀ x state, Ensures (step x state) (Frame entry) (fun _ => (Frame entry))) :
      Ensures (forIn xs state step) (Frame entry) (fun _ => (Frame entry)) := by
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
    | with_reducible exact hmodify _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    | with_reducible exact setPeer_rich entry _ _ (by assumption)
    | with_reducible exact setKey entry _ _ (by assumption)
    | with_reducible exact peerGet_rich _ entry
    | with_reducible exact peerPut_rich entry _
    | with_reducible exact setTxSkb_rich _ _ entry
    | with_reducible exact freeTxSkb_rich _ entry
    | with_reducible exact cpumaskChooseOnline_rich _ entry
    | with_reducible exact enqueuePerDeviceAndPeer_rich _ _ entry
    | with_reducible exact release entry _ _
    | with_reducible exact (ensures_iff _ _ _).mpr (sendQueuedHandshakeInitiation_rich _ _ entry)
    | (staging_getPeer_bind; refine readPeer entry _ _ _ ?_; intro p tag)
    | (rich_getKey_bind; refine readKey entry _ _ _ ?_; intro key keyCell)
    | (with_reducible refine ensures_bind (Q := fun _ => (Frame entry)) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | (with_reducible refine hloop _ _ _ ?_; intro _ _)
    | split

theorem stagedAfterGet_rich (pid : PeerId) (packets : List Packet) (key : Option KeypairId) (entry : WGWorld) :
    ⦃fun g => ⌜(Frame entry) g⌝⦄ Config.stagedAfterGet pid packets key ⦃⇓? _ g => ⌜(Frame entry) g⌝⦄ := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) (Frame entry) (fun _ => (Frame entry)) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action (Frame entry))
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) : Ensures (branchCmp site value lhs rhs : WG.M Bool) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.hiddenClock64 site)
  have hpeek (kind : Worker) (pid : PeerId) : Ensures (peekQueuedUnit kind pid : WG.M Bool) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.peekQueuedUnit kind pid)
  have hqueue (kind : Worker) (pid : PeerId) : Ensures (recordQueued kind pid : WG.M Unit) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.recordQueued kind pid)
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run; cases run
  have hreadPeer (pid : PeerId) : Ensures (getPeer pid) (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid (Frame entry)) g a r f b pre run).1
  have hreadDev : Ensures getDev (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hreadKey (id : KeypairId) : Ensures (getKeypair id) (Frame entry) (fun _ => (Frame entry)) := by
    unfold getKeypair
    refine ensures_bind _ _ hreadDev ?_
    intro d
    split
    · exact hpure _
    · exact hstop _
  have hmodify (f : Device → Device)
      (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d)
      (peers : ∀ d, (f d).peers = d.peers)
      (keys : ∀ d, (f d).keypairs = d.keypairs) :
      Ensures (modifyDev f) (Frame entry) (fun _ => Frame entry) :=
    modifyDev_rich entry f same peers keys
  have hif {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
      (hy : Ensures yes (Frame entry) (fun _ => (Frame entry)))
      (hn : Ensures no (Frame entry) (fun _ => (Frame entry))) :
      Ensures (if p then yes else no) (Frame entry) (fun _ => (Frame entry)) := by split <;> assumption
  have hword (owner : IndexOwner) : Ensures owner.peerDeref (Frame entry) (fun _ => (Frame entry)) := by
    unfold IndexOwner.peerDeref
    have hr : Ensures owner.peerWord (Frame entry) (fun _ => (Frame entry)) := by
      cases owner with
      | handshake pid => exact ensures_bind _ _ (hreadPeer pid) (fun p => hpure p.handshakeEntryPeer)
      | keypair kid => exact ensures_bind _ _ (hreadKey kid) (fun k => hpure k.peer)
    refine ensures_bind _ _ hr ?_
    intro word
    cases word with
    | none => exact hambient (AmbientM.unsupported _)
    | some pid => exact hpure pid
  have hreadTx (id : SkbId) :
      Ensures (getTxSkb id) (Frame entry) (fun _ => Frame entry) :=
    liftSkb_rich (SkbStore.getTx id) entry
  have hloop {α β : Type} (xs : List α) (state : β) (step : α → β → WG.M (ForInStep β))
      (preserve : ∀ x state, Ensures (step x state) (Frame entry) (fun _ => (Frame entry))) :
      Ensures (forIn xs state step) (Frame entry) (fun _ => (Frame entry)) := by
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
    | with_reducible exact hmodify _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    | with_reducible exact setPeer_rich entry _ _ (by assumption)
    | with_reducible exact setKey entry _ _ (by assumption)
    | with_reducible exact peerGet_rich _ entry
    | with_reducible exact peerPut_rich entry _
    | with_reducible exact setTxSkb_rich _ _ entry
    | with_reducible exact freeTxSkb_rich _ entry
    | with_reducible exact cpumaskChooseOnline_rich _ entry
    | with_reducible exact enqueuePerDeviceAndPeer_rich _ _ entry
    | with_reducible exact release entry _ _
    | with_reducible exact (ensures_iff _ _ _).mpr (sendQueuedHandshakeInitiation_rich _ _ entry)
    | with_reducible exact (ensures_iff _ _ _).mpr (stagedFallback_rich _ _ _ _ entry)
    | with_reducible exact (ensures_iff _ _ _).mpr (ipTunnelEcnEncap_wg_variant (Frame entry) _)
    | with_reducible exact newTxSkbs_rich _ entry
    | with_reducible exact (ensures_iff _ _ _).mpr (createData_rich _ _ entry)
    | (staging_getPeer_bind; refine readPeer entry _ _ _ ?_; intro p tag)
    | (rich_getKey_bind; refine readKey entry _ _ _ ?_; intro key keyCell)
    | (with_reducible refine ensures_bind (Q := fun _ => (Frame entry)) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | (with_reducible refine hloop _ _ _ ?_; intro _ _)
    | split

theorem sendStagedPackets_rich (pid : PeerId) (entry : WGWorld) :
    Ensures (sendStagedPackets pid) (Frame entry) (fun _ => (Frame entry)) := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) (Frame entry) (fun _ => (Frame entry)) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action (Frame entry))
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) : Ensures (branchCmp site value lhs rhs : WG.M Bool) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.hiddenClock64 site)
  have hpeek (kind : Worker) (pid : PeerId) : Ensures (peekQueuedUnit kind pid : WG.M Bool) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.peekQueuedUnit kind pid)
  have hqueue (kind : Worker) (pid : PeerId) : Ensures (recordQueued kind pid : WG.M Unit) (Frame entry) (fun _ => (Frame entry)) :=
    hambient (AmbientM.recordQueued kind pid)
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run; cases run
  have hreadPeer (pid : PeerId) : Ensures (getPeer pid) (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid (Frame entry)) g a r f b pre run).1
  have hreadDev : Ensures getDev (Frame entry) (fun _ => (Frame entry)) := by
    intro g a r f b pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hreadKey (id : KeypairId) : Ensures (getKeypair id) (Frame entry) (fun _ => (Frame entry)) := by
    unfold getKeypair
    refine ensures_bind _ _ hreadDev ?_
    intro d
    split
    · exact hpure _
    · exact hstop _
  have hmodify (f : Device → Device)
      (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d)
      (peers : ∀ d, (f d).peers = d.peers)
      (keys : ∀ d, (f d).keypairs = d.keypairs) :
      Ensures (modifyDev f) (Frame entry) (fun _ => Frame entry) :=
    modifyDev_rich entry f same peers keys
  have hif {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
      (hy : Ensures yes (Frame entry) (fun _ => (Frame entry)))
      (hn : Ensures no (Frame entry) (fun _ => (Frame entry))) :
      Ensures (if p then yes else no) (Frame entry) (fun _ => (Frame entry)) := by split <;> assumption
  rw [← Config.sendStaged_source]
  unfold Config.stagedSource
  repeat' first
    | with_reducible exact hpure _
    | with_reducible exact hbranch _ _
    | with_reducible exact hreadPeer _
    | with_reducible exact setPeer_rich entry _ _ (by assumption)
    | with_reducible exact keypairGet_rich _ entry
    | with_reducible exact (ensures_iff _ _ _).mpr (stagedAfterGet_rich _ _ _ entry)
    | (staging_getPeer_bind; refine readPeer entry _ _ _ ?_; intro p tag)
    | (rich_getKey_bind; refine readKey entry _ _ _ ?_; intro key keyCell)
    | (with_reducible refine ensures_bind (Q := fun _ => (Frame entry)) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)

set_option maxHeartbeats 200000
set_option maxRecDepth 1000
open Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem keepalive_rule (pid : PeerId) (P Q : WGWorld → Prop)
    (returns : ∀g, P g → Q g)
    (staged : Ensures (sendStagedPackets pid) P (fun _ => Q))
    (write : ∀g d p mtu, g.dev = some d → d.peers[pid]? = some p → P g →
      P {g with dev := some {d with peers := d.peers.insert pid ({p with staged := p.staged ++ [{mtu := mtu}]})}}) :
    Ensures (sendKeepalive pid) P (fun _ => Q) := by
  have ambient_state {α : Type} (action : AmbientM α) (g f : WGWorld)
      (a b : Ambient) (r : α)
      (run : (((monadLift action : WG.M α)).run g).run a = .ok ((r,f),b)) : f = g :=
    (hoare_iff_run_ambient _ _ _).mp (hoare_liftAmbient action (· = g)) g a r f b rfl run
  intro g a r f b pre run
  unfold sendKeepalive at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,read,ar,getter,run⟩ := run
  obtain ⟨same,time,d,hd,hp⟩ := getPeer_normal pid g read p a ar getter
  subst read
  subst ar
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨empty,guarded,ag,guard,run⟩ := run
  have same := ambient_state (AmbientM.branch .keepaliveStagedEmpty p.staged.isEmpty) g guarded a ag empty guard
  subst guarded
  cases empty with
  | false =>
    simp only [Bool.false_eq_true,ite_false] at run
    exact staged g ag r f b pre run
  | true =>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨allocated,read,aa,alloc,failed,guarded,af,guard,run⟩ := run
    have same := ambient_state (AmbientM.hiddenAlloc .keepaliveSkb) g read ag aa allocated alloc
    subst read
    have same := ambient_state (AmbientM.branch .keepaliveNoMem (!allocated)) g guarded aa af failed guard
    subst guarded
    cases failed with
    | true =>
      simp only [ite_true] at run
      cases run
      exact returns g pre
    | false =>
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at run
      obtain ⟨dev,read,ad,getter,u,prepared,ap,changed,run⟩ := run
      obtain ⟨same,time,_⟩ := DecryptCarrier.getDev_current af ad getter
      subst read
      subst ad
      simp only [WG.setPeer,WG.modifyDev] at changed
      cases changed
      exact staged _ af r f b (write g d p dev.mtu hd hp pre)
        (by simpa only [hd,Option.map_some] using run)

theorem sendKeepalive_rich (pid : PeerId) (entry : WGWorld) :
    Ensures (sendKeepalive pid) (Frame entry) (fun _ => Frame entry) := by
  apply keepalive_rule pid _ _ (fun _ h => h) (sendStagedPackets_rich pid entry)
  intro g d p mtu hd hp pre
  have cell : peerMap entry pid = some (PeerCell p) :=
    pre.peers pid _ (by simp [peerMap,hd,hp])
  have write := setPeer_rich entry pid {p with staged := p.staged ++ [{mtu := mtu}]} cell
    g ({env := fun _ _ => false,timing := ⟨0,0⟩} : Ambient) () _ ({env := fun _ _ => false,timing := ⟨0,0⟩} : Ambient) pre rfl
  simpa only [hd,Option.map_some] using write

end StagingRich

theorem keypairPut_staging (key : Option KeypairId) (now : Bool) (entry : WGWorld) :
    ⦃fun g => ⌜(StagingFrame entry) g⌝⦄ keypairPut key now ⦃⇓? _ g => ⌜(StagingFrame entry) g⌝⦄ := (ensures_iff _ _ _).mp (StagingRich.forget _ (fun e => StagingRich.release e key now) entry)

theorem sendQueuedHandshakeInitiation_staging (pid : PeerId) (retry : Bool) (entry : WGWorld) :
    ⦃fun g => ⌜(StagingFrame entry) g⌝⦄ sendQueuedHandshakeInitiation pid retry ⦃⇓? _ g => ⌜(StagingFrame entry) g⌝⦄ := (ensures_iff _ _ _).mp (StagingRich.forget _ (fun e => (ensures_iff _ _ _).mpr (StagingRich.sendQueuedHandshakeInitiation_rich pid retry e)) entry)

theorem enqueuePerPeerTx_staging (item : List SkbId) (state : PacketState) (entry : WGWorld) :
    ⦃fun g => ⌜(StagingFrame entry) g⌝⦄ enqueuePerPeerTx item state ⦃⇓? _ g => ⌜(StagingFrame entry) g⌝⦄ := (ensures_iff _ _ _).mp (StagingRich.forget _ (fun e => (ensures_iff _ _ _).mpr (StagingRich.enqueuePerPeerTx_rich item state e)) entry)

theorem createData_staging (pid : PeerId) (item : List SkbId) (entry : WGWorld) :
    ⦃fun g => ⌜(StagingFrame entry) g⌝⦄ createData pid item ⦃⇓? _ g => ⌜(StagingFrame entry) g⌝⦄ := (ensures_iff _ _ _).mp (StagingRich.forget _ (fun e => (ensures_iff _ _ _).mpr (StagingRich.createData_rich pid item e)) entry)

theorem stagedFallback_staging (pid : PeerId) (packets : List Packet) (key : Option KeypairId) (invalid : Bool) (entry : WGWorld) :
    ⦃fun g => ⌜(StagingFrame entry) g⌝⦄ Config.stagedFallback pid packets key invalid ⦃⇓? _ g => ⌜(StagingFrame entry) g⌝⦄ := (ensures_iff _ _ _).mp (StagingRich.forget _ (fun e => (ensures_iff _ _ _).mpr (StagingRich.stagedFallback_rich pid packets key invalid e)) entry)

theorem stagedAfterGet_staging (pid : PeerId) (packets : List Packet) (key : Option KeypairId) (entry : WGWorld) :
    ⦃fun g => ⌜(StagingFrame entry) g⌝⦄ Config.stagedAfterGet pid packets key ⦃⇓? _ g => ⌜(StagingFrame entry) g⌝⦄ := (ensures_iff _ _ _).mp (StagingRich.forget _ (fun e => (ensures_iff _ _ _).mpr (StagingRich.stagedAfterGet_rich pid packets key e)) entry)

theorem sendStagedPackets_staging (pid : PeerId) (entry : WGWorld) :
    Ensures (sendStagedPackets pid) (StagingFrame entry) (fun _ => (StagingFrame entry)) := (StagingRich.forget _ (fun e => (StagingRich.sendStagedPackets_rich pid e)) entry)

theorem sendKeepalive_staging (pid : PeerId) (entry : WGWorld) :
    Ensures (sendKeepalive pid) (StagingFrame entry) (fun _ => (StagingFrame entry)) := (StagingRich.forget _ (fun e => (StagingRich.sendKeepalive_rich pid e)) entry)

theorem newTxSkbs_staging (packets : List DataPacket) (entry : WGWorld) :
    Ensures (packets.mapM newTxSkb) (StagingFrame entry) (fun _ => StagingFrame entry) := StagingRich.forget _ (StagingRich.newTxSkbs_rich packets) entry

theorem enqueuePerDeviceAndPeer_staging (pid : PeerId) (item : List SkbId) (entry : WGWorld) :
    Ensures (enqueuePerDeviceAndPeer pid item) (StagingFrame entry) (fun _ => StagingFrame entry) := StagingRich.forget _ (StagingRich.enqueuePerDeviceAndPeer_rich pid item) entry

theorem newTxSkbs_tables (packets : List DataPacket) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ packets.mapM newTxSkb ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (newTxSkbs_staging packets))

theorem enqueuePerDeviceAndPeer_tables (pid : PeerId) (item : List SkbId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ enqueuePerDeviceAndPeer pid item ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (enqueuePerDeviceAndPeer_staging pid item))

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
