import Leanux.Proofs.WG.Index.StagedFrames
import Leanux.Proofs.WG.Index.SendSource
import Leanux.Proofs.WG.Queues.DecryptCarrier

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.StagingPreservation
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do
abbrev PeerImage := Nat × Option KeypairId × Option KeypairId × Option KeypairId ×
  Option PeerId × Nat × Bool × Option (Nat × Nat × Nat × Nat) × Key × Nat × Option Endpoint
/-- Primitive contracts for the one owned staging source proof. Cached peer/key
observations are supplied by reads and consumed by the original saved writes. -/
structure Contracts (P : WGWorld → Prop) where
  peer : PeerId → PeerImage → Prop
  key : KeypairId → (Option PeerId × Bool) → Prop
  readPeer : ∀ (pid : PeerId) {α : Type} (next : Peer → WG.M α) (Q : α → WGWorld → Prop),
    (∀ p, peer pid (StagingRich.PeerCell p) → Ensures (next p) P Q) →
    Ensures (getPeer pid >>= next) P Q
  readKey : ∀ (kid : KeypairId) {α : Type} (next : Keypair → WG.M α) (Q : α → WGWorld → Prop),
    (∀ k, key kid (StagingRich.KeyCell k) → Ensures (next k) P Q) →
    Ensures (getKeypair kid >>= next) P Q
  setPeer : ∀ pid p, peer pid (StagingRich.PeerCell p) →
    Ensures (WG.setPeer pid p) P (fun _=>P)
  setKey : ∀ kid k, key kid (StagingRich.KeyCell k) →
    Ensures (WG.setKeypair kid k) P (fun _=>P)
  modify : ∀ (f : Device → Device),
    (∀ d, TimerDiscipline.tableCursor (f d)=TimerDiscipline.tableCursor d) →
    (∀ d, (f d).peers=d.peers) → (∀ d, (f d).keypairs=d.keypairs) →
    (∀ d, TimerDiscipline.sendConfiguration (f d)=TimerDiscipline.sendConfiguration d) →
    Ensures (modifyDev f) P (fun _=>P)
  peerGet : ∀ pid, Ensures (WG.peerGet pid) P (fun _=>P)
  peerPut : ∀ pid, Ensures (WG.peerPut pid) P (fun _=>P)
  keyGet : ∀ kid, Ensures (keypairGet kid) P (fun _=>P)
  release : ∀ kid now, Ensures (keypairPut kid now) P (fun _=>P)
  skb : ∀ {α : Type} (action : SkbM α), Ensures (liftSkb action) P (fun _=>P)
  cpu : ∀ pid, Ensures (cpumaskChooseOnline pid) P (fun _=>P)
variable {P : WGWorld → Prop}

private theorem hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) P (fun _ => P) := by
  intro g a r f b pre run; cases run; exact pre

private theorem hambient {α : Type} (action : AmbientM α) :
    Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
  (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action P)

private theorem hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
  hambient (AmbientM.branch site value)

private theorem hcmp (site : Decision) (value : Bool) (lhs rhs : Int) : Ensures (branchCmp site value lhs rhs : WG.M Bool) P (fun _ => P) :=
  hambient (AmbientM.branchCmp site value lhs rhs)

private theorem hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) P (fun _ => P) :=
  hambient (AmbientM.hiddenClock64 site)

private theorem hpeek (kind : Worker) (pid : PeerId) : Ensures (peekQueuedUnit kind pid : WG.M Bool) P (fun _ => P) :=
  hambient (AmbientM.peekQueuedUnit kind pid)

private theorem hqueue (kind : Worker) (pid : PeerId) : Ensures (recordQueued kind pid : WG.M Unit) P (fun _ => P) :=
  hambient (AmbientM.recordQueued kind pid)

private theorem hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) P (fun _ => P) := by
  intro g a r f b pre run; cases run

private theorem hreadPeer (pid : PeerId) : Ensures (getPeer pid) P (fun _ => P) := by
  intro g a r f b pre run
  exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P) g a r f b pre run).1

private theorem hreadDev : Ensures getDev P (fun _ => P) := by
  intro g a r f b pre run
  cases hd : g.dev with
  | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
  | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre

private theorem hreadKey (id : KeypairId) : Ensures (getKeypair id) P (fun _ => P) := by
  unfold getKeypair
  refine ensures_bind _ _ hreadDev ?_
  intro d
  split
  · exact hpure _
  · exact hstop _

private theorem hif {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
    (hy : Ensures yes P (fun _ => P))
    (hn : Ensures no P (fun _ => P)) :
    Ensures (if p then yes else no) P (fun _ => P) := by split <;> assumption

private theorem hword (owner : IndexOwner) : Ensures owner.peerDeref P (fun _ => P) := by
  unfold IndexOwner.peerDeref
  have hr : Ensures owner.peerWord P (fun _ => P) := by
    cases owner with
    | handshake pid => exact ensures_bind _ _ (hreadPeer pid) (fun p => hpure p.handshakeEntryPeer)
    | keypair kid => exact ensures_bind _ _ (hreadKey kid) (fun k => hpure k.peer)
  refine ensures_bind _ _ hr ?_
  intro word
  cases word with
  | none => exact hambient (AmbientM.unsupported _)
  | some pid => exact hpure pid

private theorem hreadTx (c : Contracts P) (id : SkbId) :
    Ensures (getTxSkb id) P (fun _ => P) :=
  c.skb (SkbStore.getTx id)

private theorem hloop {α β : Type} (xs : List α) (state : β) (step : α → β → WG.M (ForInStep β))
    (preserve : ∀ x state, Ensures (step x state) P (fun _ => P)) :
    Ensures (forIn xs state step) P (fun _ => P) := by
  induction xs generalizing state with
  | nil => exact hpure _
  | cons x xs ih =>
    rw [List.forIn_cons]
    refine ensures_bind _ _ (preserve x state) ?_
    intro out
    cases out with
    | done v => exact hpure _
    | yield v => exact ih v

theorem setTx (c : Contracts P) (id : SkbId) (f : DataPacket → DataPacket) :
    Ensures (setTxSkb id f) P (fun _=>P) := c.skb (SkbStore.setTx id f)
theorem freeTx (c : Contracts P) (id : SkbId) :
    Ensures (freeTxSkb id) P (fun _=>P) := c.skb (SkbStore.freeTx id)

theorem newTxSkbs_rule (packets : List DataPacket) (c : Contracts P) :
    Ensures (packets.mapM newTxSkb) P (fun _ => P) := by
  have loop (xs : List DataPacket) (acc : List SkbId) :
      Ensures (List.mapM.loop newTxSkb xs acc) P (fun _ => P) := by
    induction xs generalizing acc with
    | nil => intro _ _ _ _ _ pre run; cases run; exact pre
    | cons x xs ih =>
      unfold List.mapM.loop
      exact ensures_bind _ _ (c.skb (SkbStore.newTx x)) (fun id => ih (id::acc))
  exact loop packets []

theorem enqueuePerDeviceAndPeer_rule (pid : PeerId) (item : List SkbId) (c : Contracts P) :
    Ensures (enqueuePerDeviceAndPeer pid item) P (fun _ => P) := by
  let P := P
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
    refine ensures_bind _ _ (c.skb (SkbStore.setTx id _)) ?_
    intro _
    refine c.readPeer pid _ _ ?_
    intro peer tag
    refine ensures_bind _ _ (hbranch _ _) ?_
    intro full
    cases full with
    | true => exact hpure _
    | false =>
      refine ensures_bind _ _ (c.setPeer pid _ tag) ?_
      intro _
      refine ensures_bind _ _ hdev ?_
      intro device
      refine ensures_bind _ _ (hcpu _) ?_
      intro cpu
      refine ensures_bind _ _ (c.modify _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)) ?_
      intro _
      refine ensures_bind _ _ (hbranch _ _) ?_
      intro full
      cases full with
      | true => exact hpure _
      | false =>
        refine ensures_bind _ _ hqueue ?_
        intro _
        exact ensures_bind _ _ (c.modify _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
          (fun _ => hpure _)

theorem sendQueuedHandshakeInitiation_rule (pid : PeerId) (retry : Bool) (c : Contracts P) :
    ⦃fun g => ⌜P g⌝⦄ sendQueuedHandshakeInitiation pid retry ⦃⇓? _ g => ⌜P g⌝⦄ := by
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
    | with_reducible exact c.modify _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    | with_reducible exact c.setPeer _ _ (by assumption)
    | with_reducible exact c.setKey _ _ (by assumption)
    | with_reducible exact c.peerGet _
    | with_reducible exact c.peerPut _
    | (staging_getPeer_bind; refine c.readPeer _ _ _ ?_; intro p tag)
    | (rich_getKey_bind; refine c.readKey _ _ _ ?_; intro key keyCell)
    | (with_reducible refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | split

theorem enqueuePerPeerTx_rule (item : List SkbId) (state : PacketState) (c : Contracts P) :
    ⦃fun g => ⌜P g⌝⦄ enqueuePerPeerTx item state ⦃⇓? _ g => ⌜P g⌝⦄ := by
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
    | with_reducible exact hreadTx c _
    | with_reducible exact hword _
    | with_reducible exact c.modify _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    | with_reducible exact c.setPeer _ _ (by assumption)
    | with_reducible exact c.setKey _ _ (by assumption)
    | with_reducible exact c.peerGet _
    | with_reducible exact c.peerPut _
    | with_reducible exact setTx c _ _
    | with_reducible exact freeTx c _
    | with_reducible exact c.cpu _
    | with_reducible exact enqueuePerDeviceAndPeer_rule _ _ c
    | with_reducible exact c.release _ _
    | with_reducible exact (ensures_iff _ _ _).mpr (sendQueuedHandshakeInitiation_rule _ _ c)
    | (staging_getPeer_bind; refine c.readPeer _ _ _ ?_; intro p tag)
    | (rich_getKey_bind; refine c.readKey _ _ _ ?_; intro key keyCell)
    | (with_reducible refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | (with_reducible refine hloop _ _ _ ?_; intro _ _)
    | split

theorem createData_rule (pid : PeerId) (item : List SkbId) (c : Contracts P) :
    ⦃fun g => ⌜P g⌝⦄ createData pid item ⦃⇓? _ g => ⌜P g⌝⦄ := by
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
    | with_reducible exact hreadTx c _
    | with_reducible exact hword _
    | with_reducible exact c.modify _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    | with_reducible exact c.setPeer _ _ (by assumption)
    | with_reducible exact c.setKey _ _ (by assumption)
    | with_reducible exact c.peerGet _
    | with_reducible exact c.peerPut _
    | with_reducible exact setTx c _ _
    | with_reducible exact freeTx c _
    | with_reducible exact c.cpu _
    | with_reducible exact enqueuePerDeviceAndPeer_rule _ _ c
    | with_reducible exact c.release _ _
    | with_reducible exact (ensures_iff _ _ _).mpr (sendQueuedHandshakeInitiation_rule _ _ c)
    | with_reducible exact (ensures_iff _ _ _).mpr (enqueuePerPeerTx_rule _ _ c)
    | (staging_getPeer_bind; refine c.readPeer _ _ _ ?_; intro p tag)
    | (rich_getKey_bind; refine c.readKey _ _ _ ?_; intro key keyCell)
    | (with_reducible refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | (with_reducible refine hloop _ _ _ ?_; intro _ _)
    | split

theorem stagedFallback_rule (pid : PeerId) (packets : List Packet) (key : Option KeypairId) (invalid : Bool) (c : Contracts P) :
    ⦃fun g => ⌜P g⌝⦄ Config.stagedFallback pid packets key invalid ⦃⇓? _ g => ⌜P g⌝⦄ := by
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
    | with_reducible exact hreadTx c _
    | with_reducible exact hword _
    | with_reducible exact c.modify _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    | with_reducible exact c.setPeer _ _ (by assumption)
    | with_reducible exact c.setKey _ _ (by assumption)
    | with_reducible exact c.peerGet _
    | with_reducible exact c.peerPut _
    | with_reducible exact setTx c _ _
    | with_reducible exact freeTx c _
    | with_reducible exact c.cpu _
    | with_reducible exact enqueuePerDeviceAndPeer_rule _ _ c
    | with_reducible exact c.release _ _
    | with_reducible exact (ensures_iff _ _ _).mpr (sendQueuedHandshakeInitiation_rule _ _ c)
    | (staging_getPeer_bind; refine c.readPeer _ _ _ ?_; intro p tag)
    | (rich_getKey_bind; refine c.readKey _ _ _ ?_; intro key keyCell)
    | (with_reducible refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | (with_reducible refine hloop _ _ _ ?_; intro _ _)
    | split

theorem stagedAfterGet_rule (pid : PeerId) (packets : List Packet) (key : Option KeypairId) (c : Contracts P) :
    ⦃fun g => ⌜P g⌝⦄ Config.stagedAfterGet pid packets key ⦃⇓? _ g => ⌜P g⌝⦄ := by
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
    | with_reducible exact hreadTx c _
    | with_reducible exact hword _
    | with_reducible exact c.modify _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    | with_reducible exact c.setPeer _ _ (by assumption)
    | with_reducible exact c.setKey _ _ (by assumption)
    | with_reducible exact c.peerGet _
    | with_reducible exact c.peerPut _
    | with_reducible exact setTx c _ _
    | with_reducible exact freeTx c _
    | with_reducible exact c.cpu _
    | with_reducible exact enqueuePerDeviceAndPeer_rule _ _ c
    | with_reducible exact c.release _ _
    | with_reducible exact (ensures_iff _ _ _).mpr (sendQueuedHandshakeInitiation_rule _ _ c)
    | with_reducible exact (ensures_iff _ _ _).mpr (stagedFallback_rule _ _ _ _ c)
    | with_reducible exact (ensures_iff _ _ _).mpr (ipTunnelEcnEncap_wg_variant P _)
    | with_reducible exact newTxSkbs_rule _ c
    | with_reducible exact (ensures_iff _ _ _).mpr (createData_rule _ _ c)
    | (staging_getPeer_bind; refine c.readPeer _ _ _ ?_; intro p tag)
    | (rich_getKey_bind; refine c.readKey _ _ _ ?_; intro key keyCell)
    | (with_reducible refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | (with_reducible refine hloop _ _ _ ?_; intro _ _)
    | split

theorem sendStagedPackets_rule (pid : PeerId) (c : Contracts P) :
    Ensures (sendStagedPackets pid) P (fun _ => P) := by
  rw [← Config.sendStaged_source]
  unfold Config.stagedSource
  repeat' first
    | with_reducible exact hpure _
    | with_reducible exact hbranch _ _
    | with_reducible exact hreadPeer _
    | with_reducible exact c.setPeer _ _ (by assumption)
    | with_reducible exact c.keyGet _
    | with_reducible exact (ensures_iff _ _ _).mpr (stagedAfterGet_rule _ _ _ c)
    | (staging_getPeer_bind; refine c.readPeer _ _ _ ?_; intro p tag)
    | (rich_getKey_bind; refine c.readKey _ _ _ ?_; intro key keyCell)
    | (with_reducible refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)


end Leanux.Proofs.WG.Index.StagingPreservation
