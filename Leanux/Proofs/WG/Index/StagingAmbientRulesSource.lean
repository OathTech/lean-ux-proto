import Leanux.Proofs.WG.Index.StagedFrames
import Leanux.Proofs.WG.Index.SendSource
import Leanux.Proofs.WG.Queues.DecryptCarrier

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.StagingAmbientRules
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do
def Ensures {α : Type} (action : WG.M α) (P : WGWorld → Ambient → Prop)
    (Q : α → WGWorld → Ambient → Prop) : Prop :=
  ∀ g a value after b, P g a → (action.run g).run a = .ok ((value,after),b) → Q value after b

theorem ensures_bind {α β : Type} {P : WGWorld → Ambient → Prop}
    {Q : α → WGWorld → Ambient → Prop} {R : β → WGWorld → Ambient → Prop}
    (action : WG.M α) (next : α → WG.M β)
    (first : Ensures action P Q) (rest : ∀ x, Ensures (next x) (Q x) R) :
    Ensures (action >>= next) P R := by
  intro g a value after b pre run
  rw [Leanux.Proofs.WG.MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨x,middle,c,head,tail⟩ := run
  exact rest x middle c value after b (first g a x middle c pre head) tail

abbrev PeerImage := Nat × Option KeypairId × Option KeypairId × Option KeypairId ×
  Option PeerId × Nat × Bool × Option (Nat × Nat × Nat × Nat) × Key × Nat × Option Endpoint
/-- Primitive contracts for the one owned staging source proof. Cached peer/key
observations are supplied by reads and consumed by the original saved writes. -/
structure Contracts (P : WGWorld → Ambient → Prop) where
  peer : PeerId → PeerImage → Prop
  key : KeypairId → (Option PeerId × Bool) → Prop
  readPeer : ∀ (pid : PeerId) {α : Type} (next : Peer → WG.M α),
    (∀ p, peer pid (StagingRich.PeerCell p) → Ensures (next p) P (fun _=>P)) →
    Ensures (getPeer pid >>= next) P (fun _=>P)
  readKey : ∀ (kid : KeypairId) {α : Type} (next : Keypair → WG.M α),
    (∀ k, key kid (StagingRich.KeyCell k) → Ensures (next k) P (fun _=>P)) →
    Ensures (getKeypair kid >>= next) P (fun _=>P)
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
  getTx : ∀ id, Ensures (getTxSkb id) P (fun _=>P)
  setTx : ∀ id f, Ensures (setTxSkb id f) P (fun _=>P)
  freeTx : ∀ id, Ensures (freeTxSkb id) P (fun _=>P)
  newTx : ∀ pkt, Ensures (newTxSkb pkt) P (fun _=>P)
  branch : ∀ site value, Ensures (Leanux.branch site value) P (fun _=>P)
  cmp : ∀ site value lhs rhs, Ensures (branchCmp site value lhs rhs) P (fun _=>P)
  clock : ∀ site, Ensures (hiddenClock64 site) P (fun _=>P)
  peek : ∀ worker pid, Ensures (peekQueuedUnit worker pid) P (fun _=>P)
  queue : ∀ worker pid, Ensures (recordQueued worker pid) P (fun _=>P)
  deviceQueue : ∀ worker, Ensures (queueDeviceWork worker) P (fun _=>P)
  ecn : ∀ pkt, Ensures (ipTunnelEcnEncap pkt) P (fun _=>P)
  cpu : ∀ pid, Ensures (cpumaskChooseOnline pid) P (fun _=>P)
open Lean Meta Elab Tactic in
elab "ambient_getPeer_bind" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Ensures do throwError "not an Ensures contract"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  unless action.isAppOf ``Bind.bind do throwError "not a bind"
  let binds := action.getAppArgs
  unless binds[binds.size - 2]!.consumeMData.isAppOf ``getPeer do
    throwError "not a getPeer bind"
open Lean Meta Elab Tactic in
elab "ambient_getKey_bind" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Ensures do throwError "not an Ensures contract"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  unless action.isAppOf ``Bind.bind do throwError "not a bind"
  let binds := action.getAppArgs
  unless binds[binds.size - 2]!.consumeMData.isAppOf ``getKeypair do
    throwError "not a getKeypair bind"

variable {P : WGWorld → Ambient → Prop}

private theorem hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) P (fun _ => P) := by
  intro g a r f b pre run; cases run; exact pre

private theorem hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) P (fun _ => P) := by
  intro g a r f b pre run; cases run

private theorem hreadDev : Ensures getDev P (fun _ => P) := by
  intro g a r f b pre run
  cases hd : g.dev with
  | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
  | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre

private theorem hreadPeer (pid : PeerId) : Ensures (getPeer pid) P (fun _ => P) := by
  unfold getPeer
  refine ensures_bind _ _ hreadDev ?_
  intro d
  split
  · exact hpure _
  · exact hstop _

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
  | none => intro g a r f b pre run; cases run
  | some pid => exact hpure pid

private theorem hreadTx (c : Contracts P) (id : SkbId) :
    Ensures (getTxSkb id) P (fun _ => P) :=
  c.getTx id

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
    Ensures (setTxSkb id f) P (fun _=>P) := c.setTx id f
theorem freeTx (c : Contracts P) (id : SkbId) :
    Ensures (freeTxSkb id) P (fun _=>P) := c.freeTx id

theorem newTxSkbs_rule (packets : List DataPacket) (c : Contracts P) :
    Ensures (packets.mapM newTxSkb) P (fun _ => P) := by
  have loop (xs : List DataPacket) (acc : List SkbId) :
      Ensures (List.mapM.loop newTxSkb xs acc) P (fun _ => P) := by
    induction xs generalizing acc with
    | nil => intro _ _ _ _ _ pre run; cases run; exact pre
    | cons x xs ih =>
      unfold List.mapM.loop
      exact ensures_bind _ _ (c.newTx x) (fun id => ih (id::acc))
  exact loop packets []

theorem enqueuePerDeviceAndPeer_rule (pid : PeerId) (item : List SkbId) (c : Contracts P) :
    Ensures (enqueuePerDeviceAndPeer pid item) P (fun _ => P) := by
  have hcpu (last : Int) : Ensures (cpumaskNextOnlineFrom last) P (fun _ => P) := by
    unfold cpumaskNextOnlineFrom
    refine ensures_bind _ _ (c.branch _ _) ?_
    intro wrap
    cases wrap <;> exact hpure _
  unfold enqueuePerDeviceAndPeer
  cases first : item.head? with
  | none => intro _ _ _ _ _ _ run; cases run
  | some id =>
    refine ensures_bind _ _ (c.setTx id _) ?_
    intro _
    refine c.readPeer pid _ ?_
    intro peer tag
    refine ensures_bind _ _ (c.branch _ _) ?_
    intro full
    cases full with
    | true => exact hpure _
    | false =>
      refine ensures_bind _ _ (c.setPeer pid _ tag) ?_
      intro _
      refine ensures_bind _ _ hreadDev ?_
      intro device
      refine ensures_bind _ _ (hcpu _) ?_
      intro cpu
      refine ensures_bind _ _ (c.modify _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)) ?_
      intro _
      refine ensures_bind _ _ (c.branch _ _) ?_
      intro full
      cases full with
      | true => exact hpure _
      | false =>
        refine ensures_bind _ _ (c.deviceQueue .encryptWorker) ?_
        intro _
        exact ensures_bind _ _ (c.modify _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
          (fun _ => hpure _)

theorem sendQueuedHandshakeInitiation_rule (pid : PeerId) (retry : Bool) (c : Contracts P) :
    Ensures (sendQueuedHandshakeInitiation pid retry) P (fun _=>P) := by
  unfold sendQueuedHandshakeInitiation
  simp only [branchExpired, birthdateTest, bind_assoc, pure_bind]
  all_goals repeat' first
    | with_reducible exact hpure _
    | with_reducible exact c.branch _ _
    | with_reducible exact c.cmp _ _ _ _
    | with_reducible exact c.clock _
    | with_reducible exact c.peek _ _
    | with_reducible exact c.queue _ _
    | with_reducible exact hstop _
    | with_reducible exact hreadPeer _
    | with_reducible exact hreadDev
    | with_reducible exact hreadKey _
    | with_reducible exact c.modify _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    | with_reducible exact c.setPeer _ _ (by assumption)
    | with_reducible exact c.setKey _ _ (by assumption)
    | with_reducible exact c.peerGet _
    | with_reducible exact c.peerPut _
    | (ambient_getPeer_bind; refine c.readPeer _ _ ?_; intro p tag)
    | (ambient_getKey_bind; refine c.readKey _ _ ?_; intro key keyCell)
    | (with_reducible refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | split

theorem enqueuePerPeerTx_rule (item : List SkbId) (state : PacketState) (c : Contracts P) :
    Ensures (enqueuePerPeerTx item state) P (fun _=>P) := by
  unfold enqueuePerPeerTx
  all_goals repeat' first
    | with_reducible exact hpure _
    | with_reducible exact c.branch _ _
    | with_reducible exact c.cmp _ _ _ _
    | with_reducible exact c.clock _
    | with_reducible exact c.peek _ _
    | with_reducible exact c.queue _ _
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
    | with_reducible exact sendQueuedHandshakeInitiation_rule _ _ c
    | (ambient_getPeer_bind; refine c.readPeer _ _ ?_; intro p tag)
    | (ambient_getKey_bind; refine c.readKey _ _ ?_; intro key keyCell)
    | (with_reducible refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | (with_reducible refine hloop _ _ _ ?_; intro _ _)
    | split

theorem createData_rule (pid : PeerId) (item : List SkbId) (c : Contracts P) :
    Ensures (createData pid item) P (fun _=>P) := by
  unfold createData
  simp only [pure_bind]
  all_goals repeat' first
    | with_reducible exact hpure _
    | with_reducible exact c.branch _ _
    | with_reducible exact c.cmp _ _ _ _
    | with_reducible exact c.clock _
    | with_reducible exact c.peek _ _
    | with_reducible exact c.queue _ _
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
    | with_reducible exact sendQueuedHandshakeInitiation_rule _ _ c
    | with_reducible exact enqueuePerPeerTx_rule _ _ c
    | (ambient_getPeer_bind; refine c.readPeer _ _ ?_; intro p tag)
    | (ambient_getKey_bind; refine c.readKey _ _ ?_; intro key keyCell)
    | (with_reducible refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | (with_reducible refine hloop _ _ _ ?_; intro _ _)
    | split

theorem stagedFallback_rule (pid : PeerId) (packets : List Packet) (key : Option KeypairId) (invalid : Bool) (c : Contracts P) :
    Ensures (Config.stagedFallback pid packets key invalid) P (fun _=>P) := by
  unfold Config.stagedFallback
  dsimp only
  all_goals repeat' first
    | with_reducible exact hpure _
    | with_reducible exact c.branch _ _
    | with_reducible exact c.cmp _ _ _ _
    | with_reducible exact c.clock _
    | with_reducible exact c.peek _ _
    | with_reducible exact c.queue _ _
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
    | with_reducible exact sendQueuedHandshakeInitiation_rule _ _ c
    | (ambient_getPeer_bind; refine c.readPeer _ _ ?_; intro p tag)
    | (ambient_getKey_bind; refine c.readKey _ _ ?_; intro key keyCell)
    | (with_reducible refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | (with_reducible refine hloop _ _ _ ?_; intro _ _)
    | split

theorem stagedAfterGet_rule (pid : PeerId) (packets : List Packet) (key : Option KeypairId) (c : Contracts P) :
    Ensures (Config.stagedAfterGet pid packets key) P (fun _=>P) := by
  unfold Config.stagedAfterGet
  simp only [branchExpired, birthdateTest, bind_assoc, pure_bind]
  all_goals repeat' first
    | with_reducible exact hpure _
    | with_reducible exact c.branch _ _
    | with_reducible exact c.cmp _ _ _ _
    | with_reducible exact c.clock _
    | with_reducible exact c.peek _ _
    | with_reducible exact c.queue _ _
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
    | with_reducible exact sendQueuedHandshakeInitiation_rule _ _ c
    | with_reducible exact stagedFallback_rule _ _ _ _ c
    | with_reducible exact c.ecn _
    | with_reducible exact newTxSkbs_rule _ c
    | with_reducible exact createData_rule _ _ c
    | (ambient_getPeer_bind; refine c.readPeer _ _ ?_; intro p tag)
    | (ambient_getKey_bind; refine c.readKey _ _ ?_; intro key keyCell)
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
    | with_reducible exact c.branch _ _
    | with_reducible exact hreadPeer _
    | with_reducible exact c.setPeer _ _ (by assumption)
    | with_reducible exact c.keyGet _
    | with_reducible exact stagedAfterGet_rule _ _ _ c
    | (ambient_getPeer_bind; refine c.readPeer _ _ ?_; intro p tag)
    | (ambient_getKey_bind; refine c.readKey _ _ ?_; intro key keyCell)
    | (with_reducible refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)


open Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem keepalive_rule (pid : PeerId) (P Q : WGWorld → Ambient → Prop)
    (returns : ∀g a, P g a → Q g a)
    (staged : Ensures (sendStagedPackets pid) P (fun _ => Q))
    (write : ∀g a d p mtu, g.dev = some d → d.peers[pid]? = some p → P g a →
      P {g with dev := some {d with peers := d.peers.insert pid ({p with staged := p.staged ++ [{mtu := mtu}]})}} a)
    (branches : ∀ site value, Ensures (branch site value : WG.M Bool) P (fun _=>P))
    (allocation : Ensures (hiddenAlloc .keepaliveSkb : WG.M Bool) P (fun _=>P)) :
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
  have kept := branches _ _ g a empty guarded ag pre guard
  subst guarded
  cases empty with
  | false =>
    simp only [Bool.false_eq_true,ite_false] at run
    exact staged g ag r f b kept run
  | true =>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨allocated,read,aa,alloc,failed,guarded,af,guard,run⟩ := run
    have same := ambient_state (AmbientM.hiddenAlloc .keepaliveSkb) g read ag aa allocated alloc
    have allocatedKeep := allocation g ag allocated read aa kept alloc
    subst read
    have same := ambient_state (AmbientM.branch .keepaliveNoMem (!allocated)) g guarded aa af failed guard
    have guardedKeep := branches _ _ g aa failed guarded af allocatedKeep guard
    subst guarded
    cases failed with
    | true =>
      simp only [ite_true] at run
      cases run
      exact returns _ _ guardedKeep
    | false =>
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at run
      obtain ⟨dev,read,ad,getter,u,prepared,ap,changed,run⟩ := run
      obtain ⟨same,time,_⟩ := DecryptCarrier.getDev_current af ad getter
      subst read
      subst ad
      simp only [WG.setPeer,WG.modifyDev] at changed
      cases changed
      exact staged _ af r f b (write g af d p dev.mtu hd hp guardedKeep)
        (by simpa only [hd,Option.map_some] using run)


end Leanux.Proofs.WG.Index.StagingAmbientRules
