import Leanux.Proofs.WG.Index.SenderIndexEffects
import Leanux.Proofs.WG.Noise.PendingSocketFrames
import Leanux.Proofs.WG.TimerDiscipline.SendBufferFrame
import Leanux.Proofs.WG.Noise.InitiationCoverageFrames
import Leanux.Proofs.WG.Origins.RetainingLeaves

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise TimerDiscipline Std.Do Leanux.Proofs.Framing
open Queues.RxCredits

def senderFields (g : WGWorld) := g.dev.map senderDeviceCell

theorem sender_fields_of_sendWork_material {α : Type} (action : WG.M α) (pid : PeerId)
    (work : ∀ q v,⦃fun w => ⌜TimerDiscipline.sendWorkAt w pid=(q,v)⌝⦄ action
      ⦃⇓? _ w => ⌜TimerDiscipline.sendWorkAt w pid=(q,v)⌝⦄)
    (materialFrame : SameView Origins.view action) : SameView senderFields action := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result out b run
  have socket := (ensures_iff _ _ _).mpr
    (work (TimerDiscipline.sendWorkAt g pid).1 (TimerDiscipline.sendWorkAt g pid).2)
    g a result out b rfl run
  have material := (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    materialFrame g a result out b run
  cases before : g.dev <;> cases after : out.dev
  all_goals simp only [TimerDiscipline.sendWorkAt,TimerDiscipline.sendWorkKernel,
    before,after,Option.map_none,Option.map_some,Option.bind_none,Option.bind_some] at socket
  case none.none => simp [senderFields,before,after]
  case none.some d => simp at socket
  case some.none d => simp at socket
  case some.some d e =>
    have table : e.indexTable = d.indexTable :=
      congrArg (fun x : TimerDiscipline.SendWorkDevice => x.1.1) (Option.some.inj (congrArg Prod.fst socket))
    have cells := congrArg (fun x : TimerDiscipline.SendWorkDevice => x.2.2.1)
      (Option.some.inj (congrArg Prod.fst socket))
    have km : (e.ifindex,fun kid : KeypairId => e.keypairs[kid]?) = (d.ifindex,fun kid : KeypairId => d.keypairs[kid]?) := by
      simpa [Origins.view,before,after] using material
    simp only [senderFields,before,after,Option.map_some,Option.some.injEq]
    have epoch : e.ifindex=d.ifindex := congrArg Prod.fst km
    have keys : (fun kid : KeypairId => e.keypairs[kid]?)=(fun kid : KeypairId => d.keypairs[kid]?) := congrArg Prod.snd km
    unfold senderDeviceCell
    rw [table,epoch,keys]
    simp only [Prod.mk.injEq,true_and]
    funext target
    have projected := congrArg
      (Option.map (fun x : TimerDiscipline.SendWorkCell =>
        ([x.2.1,x.2.2.1,x.2.2.2.1],x.2.2.2.2.1,x.2.2.2.2.2.1,
          x.2.2.2.2.2.2.1,x.2.2.2.2.2.2.2.1))) (congrFun cells target)
    simp only [TimerDiscipline.sendWorkDevice,TimerDiscipline.sendWorkCell,
      Option.map_map,Function.comp_def] at projected
    change e.peers[target]?.map senderPeerCell=d.peers[target]?.map senderPeerCell at projected
    exact projected

theorem sender_fields_socket (pid : PeerId) (msg : List UInt8) :
    SameView senderFields (sendBufferToPeer pid msg) :=
  sender_fields_of_sendWork_material _ pid
    (TimerDiscipline.sendBufferToPeer_spec_sendWork_variant pid msg)
    (Origins.Retaining.sendBufferToPeer_material pid msg)

theorem senderFields_write_state (g : WGWorld) (pid : PeerId) (p q : Peer)
    (resident : peerAt g pid = some p) (same : senderPeerCell q = senderPeerCell p) :
    senderFields {g with dev := g.dev.map fun d => {d with peers := d.peers.insert pid q}} = senderFields g := by
  cases device : g.dev with
  | none => simp [peerAt,device] at resident
  | some d =>
    have found : d.peers[pid]? = some p := by simpa [peerAt,device] using resident
    simpa [senderFields,device] using congrArg some (senderFields_peerWrite d pid p q found same)

theorem sender_setPeer (pid : PeerId) (p q : Peer) (initial : Option SenderDeviceCell)
    (same : senderPeerCell q = senderPeerCell p) :
    Ensures (setPeer pid q)
      (fun g => senderFields g = initial ∧ peerAt g pid = some p)
      (fun _ g => senderFields g = initial) := by
  intro g a value out b pre run
  cases run
  exact (senderFields_write_state g pid p q pre.2 same).trans pre.1

theorem sender_modifyPeer (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, senderPeerCell (f p) = senderPeerCell p) :
    SameView senderFields (modifyPeer pid f) := by
  intro initial
  apply (ensures_iff _ _ _).mp
  change Ensures (getPeer pid >>= fun p => setPeer pid (f p)) _ _
  exact ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid (fun g => senderFields g=initial)))
    (fun p => sender_setPeer pid p (f p) initial (same p))

theorem sender_mac (pid : PeerId) (msg : List UInt8) :
    SameView senderFields (addMacToPacket pid msg) := by
  intro initial
  apply (ensures_iff _ _ _).mp
  let P := fun g => senderFields g = initial
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) P (fun _ => P) := by
    intro g a y v b h run; cases run; exact h
  have htest (p : Peer) :
      Ensures (WG.andM (branch .addMacCookieValid p.cookieIsValid)
        (branchExpired .addMacCookieFresh p.cookieBirthdate COOKIE_FRESH_SECONDS (!·)))
        P (fun _ => P) :=
    (ensures_iff _ _ _).mpr
      (DumpComposition.andM_sameView _ _
        (fun initial => hoare_liftAmbient (AmbientM.branch .addMacCookieValid p.cookieIsValid)
          (fun g => senderFields g = initial))
        ((branchExpired_sameWGWorld _ _ _ (!·)).factor senderFields) initial)
  unfold addMacToPacket
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid P)) ?_
  intro p
  dsimp only
  refine ensures_bind (Q := fun _ => P) _ _
    (sender_setPeer pid p _ initial rfl) ?_
  intro _
  refine ensures_bind _ _ (htest p) ?_
  intro accepted
  split <;> exact hpure _

def senderStateFields (s : Campaign2.State) := s.device.map senderDeviceCell

theorem senderStateFields_write (entry : Campaign2.State) (d : Device)
    (pid : PeerId) (p q : Peer) (device : entry.device=some d)
    (resident : d.peers[pid]?=some p) (same : senderPeerCell q=senderPeerCell p) :
    senderStateFields {entry with device:=entry.device.map fun d=>{d with peers:=d.peers.insert pid q}} =
      senderStateFields entry := by
  simpa [senderStateFields,device] using congrArg some (senderFields_peerWrite d pid p q resident same)

theorem senderStateFields_wheel (entry : Campaign2.State) (d : Device)
    (pid : PeerId) (p : Peer) (timer : PeerTimer) (expires clk : UInt64)
    (device : entry.device=some d) (resident : d.peers[pid]?=some p) :
    senderStateFields (wheelPlacementView entry pid p timer expires clk) = senderStateFields entry := by
  unfold wheelPlacementView
  split
  · exact senderStateFields_write entry d pid p _ device resident (by cases timer <;> rfl)
  · exact senderStateFields_write {entry with timerEnqueues:=entry.timerEnqueues+1}
      d pid p _ device resident (by cases timer <;> rfl)

theorem senderStateFields_armEffect (entry : Campaign2.Snapshot) (d : Device)
    (pid : PeerId) (p : Peer) (timer : PeerTimer) (delay : Nat) (final : Campaign2.State)
    (device : entry.wg.device=some d) (resident : d.peers[pid]?=some p)
    (effect : peerTimerArmEffect entry pid p timer delay final) :
    senderStateFields final = senderStateFields entry.wg := by
  unfold peerTimerArmEffect at effect
  split at effect
  · obtain ⟨caller,now,unit,_,_,effect⟩ := effect
    split at effect
    · rw [effect]; rfl
    · obtain ⟨clk,effect⟩ := effect
      rw [effect]
      exact senderStateFields_wheel _ d pid p timer _ clk device resident
  · rw [effect]
    exact senderStateFields_wheel entry.wg d pid p timer _ _ device resident

theorem sender_traversal (pid : PeerId) : SameView senderFields (timersTraversal pid) := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a value out b run
  cases device : g.dev with
  | none => simp [timersTraversal,getPeer,getDev,device,invariant,AmbientM.invariant] at run; cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none => simp [timersTraversal,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run; cases run
    | some p =>
      have effect := timersTraversal_effect pid d p resident (Campaign2.snapshot g a)
        g a value out b ⟨rfl,device⟩ run
      split at effect
      · exact senderStateFields_armEffect (Campaign2.snapshot g a) d pid p .persistentKeepalive
          (p.persistentKeepaliveInterval*HZ) (Campaign2.snapshot out b).wg device resident effect
      · exact congrArg senderStateFields effect

theorem sender_delTimer (pid : PeerId) (timer : PeerTimer) : SameView senderFields (delTimer pid timer) := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a value out b run
  cases device : g.dev with
  | none => simp [delTimer,getPeer,getDev,device,invariant,AmbientM.invariant] at run; cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none => simp [delTimer,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run; cases run
    | some p =>
      have effect := delTimer_exact pid timer p (Campaign2.snapshot g a)
        g a value out b ⟨rfl,by change peerAt g pid=some p; simp [peerAt,device,resident]⟩ run
      have projected := congrArg (fun s : Campaign2.Snapshot => senderStateFields s.wg) effect
      change senderFields out = _ at projected
      rw [projected]
      exact senderStateFields_write (Campaign2.snapshot g a).wg d pid p _ device resident
        (by cases timer <;> rfl)


theorem sender_wheel_state (entry : WGWorld) (pid : PeerId) (p : Peer)
    (timer : PeerTimer) (expires clk : UInt64) (ambient : Ambient) (resident : peerAt entry pid = some p) :
    senderFields (wheelPlacementState entry pid p timer expires clk) = senderFields entry := by
  cases device : entry.dev with
  | none => simp [peerAt,device] at resident
  | some d =>
    have found : d.peers[pid]?=some p := by simpa [peerAt,device] using resident
    have projection :
        (wheelPlacementState entry pid p timer expires clk).dev =
        (wheelPlacementView (Campaign2.snapshot entry ambient).wg pid p timer expires clk).device := by
      cases placed : TimerWheel.place p timer expires clk <;>
        simp only [wheelPlacementState,wheelPlacementView,placed] <;> rfl
    unfold senderFields
    rw [projection]
    exact senderStateFields_wheel (Campaign2.snapshot entry ambient).wg d pid p timer expires clk device found
theorem sender_armTimer_resident (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (caller : Option UInt64) (g : WGWorld) (ambient : Ambient)
    (final : WGWorld) (after : Ambient) (p : Peer)
    (resident : peerAt g pid = some p)
    (run : ((armTimer pid timer delay caller).run g).run ambient = .ok (((),final),after)) :
    senderFields final = senderFields g := by
  cases mode : ambient.armRecords with
  | false =>
    rw [armTimer_off_effect pid timer delay caller g p resident ambient after final mode run]
    exact sender_wheel_state g pid p timer _ _ ambient resident
  | true =>
    cases caller with
    | none =>
      have ambientRead : ((getAmbient : WG.M Ambient).run g).run ambient = .ok ((ambient,g),ambient) := rfl
      have hiddenRead : ((hidden .modTimerArm : WG.M (List UInt8)).run g).run ambient =
          ((AmbientM.hidden .modTimerArm).run ambient >>= fun (bytes,next) => .ok ((bytes,g),next)) := rfl
      simp only [armTimer,StateT.run_bind,StateT.run_get,pure_bind] at run
      rw [ambientRead] at run
      simp only [bind,Except.bind,mode,Bool.not_true,Bool.false_eq_true,ite_false] at run
      change (((hidden .modTimerArm : WG.M (List UInt8)).run g).run ambient >>= _) = _ at run
      rw [hiddenRead] at run
      cases read : (AmbientM.hidden .modTimerArm).run ambient with
      | error stop => rw [read] at run; cases run
      | ok out => rw [read] at run; cases out; cases run
    | some caller =>
      by_cases same : p.timer timer = some (caller + delay.toUInt64)
      · obtain ⟨now,unit,_,_,effect⟩ := armTimer_sameExpiry_effect
          pid timer delay caller g p resident same ambient after final mode run
        rw [effect]
        rfl
      · obtain ⟨now,unit,clk,_,_,effect⟩ := armTimer_changedExpiry_effect
          pid timer delay caller g p resident same ambient after final mode run
        rw [effect]
        exact sender_wheel_state _ pid p timer _ _ ambient resident

/-- The actual guard supplies residency and excludes malformed missing-peer
states before an arm. All three concrete arming effects preserve the observed index and owner fields. -/
theorem sender_guardedArm (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (caller : Option UInt64) (initial : Option SenderDeviceCell) :
    Ensures (do if ← modPeerTimerGuard pid then armTimer pid timer delay caller)
      (fun g => senderFields g = initial)
      (fun _ g => senderFields g = initial) := by
  intro g ambient result final after pre run
  change (((modPeerTimerGuard pid).run g).run ambient >>= fun ((allowed,current),inputs) =>
    ((if allowed then armTimer pid timer delay caller else pure () : WG.M Unit).run current).run inputs) = _ at run
  cases device : g.dev with
  | none =>
    simp [modPeerTimerGuard,WG.andM,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases found : d.peers[pid]? with
    | none =>
      simp [modPeerTimerGuard,WG.andM,getDev,getPeer,device,found,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      cases checked : ((modPeerTimerGuard pid).run g).run ambient with
      | error stop => rw [checked] at run; cases run
      | ok out =>
        obtain ⟨⟨allowed,current⟩,inputs⟩ := out
        have effect := modPeerTimerGuard_input_effect pid d p found
          g current ambient inputs allowed device checked
        have same := effect.2.1
        subst current
        rw [checked] at run
        cases allowed with
        | false => cases run; exact pre
        | true =>
          cases result
          exact (sender_armTimer_resident pid timer delay caller g inputs final after p
            (by simp [peerAt,device,found]) run).trans pre

theorem sender_initiated_frame (pid : PeerId) (initial : Option SenderDeviceCell) :
    Ensures (timersHandshakeInitiated pid)
      (fun g => senderFields g = initial)
      (fun _ g => senderFields g = initial) := by
  unfold timersHandshakeInitiated
  refine ensures_bind (Q := fun _ g => senderFields g = initial) _ _ ?_ ?_
  · intro g ambient caller final after pre run
    rw [(callerJiffies_input_effect _ g final ambient after caller run).1]
    exact pre
  · intro caller
    refine ensures_bind _ _ (jitter_wg_spec
      (fun g => senderFields g = initial) .retransmitJitter) ?_
    intro jitter
    exact sender_guardedArm pid .retransmitHandshake (REKEY_TIMEOUT_TICKS + jitter) caller initial

end Leanux.Proofs.WG.Index
