import Leanux.Proofs.WG.TransmitSecurity.DriverNeutralCalls
import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveConfiguration

set_option maxHeartbeats 200000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Origins TransmitSecurity Configuration

theorem config_out (a : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    Preserves (Driver.configOut a peer ret) := by
  unfold Driver.configOut
  exact StatePrefixEnsures.bind (lift _ (peer_put peer)) (fun _ =>
    StatePrefixEnsures.bind (ambient _) (fun _ => pure ret))

private theorem finish_end (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (ret : Int) (running : Bool) : Preserves (do
      if ← liftWGPrefix (branch .peerRunning running) then Driver.stagingObserved TimestampDriver.hooks pid
      Driver.configOut a peer ret) := by
  apply StatePrefixEnsures.bind (ambient _)
  intro active
  split
  · exact StatePrefixEnsures.bind (staging pid) (fun _ => config_out a peer ret)
  · exact config_out a peer ret

private theorem decide_keepalive (p : Peer) (interval : Nat) (running : Bool) : SameWGStore
    (WG.andM (branch .peerKeepaliveWasZero (p.persistentKeepaliveInterval == 0))
      (WG.andM (branch .peerKeepaliveNonzero (interval != 0)) (branch .peerKeepaliveRunning running))) := by
  intro initial
  change Framing.Preserves (fun w => wgStoreView w = initial) _
  unfold WG.andM
  simp only [branch]
  repeat' first
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem config_finish (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    Preserves (Driver.configTailFinish TimestampDriver.hooks a peer pid ret) := by
  unfold Driver.configTailFinish
  apply StatePrefixEnsures.bind (lift _ (fun h => frame_store h _ getDev_sameWGStore))
  intro d
  apply StatePrefixEnsures.bind (ambient _)
  intro keep
  cases keep with
  | false => exact finish_end a peer pid ret d.running
  | true =>
    dsimp only
    apply StatePrefixEnsures.bind (Saved.read_saved pid)
    intro p
    apply StatePrefixEnsures.bind (Saved.saved_store pid p _ (decide_keepalive p _ d.running))
    intro send
    apply StatePrefixEnsures.bind (Saved.write_saved pid p
      (fun p => {p with persistentKeepaliveInterval := a.keepalive.getD 0}) (fun _ => ⟨rfl,rfl⟩))
    intro _
    apply StatePrefixEnsures.bind (ambient _)
    intro now
    cases now with
    | false => exact finish_end a peer pid ret d.running
    | true => exact StatePrefixEnsures.bind (keepalive pid) (fun _ => finish_end a peer pid ret d.running)

private def pskSource (pid : PeerId) (psk : Key) : WGPrefix TimestampReceipt Unit := do
  let p ← liftWGPrefix (getPeer pid)
  liftWGPrefix (setPeer pid {p with presharedKey := psk})

private theorem psk_write (pid : PeerId) (psk : Key) : Preserves (pskSource pid psk) :=
  StatePrefixEnsures.bind (Saved.read_saved pid) (fun p => Saved.write_saved pid p
    (fun p => {p with presharedKey := psk}) (fun _ => ⟨rfl,rfl⟩))

macro "archive_driver_config_step " : tactic => `(tactic| first
  | unfold StatePrefixPreserves
  | maintenance_join_let
  | maintenance_join_use
  | (nonce_source_head Driver.configOut; exact config_out _ _ _)
  | (nonce_source_head Driver.configTailFinish; exact config_finish _ _ _ _)
  | (nonce_source_head Driver.keepaliveObserved; exact keepalive _)
  | (nonce_source_head Driver.stagingObserved; exact staging _)
  | (nonce_source_head setAllowedip; exact lift _ (allowed_ip _ _))
  | (nonce_source_head Driver.removeObserved; rw [Driver.remove_lift TimestampDriver.hooks rfl])
  | (nonce_source_head peerRemove; exact lift _ (remove _))
  | (nonce_source_head removeByPeer; exact lift _ (remove_ips _))
  | (nonce_source_head setPeerEndpoint; exact lift _ (endpoint _ _))
  | (nonce_source_head peerCreate; exact lift _ (peer_create _ _))
  | (nonce_source_head pubkeyLookup; exact lift _ (pubkey _))
  | (nonce_source_head peerGet; exact lift _ (peer_get _))
  | (nonce_source_head getDev; exact lift _ (fun h => frame_store h _ getDev_sameWGStore))
  | (nonce_source_head getPeer; exact lift _ (read_peer _))
  | (first | nonce_source_head WG.andM | nonce_source_head WG.orM
     apply lift; intro confirmed
     first | unfold WG.andM | unfold WG.orM
     simp only [branch]
     repeat' archive_handshake_step confirmed)
  | (first | nonce_source_head branch | nonce_source_head invariant
     exact ambient _)
  | (nonce_source_head pskSource; exact psk_write _ _)
  | (first | nonce_source_head Pure.pure | nonce_source_head pure
     exact pure _)
  | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
  | (nonce_source_head ForIn.forIn
     apply loop
     intro x b
     change StatePrefixPreserves (fun h w _ => StateInv h w) History _)
  | maintenance_intro
  | maintenance_reduce
  | maintenance_reduce_match
  | (with_reducible split))

theorem config_tail (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    Preserves (Driver.configTail TimestampDriver.hooks a peer pid) := by
  unfold Driver.configTail peerAllowedIpsWith
  apply StatePrefixEnsures.bind (ambient _)
  intro has
  cases has with
  | false => exact config_finish a peer pid 0
  | true =>
    simp only [ite_true]
    apply StatePrefixEnsures.bind
    · apply loop
      intro entry acc
      apply StatePrefixEnsures.bind (ambient _)
      intro _
      cases entry with
      | malformed =>
        apply StatePrefixEnsures.bind (ambient _)
        intro _
        apply StatePrefixEnsures.bind (config_out a peer (-EINVAL))
        intro result
        exact pure _
      | attrs ip =>
        apply StatePrefixEnsures.bind (ambient _)
        intro _
        apply StatePrefixEnsures.bind (lift _ (allowed_ip pid ip))
        intro ret
        apply StatePrefixEnsures.bind (ambient _)
        intro bad
        cases bad with
        | false => exact pure _
        | true =>
          apply StatePrefixEnsures.bind (config_out a peer ret)
          intro result
          exact pure _
    · intro acc
      rcases acc with ⟨early,ret⟩
      cases early with
      | some result => exact pure _
      | none =>
        apply StatePrefixEnsures.bind (ambient _)
        intro _
        exact config_finish a peer pid ret

private theorem guard_and (d : Decision) (b : Bool) (e : Decision) (c : Bool) :
    Preserves (liftWGPrefix (WG.andM (branch d b) (branch e c))) := by
  apply lift
  intro confirmed
  unfold WG.andM
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch d b) (StateInv confirmed))
  intro yes
  cases yes with
  | false => exact preserves_pure false
  | true => exact hoare_liftAmbient (AmbientM.branch e c) (StateInv confirmed)

open Lean Meta Elab Tactic in
elab "archive_config_callback " name:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let args := target.getAppArgs
  let action ←
    if target.isAppOf ``StatePrefixPreserves then Pure.pure args.back!
    else if target.isAppOf ``StatePrefixEnsures then Pure.pure args[args.size - 2]!
    else throwError "not a state-prefix contract"
  let expected ← Lean.Elab.Term.elabTerm name none
  unless action.consumeMData.headBeta.getAppFn == expected.getAppFn do
    throwError "different callback head"

private theorem update_control (a : PeerAttrs) (flags : UInt32) (psk : Option Key)
    (remove setPsk replace : WGPrefix TimestampReceipt Unit) (endpoint : Endpoint → WGPrefix TimestampReceipt Unit)
    (out : Int → WGPrefix TimestampReceipt Int) (tail : WGPrefix TimestampReceipt Int)
    (hr : Preserves remove) (hs : Preserves setPsk) (hp : Preserves replace)
    (he : ∀ ep, Preserves (endpoint ep)) (ho : ∀ ret, Preserves (out ret)) (ht : Preserves tail) :
    Preserves (peerConfigUpdateWith (fun {_} a => liftWGPrefix a)
      remove setPsk replace endpoint out tail a flags psk) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) History _
  unfold peerConfigUpdateWith
  unfold StatePrefixPreserves
  cases a.endpoint
  all_goals repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (archive_config_callback remove; exact hr)
    | (archive_config_callback setPsk; exact hs)
    | (archive_config_callback replace; exact hp)
    | (archive_config_callback endpoint; exact he _)
    | (archive_config_callback out; exact ho _)
    | (archive_config_callback tail; exact ht)
    | (nonce_source_head WG.andM; exact guard_and _ _ _ _)
    | (first | nonce_source_head branch | nonce_source_head invariant
       exact ambient _)
    | (nonce_source_head Pure.pure; exact pure _)
    | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
    | maintenance_intro
    | maintenance_reduce
    | maintenance_reduce_match
    | split

theorem config_update (a : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    Preserves (Driver.configUpdate TimestampDriver.hooks a peer flags psk pid) := by
  unfold Driver.configUpdate
  rw [Driver.remove_lift TimestampDriver.hooks rfl]
  exact update_control a flags psk _ _ _ _ _ _ (lift _ (remove peer))
    (psk_write pid (psk.getD [])) (lift _ (remove_ips pid))
    (fun ep => lift _ (endpoint pid ep)) (config_out a peer) (config_tail a peer pid)

private theorem acquired_control
    (out : Int → WGPrefix TimestampReceipt Int)
    (update : Option PeerId → UInt32 → Option Key → PeerId → WGPrefix TimestampReceipt Int)
    (ho : ∀ ret, Preserves (out ret)) (hu : ∀ p f k pid, Preserves (update p f k pid))
    (key : Key) (psk : Option Key) (flags : UInt32) (peer : Option PeerId) :
    Preserves (peerCommandAcquiredWith (fun {_} a => liftWGPrefix a)
      (fun key psk => liftWGPrefix (peerCreate key psk)) (fun pid => liftWGPrefix (peerGet pid))
      out update key psk flags peer) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) History _
  unfold peerCommandAcquiredWith
  unfold StatePrefixPreserves
  cases peer
  all_goals repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (archive_config_callback out; exact ho _)
    | (archive_config_callback update; exact hu _ _ _ _)
    | (nonce_source_head peerCreate; exact lift _ (peer_create _ _))
    | (nonce_source_head peerGet; exact lift _ (peer_get _))
    | (nonce_source_head getDev; exact lift _ (fun h => frame_store h _ getDev_sameWGStore))
    | (nonce_source_head WG.andM; exact guard_and _ _ _ _)
    | (first | nonce_source_head branch | nonce_source_head invariant
       exact ambient _)
    | (nonce_source_head Pure.pure; exact pure _)
    | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
    | maintenance_intro
    | maintenance_reduce
    | maintenance_reduce_match
    | split

private theorem command_control (a : PeerAttrs) (out : Int → WGPrefix TimestampReceipt Int)
    (acquired : Key → Option Key → UInt32 → Option PeerId → WGPrefix TimestampReceipt Int)
    (ho : ∀ ret, Preserves (out ret)) (ha : ∀ k p f peer, Preserves (acquired k p f peer)) :
    Preserves (setPeerCmdWith (fun {_} a => liftWGPrefix a)
      (fun key => liftWGPrefix (pubkeyLookup key)) out acquired a) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) History _
  unfold setPeerCmdWith
  unfold StatePrefixPreserves
  cases a.publicKey
  all_goals repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (archive_config_callback out; exact ho _)
    | (archive_config_callback acquired; exact ha _ _ _ _)
    | (nonce_source_head pubkeyLookup; exact lift _ (pubkey _))
    | (nonce_source_head WG.andM; exact guard_and _ _ _ _)
    | (first | nonce_source_head branch | nonce_source_head invariant
       exact ambient _)
    | (nonce_source_head Pure.pure; exact pure _)
    | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
    | maintenance_intro
    | maintenance_reduce
    | maintenance_reduce_match
    | split

theorem config_peer (a : PeerAttrs) :
    Preserves (Driver.configPeer TimestampDriver.hooks a) :=
  command_control a _ _ (config_out a none)
    (acquired_control _ _ (config_out a none) (config_update a))

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
