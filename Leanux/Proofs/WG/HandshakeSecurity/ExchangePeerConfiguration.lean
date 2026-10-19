import Leanux.Proofs.WG.HandshakeSecurity.ExchangeEnvironment
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeH1ConfigurationFrames

set_option maxHeartbeats 200000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Origins TransmitSecurity Configuration

theorem config_out (a : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    Preserves (Driver.configOut a peer ret) := by
  unfold Driver.configOut
  exact StatePrefixEnsures.bind (lift _ (peer_put peer)) (fun _ =>
    StatePrefixEnsures.bind (ambient _) (fun _ => pure ret))

private theorem finish_end (facts : H1DriverSourceFacts) (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (ret : Int) (running : Bool) : Preserves (do
      if ← liftWGPrefix (branch .peerRunning running) then Driver.stagingObserved ExchangeDriver.hooks pid
      Driver.configOut a peer ret) := by
  apply StatePrefixEnsures.bind (ambient _)
  intro active
  split
  · exact StatePrefixEnsures.bind (staging_checked facts.data pid) (fun _ => config_out a peer ret)
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

theorem config_finish (facts : H1DriverSourceFacts) (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    Preserves (Driver.configTailFinish ExchangeDriver.hooks a peer pid ret) := by
  unfold Driver.configTailFinish
  rw [show Driver.fixtureOps ExchangeDriver.hooks = AuthenticatedEffects.FixtureEffects.neutral from rfl,
    AuthenticatedEffects.FixtureEffects.peerFinish_neutral]
  unfold AuthenticatedEffects.FixtureEffects.peerFinishWith
  apply StatePrefixEnsures.bind (lift _ (fun h => frame_store h _ getDev_sameWGStore))
  intro d
  apply StatePrefixEnsures.bind (ambient _)
  intro keep
  cases keep with
  | false => exact finish_end facts a peer pid ret d.running
  | true =>
    dsimp only
    apply StatePrefixEnsures.bind (read_saved pid)
    intro p
    apply StatePrefixEnsures.bind (saved_tag pid p _ ((decide_keepalive p _ d.running).of_factor
      (fun s : WGStoreView => fun target => (s.dev.bind fun d => d.peers[target]?).map Peer.handshakeState)
      handshakeTagAt (fun _ => rfl)))
    intro send
    apply StatePrefixEnsures.bind (write_saved pid p
      (fun p => {p with persistentKeepaliveInterval := a.keepalive.getD 0}) rfl)
    intro _
    apply StatePrefixEnsures.bind (ambient _)
    intro now
    cases now with
    | false => exact finish_end facts a peer pid ret d.running
    | true => exact StatePrefixEnsures.bind (keepalive_checked facts.data pid) (fun _ => finish_end facts a peer pid ret d.running)

private def pskSource (pid : PeerId) (psk : Key) : WGPrefix Event Unit := do
  let p ← liftWGPrefix (getPeer pid)
  liftWGPrefix (setPeer pid {p with presharedKey := psk})

private theorem psk_write (pid : PeerId) (psk : Key) : Preserves (pskSource pid psk) :=
  StatePrefixEnsures.bind (read_saved pid) (fun p => write_saved pid p
    (fun p => {p with presharedKey := psk}) rfl)

theorem config_tail (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames) (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    Preserves (Driver.configTail ExchangeDriver.hooks a peer pid) := by
  unfold Driver.configTail peerAllowedIpsWith
  apply StatePrefixEnsures.bind (ambient _)
  intro has
  cases has with
  | false => exact config_finish facts a peer pid 0
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
        apply StatePrefixEnsures.bind (lift_tag _ (config.allowed pid ip))
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
        exact config_finish facts a peer pid ret

private theorem guard_and (d : Decision) (b : Bool) (e : Decision) (c : Bool) :
    Preserves (liftWGPrefix (WG.andM (branch d b) (branch e c))) := by
  apply lift
  intro h
  unfold WG.andM
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch d b) (StateInv h))
  intro yes
  cases yes with
  | false => exact preserves_pure false
  | true => exact hoare_liftAmbient (AmbientM.branch e c) (StateInv h)

open Lean Meta Elab Tactic in
elab "exchange_config_callback " name:ident : tactic => withMainContext do
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
    (remove setPsk replace : WGPrefix Event Unit) (endpoint : Endpoint → WGPrefix Event Unit)
    (out : Int → WGPrefix Event Int) (tail : WGPrefix Event Int)
    (hr : Preserves remove) (hs : Preserves setPsk) (hp : Preserves replace)
    (he : ∀ ep, Preserves (endpoint ep)) (ho : ∀ ret, Preserves (out ret)) (ht : Preserves tail) :
    Preserves (peerConfigUpdateWith (fun {_} a => liftWGPrefix a)
      remove setPsk replace endpoint out tail a flags psk) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) Safe _
  unfold peerConfigUpdateWith
  unfold StatePrefixPreserves
  cases a.endpoint
  all_goals repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (exchange_config_callback remove; exact hr)
    | (exchange_config_callback setPsk; exact hs)
    | (exchange_config_callback replace; exact hp)
    | (exchange_config_callback endpoint; exact he _)
    | (exchange_config_callback out; exact ho _)
    | (exchange_config_callback tail; exact ht)
    | (nonce_source_head WG.andM; exact guard_and _ _ _ _)
    | (first | nonce_source_head branch | nonce_source_head invariant
       exact ambient _)
    | (nonce_source_head Pure.pure; exact pure _)
    | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
    | maintenance_intro
    | maintenance_reduce
    | maintenance_reduce_match
    | split

theorem config_update (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames) (a : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    Preserves (Driver.configUpdate ExchangeDriver.hooks a peer flags psk pid) := by
  unfold Driver.configUpdate
  exact update_control a flags psk _ _ _ _ _ _ (remove_checked facts peer)
    (psk_write pid (psk.getD [])) (lift_tag _ (config.removeIps pid))
    (fun ep => lift_tag _ (config.endpoint pid ep)) (config_out a peer) (config_tail facts config a peer pid)

private theorem acquired_control (config : H1ConfigurationTagFrames)
    (out : Int → WGPrefix Event Int)
    (update : Option PeerId → UInt32 → Option Key → PeerId → WGPrefix Event Int)
    (ho : ∀ ret, Preserves (out ret)) (hu : ∀ p f k pid, Preserves (update p f k pid))
    (key : Key) (psk : Option Key) (flags : UInt32) (peer : Option PeerId) :
    Preserves (peerCommandAcquiredWith (fun {_} a => liftWGPrefix a)
      (fun key psk => liftWGPrefix (peerCreate key psk)) (fun pid => liftWGPrefix (peerGet pid))
      out update key psk flags peer) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) Safe _
  unfold peerCommandAcquiredWith
  unfold StatePrefixPreserves
  cases peer
  all_goals repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (exchange_config_callback out; exact ho _)
    | (exchange_config_callback update; exact hu _ _ _ _)
    | (nonce_source_head peerCreate; exact lift _ (fun h => frame h _ (config.create _ _)))
    | (nonce_source_head peerGet; exact lift_tag _ (config.peerGet _))
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

private theorem command_control (a : PeerAttrs) (out : Int → WGPrefix Event Int)
    (acquired : Key → Option Key → UInt32 → Option PeerId → WGPrefix Event Int)
    (ho : ∀ ret, Preserves (out ret)) (ha : ∀ k p f peer, Preserves (acquired k p f peer)) :
    Preserves (setPeerCmdWith (fun {_} a => liftWGPrefix a)
      (fun key => liftWGPrefix (pubkeyLookup key)) out acquired a) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) Safe _
  unfold setPeerCmdWith
  unfold StatePrefixPreserves
  cases a.publicKey
  all_goals repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (exchange_config_callback out; exact ho _)
    | (exchange_config_callback acquired; exact ha _ _ _ _)
    | (nonce_source_head pubkeyLookup; exact lift _ (pubkey_lookup _))
    | (nonce_source_head WG.andM; exact guard_and _ _ _ _)
    | (first | nonce_source_head branch | nonce_source_head invariant
       exact ambient _)
    | (nonce_source_head Pure.pure; exact pure _)
    | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
    | maintenance_intro
    | maintenance_reduce
    | maintenance_reduce_match
    | split

theorem config_peer (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames) (a : PeerAttrs) :
    Preserves (Driver.configPeer ExchangeDriver.hooks a) :=
  command_control a _ _ (config_out a none)
    (acquired_control config _ _ (config_out a none) (config_update facts config a))

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
