import Leanux.Proofs.WG.Roaming.InitiationConsumeErasureSource
import Leanux.Proofs.WG.Roaming.InitiationCryptoSource
import Leanux.Proofs.WG.Roaming.InitiationLookupSource
import Leanux.Proofs.WG.Roaming.PollEndpointSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem initiationFinish_facts (msg : List UInt8) (identity : StaticIdentity) (s : Key)
    (pid : PeerId) (lookup : InitiationLookup) (dhPeer : Peer) (beforeDh : Campaign2.Snapshot)
    (ck timestamp hash : List UInt8) :
    Ensures (initiationFinish msg identity s pid lookup dhPeer beforeDh ck timestamp hash)
      (fun _ => True)
      (fun result w => ∀ cut, result = some cut →
        cut.committed = Campaign2.snapshot w ∧ cut.identity = identity ∧
        cut.staticPlain = s ∧ cut.timestamp = timestamp ∧ cut.pid = pid ∧
        cut.lookup = lookup ∧ cut.dhPeer = dhPeer ∧ cut.beforeDh = beforeDh ∧
        InitiationCommitFacts msg ck hash cut) := by
  rw [ensures_iff]
  have snapshot_peer (w : World) (pid : PeerId) :
      (Campaign2.snapshot w).peerAt pid = (w.k.wg.bind fun d => d.peers[pid]?) := rfl
  have hg := fun initial => getPeer_spec pid (fun w => peerAt w pid = initial)
  have hs (p : Peer) : ⦃fun w => ⌜(peerAt w pid).isSome⌝⦄ setPeer pid p
      ⦃⇓? _ w => ⌜peerAt w pid = some p⌝⦄ := by
    have setter := setPeer_spec pid p (fun q => q = p)
    mvcgen [setter]
    all_goals simp_all
  have hh := fun initial site => hiddenClock64_kernel_spec
    (fun k => (k.wg.bind fun d => d.peers[pid]?) = initial) site
  have hr := fun initial => read_snapshot (fun w => peerAt w pid = initial)
  have ho := initiationOut_effect
  mvcgen -trivial [initiationFinish, branch, branchCmp, WG.orM, invariant, hg, hs, hh, hr, ho]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try simp_all [InitiationCommitFacts, initiationEphemeral, snapshot_peer,
    peerAt, ExceptConds.true]
  all_goals try simp_all only [heq_eq_eq]
  all_goals repeat intro
  all_goals try subst_vars
  all_goals try simp_all [snapshot_peer]
  all_goals grind only [Option.isSome_some]

theorem initiationConsume_facts (msg : List UInt8) :
    Ensures (initiationConsume msg) (fun _ => True)
      (fun result w => ∀ cut, result = some cut →
        cut.committed = Campaign2.snapshot w ∧ InitiationConsumedFacts msg cut) := by
  rw [ensures_iff]
  have snapshot_peer (w : World) (pid : PeerId) :
      (Campaign2.snapshot w).peerAt pid = (w.k.wg.bind fun d => d.peers[pid]?) := rfl
  have he := fun e ck hash => responseEphemeral_returns e ck hash (fun _ => True)
  have hd := fun ck priv pub => initiationDh_returns ck priv pub (fun _ => True)
  have hm := fun sealed key hash => responseDecrypt_returns sealed key hash (fun _ => True)
  have hs := fun ck precomputed => initiationPrecomputed_returns ck precomputed (fun _ => True)
  have hl := fun key => (ensures_iff _ _ _).mp (initiationLookup_facts key)
  have hr := fun initial => read_snapshot (fun w => w.k = initial)
  have ht := fun identity s pid lookup dhPeer beforeDh ck timestamp hash =>
    (ensures_iff _ _ _).mp (initiationFinish_facts msg identity s pid lookup dhPeer beforeDh ck timestamp hash)
  have hp (peer : Option PeerId) : ⦃fun _ => ⌜True⌝⦄ peerPut peer ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro w x final pre run
    trivial
  have ho := initiationOut_effect
  mvcgen [initiationConsume, getPeer, getDev, getK,
    branch, invariant, he, hd, hm, hs, hl, hr, ht, ho]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [InitiationConsumedFacts, initiationEphemeral,
    initiationEsInput, initiationDh, initiationEsChain, initiationStaticKey,
    initiationStaticAad, initiationTimestampAad, snapshot_peer]
  all_goals grind

end Leanux.Proofs.WG.Roaming
