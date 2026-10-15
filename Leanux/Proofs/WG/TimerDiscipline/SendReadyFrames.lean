import Leanux.Proofs.WG.Noise.PeerFrames
import Leanux.Proofs.WG.Noise.InitiationReadySource

set_option autoImplicit false
set_option pp.structureInstances false

/-! Allocation-arming metadata is preserved by initiation and index insertion. -/
namespace Leanux.Proofs.WG.TimerDiscipline.SendReady
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem bucketHas_allocArmed (allocArmed : List String) (walk collide : Decision) (index : Nat) :
    ⦃fun w => ⌜w.allocArmed = allocArmed⌝⦄ (noise_const _private.Leanux.WG.Peer.«0».Leanux.WG.bucketHas) walk collide index
      ⦃⇓? _ w => ⌜w.allocArmed = allocArmed⌝⦄ := by
  noise_vcgen [_private.Leanux.WG.Peer.«0».Leanux.WG.bucketHas,
    indexBucket, getDev, getK, branch, invariant]
  case inv1 => exact ((⇓? _ w => ⌜w.allocArmed = allocArmed⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals trivial

theorem indexInsert_allocArmed (allocArmed : List String) (owner : IndexOwner) :
    ⦃fun w => ⌜w.allocArmed = allocArmed⌝⦄ indexInsert owner
      ⦃⇓? _ w => ⌜w.allocArmed = allocArmed⌝⦄ := by
  have hh (site : HiddenSite) :
      ⦃fun w => ⌜w.allocArmed = allocArmed⌝⦄ hidden site
        ⦃⇓? _ w => ⌜w.allocArmed = allocArmed⌝⦄ := by
    mvcgen [hidden, skipAmbient, noteNetRxStart]
  have hb := bucketHas_allocArmed allocArmed
  noise_vcgen [indexInsert, _private.Leanux.WG.Peer.«0».Leanux.WG.unhashEntry,
    getDev, getK, branch, invariant, unsupported, recordBudget, budgetExhausted,
    modifyDev, modifyK, hh, hb]
  case inv1 => exact ((⇓? _ w => ⌜w.allocArmed = allocArmed⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals trivial

theorem createInitiation_allocArmed (allocArmed : List String) (pid : PeerId) :
    ⦃fun w => ⌜w.allocArmed = allocArmed⌝⦄ createInitiation pid
      ⦃⇓? _ w => ⌜w.allocArmed = allocArmed⌝⦄ := by
  have hh (site : HiddenSite) :
      ⦃fun w => ⌜w.allocArmed = allocArmed⌝⦄ hidden site
        ⦃⇓? _ w => ⌜w.allocArmed = allocArmed⌝⦄ := by
    mvcgen [hidden, skipAmbient, noteNetRxStart]
  have hk (second third : Bool) (ck data : List UInt8) :
      ⦃fun w => ⌜w.allocArmed = allocArmed⌝⦄ kdf second third ck data
        ⦃⇓? _ w => ⌜w.allocArmed = allocArmed⌝⦄ := by
    mvcgen [kdf, Leanux.WG.orM, branch]
  have ho (outs : List (List UInt8)) (i : Nat) :
      ⦃fun w => ⌜w.allocArmed = allocArmed⌝⦄ kdfOut outs i
        ⦃⇓? _ w => ⌜w.allocArmed = allocArmed⌝⦄ := by
    mvcgen [kdfOut, invariant]
  have hg (secret : Key) :
      ⦃fun w => ⌜w.allocArmed = allocArmed⌝⦄ generatePublic secret
        ⦃⇓? _ w => ⌜w.allocArmed = allocArmed⌝⦄ := by
    mvcgen [generatePublic, branch]
  have he (copy : Bool) (e ck hash : List UInt8) :
      ⦃fun w => ⌜w.allocArmed = allocArmed⌝⦄ messageEphemeral copy e ck hash
        ⦃⇓? _ w => ⌜w.allocArmed = allocArmed⌝⦄ := by
    mvcgen [messageEphemeral, branch, hk, ho]
  have hd (key : Bool) (ck priv pub : List UInt8) :
      ⦃fun w => ⌜w.allocArmed = allocArmed⌝⦄ mixDh key ck priv pub
        ⦃⇓? _ w => ⌜w.allocArmed = allocArmed⌝⦄ := by
    mvcgen [mixDh, branch, hk, ho]
  have hs (ck precomputed : List UInt8) :
      ⦃fun w => ⌜w.allocArmed = allocArmed⌝⦄ mixPrecomputedDh ck precomputed
        ⦃⇓? _ w => ⌜w.allocArmed = allocArmed⌝⦄ := by
    mvcgen [mixPrecomputedDh, branch, hk, ho]
  have hi := indexInsert_allocArmed allocArmed
  noise_vcgen [createInitiation, _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain,
    IndexOwner.peerDeref, IndexOwner.peerWord, getDev, getK, getPeer, setPeer,
    modifyDev, modifyK, branch, invariant, unsupported, hh, hi, hg, he, hd, hs]

end Leanux.Proofs.WG.TimerDiscipline.SendReady
