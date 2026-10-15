import Leanux.Proofs.WG.Noise.PeerFrames
import Leanux.Proofs.WG.Noise.InitiationReadySource

set_option autoImplicit false
set_option pp.structureInstances false

/-! Recorded timer mode is independent of original initiation and index insertion.
These removable frames are separate from the initiation output claim. -/
namespace Leanux.Proofs.WG.Noise.InitiationReady
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem bucketHas_mode (mode : Bool) (walk collide : Decision) (index : Nat) :
    ⦃fun w => ⌜w.armRecords = mode⌝⦄ (noise_const _private.Leanux.WG.Peer.«0».Leanux.WG.bucketHas) walk collide index
      ⦃⇓? _ w => ⌜w.armRecords = mode⌝⦄ := by
  noise_vcgen [_private.Leanux.WG.Peer.«0».Leanux.WG.bucketHas,
    indexBucket, getDev, getK, branch, invariant]
  case inv1 => exact ((⇓? _ w => ⌜w.armRecords = mode⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals trivial

theorem indexInsert_mode (mode : Bool) (owner : IndexOwner) :
    ⦃fun w => ⌜w.armRecords = mode⌝⦄ indexInsert owner
      ⦃⇓? _ w => ⌜w.armRecords = mode⌝⦄ := by
  have hh (site : HiddenSite) :
      ⦃fun w => ⌜w.armRecords = mode⌝⦄ hidden site
        ⦃⇓? _ w => ⌜w.armRecords = mode⌝⦄ := by
    mvcgen [hidden, skipAmbient, noteNetRxStart]
  have hb := bucketHas_mode mode
  noise_vcgen [indexInsert, _private.Leanux.WG.Peer.«0».Leanux.WG.unhashEntry,
    getDev, getK, branch, invariant, unsupported, recordBudget, budgetExhausted,
    modifyDev, modifyK, hh, hb]
  case inv1 => exact ((⇓? _ w => ⌜w.armRecords = mode⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals trivial

theorem createInitiation_mode (mode : Bool) (pid : PeerId) :
    ⦃fun w => ⌜w.armRecords = mode⌝⦄ createInitiation pid
      ⦃⇓? _ w => ⌜w.armRecords = mode⌝⦄ := by
  have hh (site : HiddenSite) :
      ⦃fun w => ⌜w.armRecords = mode⌝⦄ hidden site
        ⦃⇓? _ w => ⌜w.armRecords = mode⌝⦄ := by
    mvcgen [hidden, skipAmbient, noteNetRxStart]
  have hk (second third : Bool) (ck data : List UInt8) :
      ⦃fun w => ⌜w.armRecords = mode⌝⦄ kdf second third ck data
        ⦃⇓? _ w => ⌜w.armRecords = mode⌝⦄ := by
    mvcgen [kdf, Leanux.WG.orM, branch]
  have ho (outs : List (List UInt8)) (i : Nat) :
      ⦃fun w => ⌜w.armRecords = mode⌝⦄ kdfOut outs i
        ⦃⇓? _ w => ⌜w.armRecords = mode⌝⦄ := by
    mvcgen [kdfOut, invariant]
  have hg (secret : Key) :
      ⦃fun w => ⌜w.armRecords = mode⌝⦄ generatePublic secret
        ⦃⇓? _ w => ⌜w.armRecords = mode⌝⦄ := by
    mvcgen [generatePublic, branch]
  have he (copy : Bool) (e ck hash : List UInt8) :
      ⦃fun w => ⌜w.armRecords = mode⌝⦄ messageEphemeral copy e ck hash
        ⦃⇓? _ w => ⌜w.armRecords = mode⌝⦄ := by
    mvcgen [messageEphemeral, branch, hk, ho]
  have hd (key : Bool) (ck priv pub : List UInt8) :
      ⦃fun w => ⌜w.armRecords = mode⌝⦄ mixDh key ck priv pub
        ⦃⇓? _ w => ⌜w.armRecords = mode⌝⦄ := by
    mvcgen [mixDh, branch, hk, ho]
  have hs (ck precomputed : List UInt8) :
      ⦃fun w => ⌜w.armRecords = mode⌝⦄ mixPrecomputedDh ck precomputed
        ⦃⇓? _ w => ⌜w.armRecords = mode⌝⦄ := by
    mvcgen [mixPrecomputedDh, branch, hk, ho]
  have hi := indexInsert_mode mode
  noise_vcgen [createInitiation, _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain,
    IndexOwner.peerDeref, IndexOwner.peerWord, getDev, getK, getPeer, setPeer,
    modifyDev, modifyK, branch, invariant, unsupported, hh, hi, hg, he, hd, hs]

end Leanux.Proofs.WG.Noise.InitiationReady
