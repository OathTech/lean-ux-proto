import Leanux.Proofs.WG.TimerDiscipline.InitiationArm
import Leanux.Proofs.WG.Noise.StateEdges

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The fields connecting a timer dispatch to the next send worker. -/
abbrev InitiationView := Nat × Nat × Nat × Option UInt64

def initiationView (p : Peer) : InitiationView :=
  (p.internalId, p.timerHandshakeAttempts, p.refcount, p.timerRetransmitHandshake)

def initiationAt (w : World) (pid : PeerId) : Option InitiationView :=
  (peerAt w pid).map initiationView

theorem createInitiation_view (pid : PeerId) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ createInitiation pid
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  let P := fun k : Kernel => ((k.wg.bind fun d => d.peers[pid]?).map initiationView) = some v
  have hh := hidden_kernel_spec P
  have hg := generatePublic_kernel_spec P
  have he := messageEphemeral_kernel_spec P
  have hd := mixDh_kernel_spec P
  have hs := mixPrecomputedDh_kernel_spec P
  have hi := indexInsert_peers_spec (fun ps => (ps pid).map initiationView = some v)
  noise_vcgen [createInitiation, _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain,
    IndexOwner.peerDeref, IndexOwner.peerWord, unsupported, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, branch, invariant, hh, hg, he, hd, hs, hi]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [P, initiationAt, initiationView, peerAt, Option.bind_map,
    Function.comp_def, Std.TreeMap.getElem?_insert]
  all_goals grind

theorem addMacToPacket_view (pid : PeerId) (msg : List UInt8) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ addMacToPacket pid msg
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  have hh := hiddenClock64_kernel_spec
    (fun k => ((k.wg.bind fun d => d.peers[pid]?).map initiationView) = some v)
  mvcgen [addMacToPacket, Leanux.WG.andM, branchExpired, birthdateTest, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, branch, branchCmp, invariant, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [initiationAt, initiationView, peerAt, Option.bind_map,
    Function.comp_def, Std.TreeMap.getElem?_insert]
  all_goals grind

end Leanux.Proofs.WG.TimerDiscipline
