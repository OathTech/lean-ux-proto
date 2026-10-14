import Leanux.Proofs.WG.Lifetimes.AllocationRetention
import Leanux.Proofs.Framing.Projection

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! Receive queues indexed by peer slot and tagged with device interface index and peer
identity. Retention allows deletion; it does not identify a replacement peer
with an old peer or assume that generic lifetime contracts preserve queues. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

structure RxQueueCell where
  epoch : Nat
  stamp : Nat
  queue : PrevQueue SkbId

def rxMap (epoch : Nat) (peers : Std.TreeMap Nat Peer) : PeerId → Option RxQueueCell :=
  fun i => peers[i]?.map fun p => ⟨epoch, p.internalId, p.rxQueue⟩

def rxQueues (w : World) : PeerId → Option RxQueueCell :=
  fun i => w.k.wg.bind fun d => rxMap d.ifindex d.peers i

abbrev RetainsRx (a : M α) := ProjectedAction rxQueues ResidentsRetained a

theorem rx_retained_refl (s : PeerId → Option RxQueueCell) : ResidentsRetained s s :=
  fun _ _ h => h

theorem rx_retained_trans {a b c : PeerId → Option RxQueueCell}
    (hab : ResidentsRetained a b) (hbc : ResidentsRetained b c) : ResidentsRetained a c :=
  fun i x h => hab i x (hbc i x h)

theorem rxQueues_kernel (ha : SameKernel a) : SameView rxQueues a := by
  intro w x v hr
  unfold rxQueues
  rw [ha w x v hr]

theorem rxMap_insert_same (epoch : Nat) (peers : Std.TreeMap Nat Peer)
    (i : PeerId) (old p : Peer) (hp : peers[i]? = some old)
    (hs : p.internalId = old.internalId) (hq : p.rxQueue = old.rxQueue) :
    rxMap epoch (peers.insert i p) = rxMap epoch peers := by
  funext j
  simp only [rxMap, Std.TreeMap.getElem?_insert]
  split <;> simp_all

theorem rxMap_insert_retained (epoch : Nat) (peers : Std.TreeMap Nat Peer)
    (i : PeerId) (old p : Peer) (hp : peers[i]? = some old)
    (hs : p.internalId = old.internalId) (hq : p.rxQueue = old.rxQueue) :
    ResidentsRetained (rxMap epoch peers) (rxMap epoch (peers.insert i p)) := by
  rw [rxMap_insert_same epoch peers i old p hp hs hq]
  exact rx_retained_refl _

theorem rxMap_erase (epoch : Nat) (peers : Std.TreeMap Nat Peer) (i : PeerId) :
    ResidentsRetained (rxMap epoch peers) (rxMap epoch (peers.erase i)) := by
  intro j x hx
  simp only [rxMap, Std.TreeMap.getElem?_erase] at hx ⊢
  split at hx <;> simp_all

theorem rxMap_insert_erase (epoch : Nat) (peers : Std.TreeMap Nat Peer)
    (i : PeerId) (p : Peer) :
    ResidentsRetained (rxMap epoch peers) (rxMap epoch ((peers.insert i p).erase i)) := by
  intro j x hx
  simp only [rxMap, Std.TreeMap.getElem?_erase, Std.TreeMap.getElem?_insert,
    Std.LawfulEqOrd.compare_eq_iff_eq] at hx ⊢
  by_cases h : i = j <;> simp_all [eq_comm]

/-- An original fresh getter followed by a queue/identity-preserving update
frames the complete queue view. The live getter is essential. -/
theorem modifyPeer_rxQueues (pid : PeerId) (f : Peer → Peer)
    (hs : ∀ p, (f p).internalId = p.internalId)
    (hq : ∀ p, (f p).rxQueue = p.rxQueue) :
    SameView rxQueues (do let p ← getPeer pid; setPeer pid (f p)) := by
  apply SameView.of_wp
  intro s
  mvcgen [Peers.getPeer_spec, setPeer, modifyDev, modifyK]
  dsimp +zetaDelta only at *
  obtain ⟨rfl, d, hd, hp⟩ := ‹_ ∧ ∃ _, _ ∧ _›
  subst s
  funext j
  simp only [rxQueues, hd, Option.bind_some, Option.map_some]
  exact congrFun (rxMap_insert_same _ _ _ _ _ hp (hs _) (hq _)) j

end Leanux.Proofs.WG.Queues
