import Leanux.Proofs.WG.RetirementSecurity.HolderShutdown
import Leanux.Proofs.WG.RetirementSecurity.ConfiguredSessionFunding

/-! A freshly allocated peer has no published key slots or packet queues.
Insertion therefore adds no key-reference demand. Native frontier vacancy is
derived from the configured registry, independently of key credit. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem HolderAccount.insert_empty_peer (account : HolderAccount temporary w)
    (device : w.dev = some d) (vacant : d.peers[pid]? = none)
    (empty : peerLoans w pid p = some []) :
    HolderAccount temporary (replacePeer w d pid p) := by
  obtain ⟨loans,projected,credits⟩ := account
  cases mapped : d.peers.toList.mapM (fun (id,peer) => peerLoans w id peer) with
  | none => simp [durableLoans,device,mapped] at projected
  | some groups =>
    simp [durableLoans,device,mapped] at projected
    subst loans
    have filter : d.peers.toList.filter (fun pair => decide (¬ (pid == pair.1))) = d.peers.toList := by
      apply List.filter_eq_self.mpr
      intro pair member
      have found := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp member
      have different : pid ≠ pair.1 := by
        intro same
        rw [←same,vacant] at found
        cases found
      simpa using different
    have ordered : ((pid,p)::d.peers.toList).mapM (fun (id,peer) => peerLoans w id peer) =
        some ([]::groups) := by simp [List.mapM_cons,empty,mapped]
    have order := Std.TreeMap.toList_insert_perm (t := d.peers) (k := pid) (v := p)
    rw [filter] at order
    obtain ⟨after,afterRun,permuted⟩ := mapM_perm _ order.symm ordered
    have finalMapped : (d.peers.insert pid p).toList.mapM
        (fun (id,peer) => peerLoans (replacePeer w d pid p) id peer) = some after := by
      simpa only [replacePeer_loans device pid p] using afterRun
    refine ⟨after.flatten,?_,?_⟩
    · change (do
        let peers ← (d.peers.insert pid p).toList.mapM
          (fun (id,peer) => peerLoans (replacePeer w d pid p) id peer)
        pure peers.flatten) = _
      rw [finalMapped]
      rfl
    · apply replacePeer_account device pid p
      apply credits.perm
      simpa only [List.flatten_cons,List.nil_append] using
        (permuted.flatten.map (·.allocation)).append_right temporary

theorem HolderAccount.peer_create_core (account : HolderAccount temporary w)
    (configured : ConfiguredIdentity.Inv w) (device : w.dev = some d) (key : Key) :
    HolderAccount temporary (Peers.creationCoreWorld w d.nextPeer key) := by
  let before : WGWorld := {w with peerCounter := w.peerCounter+1, dev := some {d with nextPeer := d.nextPeer+1}}
  have points : ownershipPointView before = ownershipPointView w := by
    unfold ownershipPointView RetirementSecurity.keyReferenceView RetirementSecurity.keyAt ownershipAt peerAt packetKeyWords
    simp [before,device]
  have added := (account.points points).insert_empty_peer (pid := d.nextPeer)
    (p := Peers.createdPeer key (w.peerCounter+1)) (device := rfl)
    (BaseCreation.frontier_vacant configured device) (by simp [peerLoans,Peers.createdPeer,PrevQueue.all])
  simpa only [before,replacePeer,Peers.creationCoreWorld,device,Option.map_some] using added

end Leanux.Proofs.WG.RetirementSecurity
