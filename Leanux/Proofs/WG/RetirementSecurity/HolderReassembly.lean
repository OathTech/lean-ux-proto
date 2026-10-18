import Leanux.Proofs.WG.RetirementSecurity.HolderPublication

/-! Reassembly at native source-group boundaries. Rotation briefly copies
slot pointers before overwriting their source, so an exact boundary account
need not hold between every two setters. The residual groups below come from
the actual old peer map, and their post-state residency is derived from the
post-payment equation. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG

structure PeerLedger (pid : PeerId) (p : Peer) (temporary : Credits.Ledger) (w : WGWorld) where
  device : Device
  hasDevice : w.dev = some device
  resident : device.peers[pid]? = some p
  loans : List KeyLoan
  named : peerLoans w pid p = some loans
  rest : List (List KeyLoan)
  restRun : (device.peers.toList.filter (fun pair => decide (¬ (pid == pair.1)))).mapM
    (fun (id,peer) => peerLoans w id peer) = some rest
  credits : Credits.Exact (loans.map (·.allocation) ++ rest.flatten.map (·.allocation) ++ temporary) w

theorem HolderAccount.split_peer (account : HolderAccount temporary w)
    (found : peerAt w pid = some p) : Nonempty (PeerLedger pid p temporary w) := by
  obtain ⟨loans,projected,credits⟩ := account
  cases device : w.dev with
  | none => simp [peerAt,device] at found
  | some d =>
    have peer : d.peers[pid]? = some p := by simpa [peerAt,device] using found
    cases mapped : d.peers.toList.mapM (fun (id,peer) => peerLoans w id peer) with
    | none => simp [durableLoans,device,mapped] at projected
    | some groups =>
      simp [durableLoans,device,mapped] at projected
      subst loans
      obtain ⟨ordered,orderedRun,orderedPerm⟩ := mapM_perm _ (peer_list_extract d.peers peer) mapped
      cases selected : peerLoans w pid p with
      | none => simp only [List.mapM_cons,selected] at orderedRun; cases orderedRun
      | some chosen =>
        cases restRun : (d.peers.toList.filter (fun pair => decide (¬ (pid == pair.1)))).mapM
            (fun (id,peer) => peerLoans w id peer) with
        | none => simp only [List.mapM_cons,selected,restRun] at orderedRun; cases orderedRun
        | some rest =>
          simp only [List.mapM_cons,selected,restRun] at orderedRun
          simp at orderedRun
          subst ordered
          refine ⟨⟨d,device,peer,chosen,selected,rest,restRun,?_⟩⟩
          simpa only [List.flatten_cons,List.map_append,List.append_assoc] using
            credits.perm ((orderedPerm.flatten.map (·.allocation)).append_right temporary)

theorem PeerLedger.reassemble (entry : PeerLedger pid p temporary w)
    (device : v.dev = some d) (q : Peer) (newLoans : List KeyLoan)
    (order : d.peers.toList.Perm ((pid,q) :: entry.device.peers.toList.filter
      (fun pair => decide (¬ (pid == pair.1)))))
    (packets : (carrierShape v).2 = (carrierShape w).2)
    (named : peerLoans v pid q = some newLoans)
    (credits : Credits.Exact
      (newLoans.map (·.allocation) ++ entry.rest.flatten.map (·.allocation) ++ temporary') v) :
    HolderAccount temporary' v := by
  have restRun := mapM_transport _ (fun (id,peer) => peerLoans v id peer)
    _ _ entry.restRun (by
      intro pair group member found
      apply peerLoans_packets pair.1 pair.2 group packets found
      intro loan inside
      have held : loan.allocation ∈ newLoans.map (·.allocation) ++
          entry.rest.flatten.map (·.allocation) ++ temporary' := by
        have flat : loan ∈ entry.rest.flatten := List.mem_flatten.mpr ⟨group,member,inside⟩
        simp only [List.mem_append]
        exact Or.inl (Or.inr (List.mem_map_of_mem flat))
      obtain ⟨k,resident,stamp,_⟩ := credits.resident held
      exact ⟨k,resident,stamp⟩)
  have orderedRun : ((pid,q) :: entry.device.peers.toList.filter
      (fun pair => decide (¬ (pid == pair.1)))).mapM
      (fun (id,peer) => peerLoans v id peer) = some (newLoans :: entry.rest) := by
    simp only [List.mapM_cons,named,restRun]
    rfl
  obtain ⟨groups,mapped,permuted⟩ := mapM_perm _ order.symm orderedRun
  refine ⟨groups.flatten,?_,?_⟩
  · simp only [durableLoans,device,mapped]
    rfl
  · apply credits.perm
    simpa only [List.flatten_cons,List.map_append,List.append_assoc] using
      (permuted.flatten.map (·.allocation)).append_right temporary'

end Leanux.Proofs.WG.RetirementSecurity
