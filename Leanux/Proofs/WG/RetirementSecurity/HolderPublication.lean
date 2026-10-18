import Leanux.Proofs.WG.RetirementSecurity.HolderEntry

/-! Physical holder publication/removal through the original peer setter.
Only the selected peer's concrete loan list is exchanged; all other peer
groups are read from the native map and retained with their multiplicities. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG

theorem mapM_perm {xs zs : List α} {ys : List β} (f : α → Option β) (order : xs.Perm zs)
    (run : xs.mapM f = some ys) :
    ∃ ws, zs.mapM f = some ws ∧ ys.Perm ws := by
  induction order generalizing ys with
  | nil =>
    simp at run
    subst ys
    exact ⟨[],rfl,.nil⟩
  | cons x order ih =>
    rename_i left right
    cases first : f x with
    | none => simp [List.mapM_cons,first] at run
    | some y =>
      cases rest : List.mapM f left with
      | none => simp [List.mapM_cons,first,rest] at run
      | some tail =>
        simp [List.mapM_cons,first,rest] at run
        subst ys
        obtain ⟨other,mapped,permuted⟩ := ih rest
        exact ⟨y :: other,by simp [List.mapM_cons,first,mapped],permuted.cons y⟩
  | swap x y tail =>
    cases fx : f x <;> cases fy : f y <;> cases rest : tail.mapM f
    all_goals simp [List.mapM_cons,fx,fy,rest] at run
    all_goals subst ys
    all_goals exact ⟨_,by simp [List.mapM_cons,fx,fy,rest],List.Perm.swap _ _ _⟩
  | trans first second ih1 ih2 =>
    obtain ⟨middle,mapped,permuted⟩ := ih1 run
    obtain ⟨result,mapped',permuted'⟩ := ih2 mapped
    exact ⟨result,mapped',permuted.trans permuted'⟩

def replacePeer (w : WGWorld) (d : Device) (pid : PeerId) (q : Peer) : WGWorld :=
  {w with dev := some {d with peers := d.peers.insert pid q}}

theorem replacePeer_loans (device : w.dev = some d) (pid : PeerId) (q : Peer)
    (other : PeerId) (p : Peer) :
    peerLoans (replacePeer w d pid q) other p = peerLoans w other p := by
  have names (holder : KeyHolder) :
      nameLoan (replacePeer w d pid q) holder = nameLoan w holder := by
    funext key
    simp [nameLoan,keyAt,replacePeer,device]
  simp only [peerLoans,names]
  simp [replacePeer,device]

theorem replacePeer_account (device : w.dev = some d) (pid : PeerId) (q : Peer)
    (account : Credits.Exact credits w) :
    Credits.Exact credits (replacePeer w d pid q) := by
  intro allocation
  simpa [Credits.balance,keyAt,replacePeer,device] using account allocation

theorem peer_list_extract (peers : Std.TreeMap PeerId Peer compare)
    (found : peers[pid]? = some p) :
    peers.toList.Perm ((pid,p) :: peers.toList.filter (fun pair => decide (¬ (pid == pair.1)))) := by
  have unchanged : (peers.insert pid p).toList = peers.toList := by
    apply Std.TreeMap.Equiv.toList_eq
    apply Std.TreeMap.Equiv.of_forall_constGet?_eq
    intro id
    by_cases same : pid = id
    · subst id
      simp [found]
    · simp [Std.TreeMap.getElem?_insert,same]
  simpa only [unchanged] using (Std.TreeMap.toList_insert_perm (t := peers) (k := pid) (v := p))

theorem HolderAccount.replace_peer (account : HolderAccount temporary w)
    (device : w.dev = some d) (found : d.peers[pid]? = some p)
    (old : peerLoans w pid p = some oldLoans)
    (new : peerLoans w pid q = some newLoans)
    (transfer : (oldLoans.map (·.allocation) ++ temporary).Perm
      (newLoans.map (·.allocation) ++ temporary')) :
    HolderAccount temporary' (replacePeer w d pid q) := by
  obtain ⟨loans,projected,credits⟩ := account
  cases mapped : d.peers.toList.mapM (fun (id,peer) => peerLoans w id peer) with
  | none => simp [durableLoans,device,mapped] at projected
  | some groups =>
    simp [durableLoans,device,mapped] at projected
    subst loans
    obtain ⟨ordered,orderedRun,orderedPerm⟩ := mapM_perm _ (peer_list_extract d.peers found) mapped
    cases restRun : (d.peers.toList.filter (fun pair => decide (¬ (pid == pair.1)))).mapM
        (fun (id,peer) => peerLoans w id peer) with
    | none =>
      simp only [List.mapM_cons,old,restRun] at orderedRun
      cases orderedRun
    | some rest =>
      simp only [List.mapM_cons,old,restRun] at orderedRun
      simp at orderedRun
      subst ordered
      have newOrdered : ((pid,q) :: d.peers.toList.filter (fun pair => decide (¬ (pid == pair.1)))).mapM
          (fun (id,peer) => peerLoans w id peer) = some (newLoans :: rest) := by
        simp only [List.mapM_cons,new,restRun]
        rfl
      obtain ⟨newGroups,newMapped,newPerm⟩ := mapM_perm _
        (Std.TreeMap.toList_insert_perm (t := d.peers) (k := pid) (v := q)).symm newOrdered
      have finalMapped : (d.peers.insert pid q).toList.mapM
          (fun (id,peer) => peerLoans (replacePeer w d pid q) id peer) = some newGroups := by
        simpa only [replacePeer_loans device pid q] using newMapped
      refine ⟨newGroups.flatten,?_,?_⟩
      · change (do
          let groups ← (d.peers.insert pid q).toList.mapM
            (fun (id,peer) => peerLoans (replacePeer w d pid q) id peer)
          pure groups.flatten) = some newGroups.flatten
        rw [finalMapped]
        rfl
      · apply replacePeer_account device pid q
        apply credits.perm
        apply List.perm_iff_count.mpr
        intro allocation
        have before := ((orderedPerm.flatten.map (·.allocation)).append_right temporary).count_eq allocation
        have after := ((newPerm.flatten.map (·.allocation)).append_right temporary').count_eq allocation
        have move := transfer.count_eq allocation
        simp only [List.flatten_cons,List.map_append,List.count_append] at before after move ⊢
        omega

theorem HolderAccount.set_peer (account : HolderAccount temporary w)
    (found : peerAt w pid = some p)
    (old : peerLoans w pid p = some oldLoans)
    (new : peerLoans w pid q = some newLoans)
    (transfer : (oldLoans.map (·.allocation) ++ temporary).Perm
      (newLoans.map (·.allocation) ++ temporary')) (a b : Ambient)
    (run : ((setPeer pid q).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary' v := by
  cases device : w.dev with
  | none => simp [peerAt,device] at found
  | some d =>
    have peer : d.peers[pid]? = some p := by simpa [peerAt,device] using found
    have result : v = replacePeer w d pid q := by
      have equality : replacePeer w d pid q = v ∧ a = b := by
        simpa [setPeer,modifyDev,device,replacePeer] using run
      exact equality.1.symm
    subst v
    exact account.replace_peer device peer old new transfer

end Leanux.Proofs.WG.RetirementSecurity
