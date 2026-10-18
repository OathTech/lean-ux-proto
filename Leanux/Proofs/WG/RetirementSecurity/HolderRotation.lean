import Leanux.Proofs.WG.RetirementSecurity.PerimeterFrames

/-! Native rotation/confirmation at the concrete holder boundary. The old
account is split by actual peer-map occurrences, the original source's exact
reference equation is applied, and the actual post-state projection is rebuilt.
Intermediate pointer copies are not mistaken for acquired references. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem PeerLedger.finish_slots (entry : PeerLedger pid p temporary w)
    (parts : PeerParts w pid p entry.loans) (q : Peer) (slots : SlotLoans)
    (selected : peerAt v pid = some q) (aligned : slots.Aligned q)
    (tx : q.txQueue = p.txQueue) (rx : q.rxQueue = p.rxQueue)
    (perimeter : holderPerimeter pid v = holderPerimeter pid w)
    (credits : Credits.Exact (slots.credits ++ ((parts.tx ++ parts.rx).map (·.allocation) ++
      (entry.rest.flatten.map (·.allocation) ++ temporary'))) v) :
    HolderAccount temporary' v := by
  have packets := congrArg (fun view => view.2) perimeter
  obtain ⟨loans,named,loanCredits⟩ := parts.rebuild q slots aligned tx rx packets
    (by simpa only [List.append_assoc] using credits)
  cases device : v.dev with
  | none => simp [peerAt,device] at selected
  | some d =>
    apply entry.reassemble device q loans
      (perimeter_peer_order entry.hasDevice device selected perimeter) packets named
    simpa only [loanCredits,List.append_assoc] using credits

theorem HolderAccount.confirm (account : HolderAccount temporary w)
    (pid : PeerId) (key : KeypairId) (a b : Ambient)
    (run : ((receivedWithKeypair pid key).run w).run a = .ok ((result,v),b)) :
    HolderAccount temporary v := by
  have source := run
  rw [receivedWithKeypair,MaterialOrigin.bind_ok_ambient] at source
  obtain ⟨p,u,c,readRun,_⟩ := source
  obtain ⟨_,_,d,device,peer⟩ := Origins.getPeer_return pid w u p a c readRun
  have found : peerAt w pid = some p := by simp [peerAt,device,peer]
  obtain ⟨entry⟩ := account.split_peer found
  obtain ⟨parts⟩ := peer_parts entry.named
  let remaining := (parts.tx ++ parts.rx).map (·.allocation) ++
    (entry.rest.flatten.map (·.allocation) ++ temporary)
  have funded : PeerAccount pid p (parts.slots.credits ++ remaining) w :=
    ⟨found,by simpa only [parts.credits,List.append_assoc] using entry.credits⟩
  have perimeter := (ProjectedAction.iff_run_ambient _ _ _).mp
    (confirmation_perimeter pid key) w a result v b run
  by_cases next : p.keypairNext = some key
  · have completed := (hoare_iff_run_ambient _ _ _).mp
      (confirmation_account pid p parts.slots remaining key parts.aligned next)
        w a result v b funded run
    exact entry.finish_slots parts (confirmedPeer p key) parts.slots.confirm completed.2.1
      (SlotLoans.confirm_aligned parts.aligned next) rfl rfl perimeter completed.2.2
  · have completed := (hoare_iff_run_ambient _ _ _).mp
      (confirmation_refused_account pid p (parts.slots.credits ++ remaining) key next)
        w a result v b funded run
    exact entry.finish_slots parts p parts.slots completed.2.1 parts.aligned rfl rfl
      perimeter completed.2.2

theorem HolderAccount.rotate (account : HolderAccount (newKey :: temporary) w)
    (pid : PeerId) (a b : Ambient)
    (run : ((addNewKeypair pid newKey.slot).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := by
  have source := run
  rw [rotation_source,MaterialOrigin.bind_ok_ambient] at source
  obtain ⟨p,u,c,readRun,_⟩ := source
  obtain ⟨_,_,d,device,peer⟩ := Origins.getPeer_return pid w u p a c readRun
  have found : peerAt w pid = some p := by simp [peerAt,device,peer]
  obtain ⟨entry⟩ := account.split_peer found
  obtain ⟨parts⟩ := peer_parts entry.named
  let remaining := (parts.tx ++ parts.rx).map (·.allocation) ++
    (entry.rest.flatten.map (·.allocation) ++ temporary)
  have funded : PeerAccount pid p (newKey :: parts.slots.credits ++ remaining) w := by
    refine ⟨found,entry.credits.perm ?_⟩
    apply List.perm_iff_count.mpr
    intro allocation
    simp only [parts.credits,remaining,List.count_append,List.count_cons]
    omega
  obtain ⟨k,resident,_,_⟩ := funded.2.resident (allocation := newKey) (by simp)
  have completed := rotation_account pid p parts.slots newKey remaining k
    parts.aligned funded resident a b run
  have perimeter := (ProjectedAction.iff_run_ambient _ _ _).mp
    (rotation_perimeter pid newKey.slot) w a () v b run
  apply entry.finish_slots parts (rotatedPeer p newKey.slot k.iAmTheInitiator)
    (parts.slots.rotate newKey k.iAmTheInitiator p.keypairNext.isSome)
    completed.1 (SlotLoans.rotate_aligned parts.aligned newKey k.iAmTheInitiator)
    ?_ ?_ perimeter completed.2
  all_goals cases k.iAmTheInitiator <;> cases h : p.keypairNext.isSome <;>
    simp [rotatedPeer,h]

end Leanux.Proofs.WG.RetirementSecurity
