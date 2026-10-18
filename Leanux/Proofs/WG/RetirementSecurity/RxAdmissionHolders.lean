import Leanux.Proofs.WG.RetirementSecurity.RxLookupHolders

/-! Successful native receive admission supplies one concrete saved key
reference and a fresh detached packet. The peer-release condition is derived
from its own index lookup borrow, separately from the key credit. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem get_some_resident (id : KeypairId) (a b : Ambient)
    (run : ((keypairGet (some id)).run w).run a = .ok ((some id,v),b)) :
    ∃ k, keyAt w id = some k := by
  cases device : w.dev with
  | none =>
    simp [keypairGet,branch,AmbientM.branch,getKeypair,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases found : d.keypairs[id]? with
    | none =>
      simp [keypairGet,branch,AmbientM.branch,getKeypair,getDev,device,found,invariant,AmbientM.invariant] at run
      cases run
    | some k => exact ⟨k,by simp [keyAt,device,found]⟩

theorem HolderAccount.receive_key (account : HolderAccount temporary w)
    (entry : Option (IndexOwner × PeerId)) (a b : Ambient)
    (run : ((Affiliation.receiveKeyAcquire entry).run w).run a = .ok (((some kid,some pid),v),b)) :
    ∃ allocation : Credits.Allocation, allocation.slot = kid ∧
      HolderAccount (allocation :: temporary) v := by
  have entrySame := ((hoare_iff_run_ambient _ _ _).mp
    (Affiliation.receiveKeyAcquire_spec entry (Affiliation.view w))
    w a (some kid,some pid) v b rfl run).2 kid pid rfl
  subst entry
  simp only [Affiliation.receiveKeyAcquire,pure_bind,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨out,u,c,getRun,tail⟩ := run
  cases tail
  obtain ⟨k,found⟩ := get_some_resident kid a b getRun
  exact ⟨⟨kid,k.internalId⟩,rfl,account.get kid k found a b getRun⟩

theorem lookup_loan_ready (loan : Queues.RxCredits.Loan w (some pid) v) :
    PeerReleaseReady pid v := by
  obtain ⟨d,p,device,found,positive,same,_⟩ := loan
  intro q resident final
  have cell := congrFun (congrArg Prod.snd same) pid
  have count := congrArg (Option.map (fun fields => fields.2.1)) cell
  simp only [Queues.RxCredits.peerView,Option.map_map,Function.comp_def] at count
  change (peerAt v pid).map (·.refcount) = _ at count
  rw [resident] at count
  simp [Queues.RxCredits.creditWorld,final] at count
  omega

theorem HolderAccount.admitted_rx (account : HolderAccount temporary w)
    (bounded : Packets.Inv w) (msg : List UInt8) (src : SkbSource) (ds : Nat)
    (a b : Ambient)
    (run : ((RxOrigin.admitSource msg src ds).run w).run a = .ok ((some ctx,v),b)) :
    ∃ allocation : Credits.Allocation, allocation.slot = ctx.packet.keypair ∧
      HolderAccount (allocation :: temporary) v ∧ RxDetached ctx.slot v ∧
      (v.dev.bind fun d => d.rxSkbs[ctx.slot]?) = some ctx.packet ∧
      PeerReleaseReady ctx.packet.peer v ∧ ∃ p, peerAt v ctx.packet.peer = some p := by
  obtain ⟨entry,u,c,t,e,s,f,p,z,g,y,h,lookupRun,keyRun,noKeyRun,peerRun,deadRun,_,allocateRun⟩ :=
    RxOrigin.admission_execution msg src ds ctx w v a b run
  have hu := (hoare_iff_run_ambient _ _ _).mp (indexLookup_holders [.keypair] (u32le msg 4) temporary)
    w a entry u c account lookupRun
  obtain ⟨allocation,key,ht⟩ := hu.receive_key entry c e keyRun
  have front := Queues.RxCredits.lookup_front a c e lookupRun keyRun
  have ready := lookup_loan_ready front.loan
  have boundU := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Queues.RxCredits.indexLookup_packets [.keypair] (u32le msg 4)) w a entry u c lookupRun
  have boundT := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Queues.RxCredits.receiveKey_packets entry) u c _ t e keyRun
  have bt : Packets.Inv t := by simpa [Packets.Inv,boundT,boundU] using bounded
  have sameS : s = t := by cases noKeyRun; rfl
  subst s
  obtain ⟨sameZ,_,d,device,stored⟩ := Queues.getPeer_normal ctx.packet.peer t z p f g peerRun
  subst z
  have sameY : y = t := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .dataPeerDead p.isDead) (fun s => s = t))
    t g false y h rfl deadRun
  subst y
  obtain ⟨hv,detached,packet⟩ := ht.allocate_rx bt ctx.packet h b allocateRun
  have peers := (ProjectedAction.iff_run_ambient _ _ _).mp
    (packet_peer_frame (SkbStore.newRx ctx.packet)) t h ctx.slot v b allocateRun
  refine ⟨allocation,key,hv,detached,packet,ready.peers peers,p,?_⟩
  have same := congrArg (fun cells => cells.bind fun entries => entries[ctx.packet.peer]?) peers
  simpa [peersAt,peerAt,Option.bind_map,Function.comp_def,device,stored] using same

end Leanux.Proofs.WG.RetirementSecurity
