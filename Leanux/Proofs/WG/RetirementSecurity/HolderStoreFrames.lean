import Leanux.Proofs.WG.RetirementSecurity.TxHolderTransfer
import Leanux.Proofs.WG.RetirementSecurity.HolderPayments

/-! Frames for the concrete holder account. Packet contents and publication
states are absent from this projection; their key word is the only field
needed to recover a batch's reference. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

def packetKeyWords (w : WGWorld) :=
  ((fun id : SkbId => (w.dev.bind fun d => d.txSkbs[id]?).map (·.keypair)),
   (fun id : SkbId => (w.dev.bind fun d => d.rxSkbs[id]?).map (·.keypair)))

def holderStore (w : WGWorld) := (Origins.view w,peersAt w,packetKeyWords w)

theorem holderStore_kernel (action : WG.M α) (same : SameWGStore action) :
    SameView holderStore action :=
  same.of_factor (fun store : WGStoreView =>
    (store.dev.map (fun d => (d.ifindex,fun id => d.keypairs[id]?)),
     store.dev.map (·.peers),
     (fun id => (store.dev.bind fun d => d.txSkbs[id]?).map (·.keypair)),
     (fun id => (store.dev.bind fun d => d.rxSkbs[id]?).map (·.keypair))))
    holderStore (fun _ => rfl)

theorem loan_store (same : holderStore v = holderStore w) :
    (∀ holder key, nameLoan v holder key = nameLoan w holder key) ∧
    (∀ pid item, transmitLoan v pid item = transmitLoan w pid item) ∧
    (∀ pid id, receiveLoan v pid id = receiveLoan w pid id) := by
  have keys (id : KeypairId) : keyAt v id = keyAt w id := by
    have h := congrArg (fun shape => shape.1.bind fun fields => fields.2 id) same
    simpa only [holderStore,Origins.view,keyAt,Option.bind_map,Function.comp_def] using h
  have names (holder : KeyHolder) (key : KeypairId) :
      nameLoan v holder key = nameLoan w holder key := by simp only [nameLoan,keys]
  refine ⟨names,?_,?_⟩
  · intro pid item
    have tx := congrArg (fun shape => shape.2.2.1) same
    cases head : item.head? with
    | none => simp [transmitLoan,head]
    | some id =>
      have point := congrFun tx id
      simp only [holderStore,packetKeyWords] at point
      cases hv : v.dev.bind (fun d => d.txSkbs[id]?) <;>
        cases hw : w.dev.bind (fun d => d.txSkbs[id]?) <;>
        simp only [hv,hw,Option.map_none,Option.map_some,Option.some.injEq,reduceCtorEq] at point
      all_goals simp [transmitLoan,head,hv,hw,names,point]
  · intro pid id
    have point := congrFun (congrArg (fun shape => shape.2.2.2) same) id
    simp only [holderStore,packetKeyWords] at point
    cases hv : v.dev.bind (fun d => d.rxSkbs[id]?) <;>
      cases hw : w.dev.bind (fun d => d.rxSkbs[id]?) <;>
      simp only [hv,hw,Option.map_none,Option.map_some,Option.some.injEq,reduceCtorEq] at point
    all_goals simp [receiveLoan,hv,hw,names,point]

theorem HolderAccount.store (account : HolderAccount temporary w)
    (same : holderStore v = holderStore w) : HolderAccount temporary v := by
  obtain ⟨loans,projected,credits⟩ := account
  have peers : peersAt v = peersAt w := congrArg (fun shape => shape.2.1) same
  obtain ⟨names,tx,rx⟩ := loan_store same
  have peerNames (pid : PeerId) (p : Peer) : peerLoans v pid p = peerLoans w pid p := by
    have hn : nameLoan v = nameLoan w := funext fun holder => funext (names holder)
    have ht : transmitLoan v = transmitLoan w := funext fun peer => funext (tx peer)
    have hr : receiveLoan v = receiveLoan w := funext fun peer => funext (rx peer)
    simp only [peerLoans_eq,hn,ht,hr]
  refine ⟨loans,?_,credits.view (congrArg (fun shape => shape.1) same)⟩
  cases dw : w.dev <;> cases dv : v.dev
  all_goals simp only [peersAt,dw,dv,Option.map_none,Option.map_some,Option.some.injEq] at peers
  all_goals try contradiction
  · simpa [durableLoans,dw,dv] using projected
  · simpa only [durableLoans,dw,dv,peers,peerNames] using projected

theorem holderStore_preserves (action : WG.M α) (same : SameView holderStore action)
    (temporary : Credits.Ledger) : Preserves (HolderAccount temporary) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b account run
  exact account.store ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run)

theorem modifyDev_holderStore (f : Device → Device)
    (key : ∀ d, (f d).keypairs = d.keypairs)
    (iface : ∀ d, (f d).ifindex = d.ifindex)
    (peers : ∀ d, (f d).peers = d.peers)
    (tx : ∀ d, (f d).txSkbs = d.txSkbs)
    (rx : ∀ d, (f d).rxSkbs = d.rxSkbs) : SameView holderStore (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases run
  cases device : w.dev <;>
    simp [holderStore,Origins.view,peersAt,packetKeyWords,device,key,iface,peers,tx,rx]

theorem setTx_holderStore (id : SkbId) (f : DataPacket → DataPacket)
    (key : ∀ p, (f p).keypair = p.keypair) : SameView holderStore (setTxSkb id f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases result
  cases device : w.dev with
  | none => simp [setTxSkb,liftSkb_run,device] at run
  | some d =>
    cases packet : d.txSkbs[id]? with
    | none =>
      simp [setTxSkb,liftSkb_run,SkbStore.setTx,SkbStore.getTx,device,packet,
        invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      rw [Packets.setTxSkb_run w a d id p f device packet] at run
      cases run
      apply Prod.ext
      · simp [holderStore,Origins.view,Packets.update,device]
      · apply Prod.ext
        · simp [holderStore,peersAt,Packets.update,device]
        · apply Prod.ext
          · funext other
            by_cases eq : id = other
            · subst other
              simp [holderStore,packetKeyWords,Packets.update,device,packet,key]
            · simp [holderStore,packetKeyWords,Packets.update,device,
                Std.TreeMap.getElem?_insert,eq]
          · simp [holderStore,packetKeyWords,Packets.update,device]

end Leanux.Proofs.WG.RetirementSecurity
