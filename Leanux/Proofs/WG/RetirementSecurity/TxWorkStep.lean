import Leanux.Proofs.WG.RetirementSecurity.TxWorkAdmission
import Leanux.Proofs.WG.RetirementSecurity.TxDispositionCoverage

/-! A normal TX worker end cannot strand a ready queue head: its actual
false step sees an empty queue or an uncrypted head. Terminal tails behind an
uncrypted head are permitted and will share that head's later publication. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem ready_false (a b : Ambient)
    (run : ((txReadySource first).run w).run a=.ok ((false,v),b)) :
    v=w ∧ (first=none ∨ ∃items id packet,first=some items ∧ items.head?=some id ∧
      TxDisposition.txPackets w id=some packet ∧ packet.state=.uncrypted) := by
  cases first with
  | none=>
    simp [txReadySource,WG.andM,branch,AmbientM.branch] at run
    obtain ⟨rfl,_⟩:=run
    exact ⟨rfl,Or.inl rfl⟩
  | some items=>
    cases head:items.head? with
    | none=>
      simp [txReadySource,WG.andM,branch,AmbientM.branch,head,invariant,AmbientM.invariant] at run
      cases run
    | some id=>
      unfold txReadySource WG.andM at run
      rw [MaterialOrigin.bind_ok_ambient] at run
      obtain ⟨present,t,e,presentRun,run⟩:=run
      cases presentRun
      simp only [Option.isSome_some,ite_true,head] at run
      rw [MaterialOrigin.bind_ok_ambient] at run
      obtain ⟨packet,u,c,read,test⟩:=run
      obtain ⟨same,clock,d,device,stored⟩:=Packets.getTxSkb_current id w u packet _ c read
      subst u
      subst c
      have checked : (packet.state != .uncrypted)=false ∧ w=v ∧
          CounterWindow.record (CounterWindow.record a .txPacket true) .txNotUncrypted
            (packet.state != .uncrypted)=b := by
        simpa [branch,AmbientM.branch,CounterWindow.record,and_assoc] using test
      refine ⟨checked.2.1.symm,Or.inr ⟨items,id,packet,rfl,head,?_,?_⟩⟩
      · simp [TxDisposition.txPackets,device,stored]
      · have bad:=checked.1
        cases mark:packet.state with
        | uncrypted=>rfl
        | crypted=>rw [mark] at bad; cases bad
        | dead=>rw [mark] at bad; cases bad

theorem body_false (pid : PeerId) (a b : Ambient)
    (run : ((TxDisposition.bodySource pid first).run w).run a=.ok ((false,v),b)) :
    v=w ∧ (first=none ∨ ∃items id packet,first=some items ∧ items.head?=some id ∧
      TxDisposition.txPackets w id=some packet ∧ packet.state=.uncrypted) := by
  rw [tx_body_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ready,u,c,test,tail⟩:=run
  cases ready with
  | false=>
    simp only [Bool.not_false,ite_true] at tail
    cases tail
    exact ready_false a b test
  | true=>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false] at tail
    have impossible: false=true := (hoare_iff_run_ambient _ _ _).mp
      (ready_tail_true pid first) u c false v b True.intro tail
    cases impossible

theorem peek_selected (pid : PeerId) (a b : Ambient)
    (run : ((txPeekSource pid).run w).run a=.ok ((first,v),b)) :
    ∃p,peerAt w pid=some p ∧ first=p.txQueue.all.head? := by
  simp only [txPeekSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,readRun,pair,t,e,peekRun,_,_,_,_,_,_,_,_,finish⟩:=run
  obtain ⟨world,clock,d,device,stored⟩:=Origins.getPeer_return pid w u p a c readRun
  subst u
  subst c
  obtain ⟨selected,queue⟩:=pair
  have head: selected=p.txQueue.all.head? := (prev_peek_normal p.txQueue w t a e selected queue peekRun).1
  cases finish
  exact ⟨p,by simp [peerAt,device,stored],head⟩

theorem ended_head (pid : PeerId) (a b : Ambient)
    (run : ((txStep pid).run w).run a=.ok ((false,v),b)) :
    txQueueContents v pid=[] ∨ ∃items id packet,
      (txQueueContents v pid).head?=some items ∧ items.head?=some id ∧
      TxDisposition.txPackets v id=some packet ∧ packet.state=.uncrypted := by
  rw [txStep_peek_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨first,u,c,peek,body⟩:=run
  obtain ⟨p,found,selected⟩:=peek_selected pid a c peek
  obtain ⟨d,q,queue,device,stored,contents,cached,after⟩:=txPeek_effect pid a c peek
  have same:q=p := by
    have atStart:peerAt w pid=some q := by simp [peerAt,device,stored]
    exact Option.some.inj (atStart.symm.trans found)
  subst q
  obtain ⟨same,empty|⟨items,id,packet,chosen,head,resident,uncrypted⟩⟩:=body_false pid c b body
  · subst v
    left
    have nil:p.txQueue.all=[] := List.head?_eq_none_iff.mp (selected.symm.trans empty)
    simp [txQueueContents,Queues.RxCredits.handoffTxView,after,replacePeer,contents,nil]
  · subst v
    right
    refine ⟨items,id,packet,?_,head,resident,uncrypted⟩
    simpa [txQueueContents,Queues.RxCredits.handoffTxView,after,replacePeer,contents] using
      selected.symm.trans chosen

end Leanux.Proofs.WG.RetirementSecurity.TxWork
