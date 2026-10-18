import Leanux.Proofs.WG.Index.TxSelectionFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.CryptCore
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem tx_body_cut (pid : PeerId) (selected : Option (List SkbId))
    (w v : WGWorld) (a b : Ambient) (result : Bool)
    (run : ((TxDisposition.bodySource pid selected).run w).run a=.ok ((result,v),b)) :
    (result=false ∧ v=w) ∨
    ∃ (first : SkbId) (rest : List SkbId) (d : Device) (p : Peer) (head : DataPacket) (start middle : Ambient) (completed : WGWorld),
      selected=some (first::rest) ∧ w.dev=some d ∧ d.peers[pid]?=some p ∧
      (w.dev.bind fun dev=>dev.txSkbs[first]?)=some head ∧
      ((if head.state == PacketState.crypted then createDataDone pid (first::rest) else pure ()).run
        {w with dev:=some {d with peers:=d.peers.insert pid {p with txQueue:=p.txQueue.dropPeeked}}}).run start
          =.ok (((),completed),middle) ∧
      ((TxDisposition.disposeSource pid (first::rest) head.keypair).run completed).run middle
          =.ok ((result,v),b) := by
  cases selected with
  | none =>
    change Except.ok ((false,w),CounterWindow.record a .txPacket false)=.ok ((result,v),b) at run
    cases run
    exact Or.inl ⟨rfl,rfl⟩
  | some item =>
    cases item with
    | nil =>
      change Except.error (Stop.invariant "an empty ring item")=.ok ((result,v),b) at run
      cases run
    | cons first rest =>
      unfold TxDisposition.bodySource at run
      rw [MaterialOrigin.bind_ok_ambient] at run
      obtain ⟨go,checked,ac,hgo,tail⟩ := run
      change (((do let packet←getTxSkb first
                   branch .txNotUncrypted (packet.state != .uncrypted) : WG.M Bool).run w).run
        (CounterWindow.record a .txPacket true))=.ok ((go,checked),ac) at hgo
      rw [MaterialOrigin.bind_ok_ambient] at hgo
      obtain ⟨pkt,read,ar,hread,hbranch⟩ := hgo
      obtain ⟨readEq,_,_,_,_⟩ := Packets.getTxSkb_current first w read pkt _ ar hread
      subst read
      cases hbranch
      cases active : (pkt.state != .uncrypted) with
      | false =>
        simp only [active,Bool.not_false,ite_true] at tail
        cases tail
        exact Or.inl ⟨rfl,rfl⟩
      | true =>
        simp only [active,Bool.not_true,Bool.false_eq_true,ite_false,List.head?_cons,bind_assoc] at tail
        rw [MaterialOrigin.bind_ok_ambient] at tail
        obtain ⟨head,read,ar,hread,tail⟩ := tail
        obtain ⟨readEq,_,d₀,device₀,packet⟩ := Packets.getTxSkb_current first w read head _ ar hread
        subst read
        rw [MaterialOrigin.bind_ok_ambient] at tail
        obtain ⟨p,read,ap,hpeer,tail⟩ := tail
        obtain ⟨readEq,timeEq,d,device,resident⟩ := getPeer_normal pid w read p ar ap hpeer
        subst read
        subst ap
        rw [MaterialOrigin.bind_ok_ambient] at tail
        obtain ⟨p₂,read,ap,hpeer₂,tail⟩ := tail
        obtain ⟨readEq,timeEq,d₂,device₂,resident₂⟩ := getPeer_normal pid w read p₂ ar ap hpeer₂
        subst read
        subst ap
        have dEq : d₂=d := Option.some.inj (device₂.symm.trans device)
        subst d₂
        have pEq : p₂=p := Option.some.inj (resident₂.symm.trans resident)
        subst p₂
        rw [MaterialOrigin.bind_ok_ambient] at tail
        obtain ⟨ignored,dropped,ad,written,tail⟩ := tail
        cases ignored
        have dropEq : dropped={w with dev:=w.dev.map fun d=>{d with peers:=d.peers.insert pid {p with txQueue:=p.txQueue.dropPeeked}}} ∧ ad=ar := by
          simpa [setPeer,modifyDev] using written.symm
        rcases dropEq with ⟨rfl,rfl⟩

        rw [MaterialOrigin.bind_ok_ambient] at tail
        obtain ⟨condition,conditioned,ac,conditionRun,tail⟩ := tail
        cases conditionRun
        cases choice : (head.state == PacketState.crypted) with
        | false =>
          simp only [choice,Bool.false_eq_true,ite_false] at tail
          refine Or.inr ⟨first,rest,d,p,head,
            CounterWindow.record ad .txCrypted false,CounterWindow.record ad .txCrypted false,
            {w with dev:=some {d with peers:=d.peers.insert pid {p with txQueue:=p.txQueue.dropPeeked}}},
            rfl,device,resident,?_,?_,?_⟩
          · simpa [device₀] using packet
          · simp only [choice,Bool.false_eq_true,ite_false]
            rfl
          · simpa only [CounterWindow.record,device,Option.map_some] using tail
        | true =>
          simp only [choice,ite_true] at tail
          rw [MaterialOrigin.bind_ok_ambient] at tail
          obtain ⟨ignored,completed,middle,completion,dispose⟩ := tail
          cases ignored
          refine Or.inr ⟨first,rest,d,p,head,CounterWindow.record ad .txCrypted true,middle,completed,rfl,device,resident,?_,?_,dispose⟩
          · simpa [device₀] using packet
          · simpa only [CounterWindow.record,choice,ite_true,device,Option.map_some] using completion

theorem tx_step_cut (pid : PeerId) (w v : WGWorld) (a b : Ambient) (result : Bool)
    (run : ((txStep pid).run w).run a=.ok ((result,v),b)) :
    (result=false ∧ ConfigurationIndex.fields v=ConfigurationIndex.fields w) ∨
    ∃ (first : SkbId) (rest : List SkbId) (d : Device) (p : Peer)
      (q : PrevQueue (List SkbId)) (head : DataPacket) (start middle : Ambient) (completed : WGWorld),
      w.dev=some d ∧ d.peers[pid]?=some p ∧
      q.all=p.txQueue.all ∧ p.txQueue.all=(first::rest)::q.dropPeeked.all ∧
      ((if head.state == PacketState.crypted then createDataDone pid (first::rest) else pure ()).run
        {w with dev:=some {d with peers:=(d.peers.insert pid {p with txQueue:=q}).insert pid {p with txQueue:=q.dropPeeked}}}).run start
          =.ok (((),completed),middle) ∧
      ((TxDisposition.disposeSource pid (first::rest) head.keypair).run completed).run middle
          =.ok ((result,v),b) := by
  rw [←TxDisposition.stepSource_eq] at run
  unfold TxDisposition.stepSource at run
  simp only [bind_assoc] at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,read,ar,hread,tail⟩ := run
  obtain ⟨readEq,timeEq,d,device,resident⟩ := getPeer_normal pid w read p a ar hread
  subst read
  subst ar
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨⟨selected,q⟩,peeked,ap,hpeek,tail⟩ := tail
  obtain ⟨selectedEq,allEq,_,peekedEq⟩ := prev_peek_normal p.txQueue w peeked a ap selected q hpeek
  subst peeked
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨current,read,ar,hread,tail⟩ := tail
  obtain ⟨readEq,timeEq,d₂,device₂,resident₂⟩ := getPeer_normal pid w read current ap ar hread
  subst read
  subst ar
  have dEq : d₂=d := Option.some.inj (device₂.symm.trans device)
  subst d₂
  have pEq : current=p := Option.some.inj (resident₂.symm.trans resident)
  subst current
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨ignored,installed,ai,written,tail⟩ := tail
  cases ignored
  have installedEq : installed={w with dev:=some {d with peers:=d.peers.insert pid {p with txQueue:=q}}} := by
    cases written
    simp [device]
  rcases tx_body_cut pid selected installed v ai b result tail with idle | active
  · refine Or.inl ⟨idle.1,?_⟩
    rw [idle.2,installedEq]
    simpa [ConfigurationIndex.fields,device] using congrArg some
      (ConfigurationIndex.deviceFields_peerWrite d pid p {p with txQueue:=q} resident rfl)
  · obtain ⟨first,rest,di,pi,head,start,middle,completed,chosen,devicei,residenti,_,completion,dispose⟩ := active
    have diEq : di={d with peers:=d.peers.insert pid {p with txQueue:=q}} := by
      simp only [installedEq,Option.some.injEq] at devicei
      exact devicei.symm
    subst di
    have piEq : pi={p with txQueue:=q} := by
      simpa using residenti.symm
    subst pi
    have dropped := prev_peek_then_drop p.txQueue w w a ap (first::rest) q (chosen ▸ hpeek)
    refine Or.inr ⟨first,rest,d,p,q,head,start,middle,completed,device,resident,allEq,dropped,?_,dispose⟩
    simpa only [installedEq] using completion

end Leanux.Proofs.WG.Index.CryptCore
