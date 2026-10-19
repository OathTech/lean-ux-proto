import Leanux.Proofs.WG.Config.ScalarFinishFrames
import Leanux.Proofs.WG.Index.ConfigurationTailSource
import Leanux.Proofs.WG.Queues.BaseCoherenceConfiguration

/-! Original finish-source effect. Funding and base membership come from the same normal call, and recover the selected peer after the actual final payment. -/

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.ScalarFinish
open Leanux Leanux.WG Noise Std.Do
open Queues Queues.RxCredits Leanux.Proofs.Framing Lifetimes
open PeerScalarRetention

theorem setup_selected (pid : PeerId) (interval : Nat) (running : Bool) (expected : Cell) :
    Hoare (HolderConfigTail.setup pid interval running)
      (fun g=>Selected pid expected (view g))
      (fun _ g=>Selected pid (intervalCell expected interval) (view g)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  unfold HolderConfigTail.setup at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,read,ar,getter,run⟩ := run
  obtain ⟨same,time,d,hd,hp⟩ := getPeer_normal pid w read p a ar getter
  subst read
  subst ar
  have initial : cell p=expected := pre (cell p) (by
    simp only [view,peerValues,hd,Option.bind_some,hp,Option.map_some])
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨send,guarded,ag,guard,run⟩ := run
  have ambient : Preserves (· = w) (WG.andM
      (branch .peerKeepaliveWasZero (p.persistentKeepaliveInterval == 0))
      (WG.andM (branch .peerKeepaliveNonzero (interval != 0))
        (branch .peerKeepaliveRunning running))) := by
    unfold WG.andM
    simp only [branch]
    repeat' first
      | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
      | rx_retention_step
  have same := (hoare_iff_run_ambient _ _ _).mp ambient w a send guarded ag rfl guard
  subst guarded
  simp [setPeer,modifyDev,hd] at run
  rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
  intro c present
  simp only [view,peerValues,Option.bind_some,Std.TreeMap.getElem?_insert_self,Option.map_some] at present
  cases present
  exact congrArg (fun c=>intervalCell c interval) initial

theorem out_selected (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (ret : Int) (expected : Cell) :
    Hoare (do peerPut peer; _ ← branch .peerZeroPsk attrs.presharedKey.isSome
              pure ret : WG.M Int)
      (fun g=>Selected pid expected (view g))
      (fun result g=>result=ret ∧ Selected pid expected (view g)) := by
  apply hoare_bind _ _ (put_selected peer pid expected)
  intro _
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .peerZeroPsk attrs.presharedKey.isSome) _)
  intro _
  exact hoare_pure ret _

theorem finish_selected (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (ret : Int) (expected : Cell) :
    Hoare (Configuration.peerTailFinishSource attrs peer pid ret)
      (fun g=>Selected pid expected (view g))
      (fun result g=>result=ret ∧ Selected pid (finishCell attrs expected) (view g)) := by
  rw [HolderConfigTail.finish_factor]
  apply hoare_bind _ _ (read_selected pid expected)
  intro d
  apply hoare_bind _ _ (branch_state_spec (fun g=>Selected pid expected (view g))
    .peerHasKeepalive attrs.keepalive.isSome)
  intro keep
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  obtain ⟨rfl,pre⟩ := pre
  have tail (value : Cell) : Hoare (do
      if ← branch .peerRunning d.running then sendStagedPackets pid
      peerPut peer
      _ ← branch .peerZeroPsk attrs.presharedKey.isSome
      pure ret : WG.M Int)
      (fun g=>Selected pid value (view g))
      (fun result g=>result=ret ∧ Selected pid value (view g)) := by
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .peerRunning d.running) _)
    intro running
    cases running with
    | false => exact out_selected attrs peer pid ret value
    | true =>
      exact hoare_bind _ _ (staged_selected pid value)
        (fun _=>out_selected attrs peer pid ret value)
  cases hk : attrs.keepalive with
  | none =>
    have done := (hoare_iff_run_ambient _ _ _).mp (tail expected) w a result v b pre
      (by simpa only [hk,Option.isSome_none,Bool.false_eq_true,ite_false,pure_bind] using run)
    simpa only [finishCell,hk,Option.getD_none,intervalCell] using done
  | some interval =>
    have prepared : Hoare (do
        if ← branch .peerSendKeepalive (←HolderConfigTail.setup pid interval d.running) then
          sendKeepalive pid
        if ← branch .peerRunning d.running then sendStagedPackets pid
        peerPut peer
        _ ← branch .peerZeroPsk attrs.presharedKey.isSome
        pure ret : WG.M Int)
        (fun g=>Selected pid expected (view g))
        (fun result g=>result=ret ∧ Selected pid (intervalCell expected interval) (view g)) := by
      apply hoare_bind _ _ (setup_selected pid interval d.running expected)
      intro send
      apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .peerSendKeepalive send) _)
      intro keepNow
      cases keepNow with
      | false => exact tail (intervalCell expected interval)
      | true =>
        exact hoare_bind _ _ (keepalive_selected pid (intervalCell expected interval))
          (fun _=>tail (intervalCell expected interval))
    have done := (hoare_iff_run_ambient _ _ _).mp prepared w a result v b pre
      (by simpa only [hk,Option.isSome_some,ite_true,Option.getD_some] using run)
    simpa only [finishCell,hk,Option.getD_some] using done

theorem base_resident (cs : Ledger) (loans : Reservations) (pid : PeerId)
    (g : WGWorld) (entry : Index.ConfigurationIndex.Entry cs loans g)
    (member : pid∈BaseCoherence.slots g) :
    ∃ d p,g.dev=some d ∧ d.peers[pid]?=some p := by
  obtain ⟨holders,funded,_⟩ := entry.1.1
  have mapped : pid∈holders.base.map Owner.slot := by
    rw [funded.aligned.base]
    exact member
  obtain ⟨owner,inside,slot⟩ := List.mem_map.mp mapped
  have held : owner∈holders.owners := by
    simp only [DurableHolders.owners,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl inside))))
  obtain ⟨p,resident⟩ := funded.resident held
  obtain ⟨d,device,_,stored,_⟩ := resident_fields resident
  exact ⟨d,p,device,by simpa only [slot] using stored⟩

theorem finish_exact (cs : Ledger) (loans : Reservations) (paid : Owner)
    (attrs : PeerAttrs) (ret : Int) (expected : Cell) :
    Noise.Ensures (Configuration.peerTailFinishSource attrs (some paid.slot) paid.slot ret)
      (fun g=>Index.ConfigurationIndex.Entry cs (paid::loans) g ∧
        paid.slot∈BaseCoherence.slots g ∧ view g paid.slot=some expected)
      (fun result g=>result=ret ∧ Index.ConfigurationIndex.Entry cs loans g ∧
        view g paid.slot=some (finishCell attrs expected)) := by
  intro g a result final b pre run
  have account := (hoare_iff_run_ambient _ _ _).mp
    (Index.ConfigurationIndex.finish_entry cs loans paid attrs ret) g a result final b pre.1 run
  have same := congrArg Prod.fst ((ProjectedAction.iff_run_ambient _ _ _).mp
    (BaseCoherence.tailFinish_view attrs (some paid.slot) paid.slot ret) g a result final b run)
  change BaseCoherence.slots final=BaseCoherence.slots g at same
  have member : paid.slot∈BaseCoherence.slots final := by rw [same]; exact pre.2.1
  obtain ⟨d,p,device,resident⟩ := base_resident cs loans paid.slot final account member
  have found : view final paid.slot=some (cell p) := by
    simp only [view,peerValues,device,Option.bind_some,resident,Option.map_some]
  have scalar := (hoare_iff_run_ambient _ _ _).mp
    (finish_selected attrs (some paid.slot) paid.slot ret expected) g a result final b
    (selected_initial paid.slot expected (view g) pre.2.2) run
  exact ⟨scalar.1,account,by rw [found,scalar.2 (cell p) found]⟩

end Leanux.Proofs.WG.Config.ScalarFinish
