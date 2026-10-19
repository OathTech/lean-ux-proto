import Leanux.Proofs.WG.Config.GetterPeerCommandClaims
import Leanux.Proofs.WG.Index.ConfigurationPeersSource
import Leanux.Proofs.WG.Config.ScalarCommandExpectationEffects
import Leanux.Proofs.WG.Config.ScalarCommandExpectationFrames
import Leanux.Proofs.WG.Config.GetterScalarOtherClaims
import Leanux.Proofs.WG.Config.CreationScalarClaims
import Leanux.Proofs.WG.Config.ScalarCommandSource
import Leanux.Proofs.WG.Config.RequestWgChainClaims
import Leanux.Proofs.WG.Config.KeyStageEntryClaims
import Leanux.Proofs.WG.Config.RequestReceiptEffectBridge

/-! Original command classification and actual receipt-chain composition. Each
selected scalar effect and nonselected frame applies to the same run. Source
inputs are retained in Matches; no observer or operational walker is added. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.GetterScalar.Expectation
open Leanux Leanux.WG Queues Queues.RxCredits Noise
open Leanux.Proofs.Framing Lifetimes Std.Do

theorem command_input (cs : Ledger) (loans : Reservations) (attrs : PeerAttrs) :
    Campaign2.Ensures (setPeerCmd attrs) (Input cs loans) (fun _=>Input cs loans) := by
  intro g a result final b pre run
  have output:=(hoare_iff_run_ambient _ _ _).mp
    (Index.ConfigurationIndex.command_entry cs loans attrs) g a result final b
    ((Index.configurationInput_snapshot cs loans g a).mp pre.1) run
  have same:=setPeerCmd_getterMetadata attrs (getterMetadataObservation (Campaign2.snapshot g a))
    g a result final b rfl run
  obtain ⟨d,device⟩:=pre.2
  refine ⟨(Index.configurationInput_snapshot cs loans final b).mpr output,?_⟩
  have presence : final.dev.isSome=g.dev.isSome := by
    simpa only [getterMetadataObservation,Option.isSome_map,Campaign2.snapshot,Campaign2.core] using congrArg Option.isSome same
  change g.dev=some d at device
  cases out:final.dev with
  | none=>
    simp only [out,Option.isSome_none,device,Option.isSome_some] at presence
    cases presence
  | some d=>exact ⟨d,out⟩


theorem command_step (cs : Ledger) (loans : Reservations) (attrs : PeerAttrs)
    (initial : Campaign2.Snapshot) :
    Campaign2.Ensures (setPeerCmd attrs)
      (fun s=>Input cs loans s ∧ s.wg=initial.wg)
      (fun ret final=>∃action,Matches attrs ret initial action ∧
        Step action (observation initial) (observation final)) := by
  intro g a ret final b pre run
  obtain ⟨d,present⟩:=pre.1.2
  have initialDevice : initial.wg.device=some d := by
    rw [←pre.2]
    exact present
  have beforeDevice : g.dev=some d:=present
  have classified:=Other.original_command cs loans attrs d g a ret final b
    ⟨pre.1.1,present⟩ run
  cases classified with
  | quiet kept=>
    exact ⟨.quiet,True.intro,by simpa only [Step,Agrees,observation,initialDevice] using kept⟩
  | existing key pid p pubkey valid protocol keep found resident others=>
    have selected:=ScalarCommand.existing_command_index cs loans attrs key pid d
      pubkey valid protocol keep found g a ret final b
      ⟨(Index.configurationInput_snapshot cs loans g a).mp pre.1.1,beforeDevice⟩ run
    obtain ⟨_,q,stored,full⟩:=selected
    have same:q=p:=Option.some.inj (stored.symm.trans resident)
    subst q
    have normalized:=congrArg (Option.map fromFull) full
    change (PeerScalarRetention.observation (Campaign2.snapshot final b) pid).map fromFull=
      some (fromFull (ScalarTail.tailCell attrs ret
        (ScalarTail.prefixCell p attrs.presharedKey attrs.endpoint))) at normalized
    rw [←observation_fromFull,←sourceResult_exact] at normalized
    refine ⟨.update pid p attrs ret,⟨rfl,rfl,d,key,initialDevice,pubkey,found,resident⟩,?_,normalized,?_⟩
    · simp only [observation,values,initialDevice,Option.bind_some,resident,Option.map_some]
    · simpa only [Other.ExceptAt,observation,initialDevice] using others
  | missing key pubkey valid protocol keep absent others=>
    have effect:=CreationScalar.original_missing_command cs loans attrs key initial.wg d
      initialDevice pubkey valid protocol keep absent g a ret final b ⟨pre.1.1,pre.2⟩ run
    rcases effect.2 with ⟨same,_⟩ | ⟨pid,chosen,full⟩
    · refine ⟨.quiet,True.intro,?_⟩
      change Agrees (observation initial) (observation (Campaign2.snapshot final b))
      simpa only [observation,same] using Agrees.refl (observation initial)
    · have slot:pid=d.nextPeer:=by
        simpa only [initialDevice,Option.map_some,Option.some.injEq] using chosen.symm
      subst pid
      have normalized:=congrArg (Option.map fromFull) full
      rw [←observation_fromFull,Option.map_some,←sourceResult_exact] at normalized
      have birth:sourceResult (CreationScalar.initializedPeer key
          (initial.wg.peerCounter+1) attrs.presharedKey) attrs ret=
          birthResult (initial.wg.peerCounter+1) attrs ret :=
        sourceResult_of_fullCell _ _ attrs ret rfl
      rw [birth] at normalized
      refine ⟨.birth d.nextPeer (initial.wg.peerCounter+1) attrs ret,
        ⟨rfl,rfl,rfl,d,key,initialDevice,pubkey,absent,rfl⟩,normalized,?_⟩
      simpa only [Other.ExceptAt,observation,initialDevice] using others

end Leanux.Proofs.WG.Config.GetterScalar.Expectation

namespace Leanux.Proofs.WG.Config.GetterScalar.Expectation
open Leanux Leanux.WG Queues Queues.RxCredits Noise
open RequestOrder

theorem chain_steps (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    {start finish : Campaign2.State} {rs : List Receipt}
    (chain : WgLinks.Chain start rs finish)
    (valid : ∀r∈rs,Valid attrs r)
    (commands : ∀r∈rs,∃p,r.kind=.peer p)
    (prior : Campaign2.Snapshot) (pre : Input cs loans prior)
    (same : prior.wg=start) :
    ∃actions,ReceiptSteps rs actions := by
  induction chain generalizing prior with
  | nil state=>exact ⟨[],ReceiptSteps.nil⟩
  | @cons state final head rest before tail ih=>
    have input:=input_at_receipt cs loans attrs prior head
      (valid head (by simp)) pre (before.trans same.symm)
    obtain ⟨p,kind⟩:=commands head (by simp)
    obtain ⟨action,matched,step⟩:=Valid.ensures (valid head (by simp)) kind
      (command_step cs loans p head.before) ⟨input,rfl⟩
    have output:=Valid.ensures (valid head (by simp)) kind
      (command_input cs loans p) input
    obtain ⟨actions,linked⟩:=ih (fun r member=>valid r (List.mem_cons_of_mem head member))
      (fun r member=>commands r (List.mem_cons_of_mem head member))
      head.after output rfl
    exact ⟨action::actions,ReceiptSteps.cons ⟨p,kind,matched,step⟩ linked⟩

theorem certificate_steps (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (result : Inspection)
    (certificate : Certificate attrs initial result)
    (pre : OwnerConfiguration.ProjectedEntry cs loans initial)
    (key : Receipt) (member : key∈result.receipts) (kind : key.kind=.keyStage) :
    ∃actions,ReceiptSteps (peerReceipts result.receipts) actions := by
  have keyEffect:=KeyStage.certificate_initial_effects cs loans attrs initial result certificate pre
    key member kind
  have ready:=keyEffect.2.2.1
  obtain ⟨d,device,_⟩:=ready.2
  obtain ⟨finish,chain⟩:=WgLinks.certificate_peer_chain attrs initial result certificate key member kind
  apply chain_steps cs loans attrs chain
    (fun r hr=>certificate.1.2.1 r (List.mem_filter.mp hr).1) ?_
    key.after ⟨ready.1,d,device⟩ rfl
  intro r selected
  have filtered:=(List.mem_filter.mp selected).2
  cases rkind:r.kind <;> simp only [rkind] at filtered
  all_goals first | contradiction | exact ⟨_,rfl⟩

end Leanux.Proofs.WG.Config.GetterScalar.Expectation
