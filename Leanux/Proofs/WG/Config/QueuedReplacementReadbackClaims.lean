import Leanux.Proofs.WG.Config.QueuedReplacementReadbackModel
import Leanux.Proofs.WG.Config.GetterCleanupClaims
import Leanux.Proofs.WG.Config.ReplacementCompletionClaims
import Leanux.Proofs.WG.Config.EmptyMetadataGetterClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG TimerDiscipline Keypairs

/-- A normal setter successor supplies every state-dependent premise for
empty-peer readback, including the exact retained initial socket and selector. -/
theorem replacement_queued_getter_ready
    (cs : Queues.RxCredits.Ledger) (loans : Queues.RxCredits.Reservations)
    (tables : AllowedIps.FlatTable × AllowedIps.FlatTable) (d : Device) (sock : NlSock) :
    Campaign2.Ensures (wgSetDevice (replacePeersAttrs (byIndex d)))
      (fun s => s.wg.device=some d ∧ ClaimView.selectsDevice s d ∧
        s.wg.nlSock7=sock ∧ ReplaceCompletion.View.Input cs loans tables s)
      (fun ret s => ret=0 ∧ ReplacementReadbackReady (requestGeneration d) sock s) := by
  intro g a ret removed time pre setRun
  obtain ⟨zero,out,device,empty,table,routes⟩ :=
    ReplaceCompletion.request_completion cs loans tables d
      g a ret removed time ⟨pre.1,pre.2.1,pre.2.2.2⟩ setRun
  obtain ⟨_,metadata⟩ := GetterCleanup.request_metadata_projected d sock g.fixtureNetDevices
    g a ret removed time ⟨pre.1,pre.2.1,pre.2.2.1,rfl⟩ setRun
  change removed.dev=some out at device
  change removed.dev.map (fun d=>(sendConfiguration d,removed.nlSock7,removed.fixtureNetDevices))=
    some (sendConfiguration (requestGeneration d),sock,g.fixtureNetDevices) at metadata
  rw [device] at metadata
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq] at metadata
  obtain ⟨same,socket,fixtures⟩ := metadata
  have selected : ClaimView.selectsDevice (Campaign2.snapshot removed time) (requestGeneration d) := by
    change (removed.fixtureNetDevices ++ [(d.ifname,d.ifindex,some "wireguard")]).find? _ =
      some (d.ifname,d.ifindex,some "wireguard")
    rw [fixtures]
    exact pre.2.1
  exact ⟨zero,out,device,empty,same,socket,selected,out,device,empty,table,routes⟩

/-- Every concrete realization of the derived successor observation admits the
actual getter. The capacity and socket-idleness bounds are initial static inputs. -/
theorem replacement_ready_getter_returns (d : Device) (sock : NlSock)
    (room : devicePrefixSpace d + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (queue : sock.queue = []) :
    Campaign2.Returns (wgGetDevice (byIndex d)) (ReplacementReadbackReady d sock)
      (fun value s => value=.ok (emptyPeersJson d) ∧
        ReplaceCompletion.View.Empty s ∧ s.wg.nlSock7=socketReadbackFinal sock d) := by
  intro g a pre
  obtain ⟨out,device,empty,same,socket,selected,remaining⟩ := pre
  obtain ⟨other,present,list,table,routes⟩ := remaining
  have eq : other=out := Option.some.inj (present.symm.trans device)
  subst other
  obtain ⟨value,final,after,run,json,kept,readSocket⟩ :=
    empty_metadata_getter_returns d out sock empty same room idle queue
      g a ⟨device,socket,selected⟩
  refine ⟨value,final,after,run,json,⟨out,kept,empty,table,?_⟩,readSocket⟩
  rw [kept]
  simpa only [device,Option.map_some] using routes

/-- Whole queued flag-only replacement followed by the actual complete getter.
Cleanup derives the empty configured endpoint and retains the header/socket
needed by the getter. The entry gives no empty-work or successor-state premise;
the setter may still stop on its original record and consistency checks. -/
theorem replacement_queued_get_after_set
    (cs : Queues.RxCredits.Ledger) (loans : Queues.RxCredits.Reservations)
    (tables : AllowedIps.FlatTable × AllowedIps.FlatTable) (d : Device) (sock : NlSock)
    (room : devicePrefixSpace (requestGeneration d) + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (queue : sock.queue = []) :
    Campaign2.Ensures (do
      let ret ← wgSetDevice (replacePeersAttrs (byIndex d))
      let value ← wgGetDevice (byIndex d)
      pure (ret,value))
      (fun s => s.wg.device=some d ∧ ClaimView.selectsDevice s d ∧
        s.wg.nlSock7=sock ∧ ReplaceCompletion.View.Input cs loans tables s)
      (fun result s => result=(0,.ok (emptyPeersJson (requestGeneration d))) ∧
        ReplaceCompletion.View.Empty s ∧
        s.wg.nlSock7=socketReadbackFinal sock (requestGeneration d)) := by
  intro g a result final after pre run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ret,removed,time,setRun,tail⟩ := run
  obtain ⟨zero,ready⟩ := replacement_queued_getter_ready cs loans tables d sock
    g a ret removed time pre setRun
  obtain ⟨value,readFinal,readTime,getRun,json,empty,readSocket⟩ :=
    replacement_ready_getter_returns (requestGeneration d) sock room idle queue
      removed time ready
  change ((wgGetDevice (byIndex d)).run removed).run time = _ at getRun
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨actual,current,now,actualGet,pureRun⟩ := tail
  rw [getRun] at actualGet
  cases actualGet
  cases pureRun
  exact ⟨Prod.ext zero json,empty,readSocket⟩

end Leanux.Proofs.WG.Config
