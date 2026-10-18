import Leanux.Proofs.WG.Noise.ReceiveStepCoverageFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.ReceiveStepCaller
open Leanux Leanux.WG Leanux.Proofs.WG.Origins
open ReceptionCaller

theorem observeStep_coverage (g : WGWorld) (ambient : Ambient)
    (receipt : StepReceipt) (final : WGWorld) (after : Ambient)
    (run : observeStep g ambient = .ok ((receipt,final),after)) :
    TagCoverage (responseTagMap g.dev) receipt.poll.receipts (responseTagMap final.dev) := by
  cases device : g.dev with
  | none =>
    change (getDev g ambient >>= _) = _ at run
    have read : getDev g ambient =
        .error (.invariant "no WireGuard device in this trace's fixture") := by
      change ((getDev.run g).run ambient) = _
      simp [getDev,device,invariant,AmbientM.invariant]
      rfl
    rw [read] at run
    cases run
  | some d =>
    cases selected : d.handshakeQueue.consume with
    | mk packet ring =>
      cases packet with
      | none =>
        rw [observeStep_empty_run g ambient d ring device selected] at run
        cases run
        simpa only [device, PollResult.receipts, TagCoverage] using
          (TagsRetained.refl (responseTagMap g.dev))
      | some packet =>
        obtain ⟨msg,src⟩ := packet
        rw [observeStep_consumed_run g ambient d msg src ring device selected] at run
        cases received : observeClassified msg src (dequeueWorld g ring) (pollAmbient ambient true) with
        | error stop => simp only [received,Except.map] at run; cases run
        | ok out =>
          obtain ⟨⟨call,current⟩,tail⟩ := out
          have coverage := observeClassified_coverage msg src (dequeueWorld g ring)
            (pollAmbient ambient true) call current tail received
          simp only [received,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
          obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
          change TagCoverage (responseTagMap (some d)) call.receipts
            (responseTagMap (decrementWorld current).dev)
          simpa only [dequeueWorld_tags,decrementWorld_tags,device] using coverage

end Leanux.Proofs.WG.Noise.ReceiveStepCaller
