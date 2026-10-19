import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationSendResult

/-! The native completion loop exposes its exact current packet and suffix.
The factors do not add observations or skip the post-send timer suffix. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.CompletionFrontier
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity AuthenticatedEffects

def iteration (o : CompletionEffects.Ops E) (pid : PeerId) (id : SkbId)
    (dataSent : Bool) : PrefixM E Bool := do
  let packet ← captureObserved (o.packet id)
  _ ← o.step (branch .doneSkbIterate true)
  let isKeepalive := packet.value.bytes.length == MESSAGE_DATA_LEN_0
  let sent ← o.send pid id packet
  if ← Queues.TxDisposition.andObs (o.step (branch .doneSendOk sent))
      (o.step (branch .doneNotKeepalive !isKeepalive)) then pure true
  else pure dataSent

def walk (o : CompletionEffects.Ops E) (pid : PeerId) (item : List SkbId)
    (dataSent : Bool) : PrefixM E Bool :=
  forIn item dataSent fun id sent => do
    let next ← iteration o pid id sent
    pure (.yield next)

def before (o : CompletionEffects.Ops E) (pid : PeerId) (item : List SkbId) : PrefixM E Unit := do
  o.completion pid item
  o.traversal pid
  o.sent pid

def after (o : CompletionEffects.Ops E) (pid : PeerId) (dataSent : Bool) : PrefixM E Unit := do
  _ ← o.step (branch .doneSkbIterate false)
  if ← o.step (branch .doneDataSent dataSent) then o.dataSent pid
  o.fresh pid

theorem complete_factor (o : CompletionEffects.Ops E) (pid : PeerId) (item : List SkbId) :
    CompletionEffects.completeWith o pid item =
      (do before o pid item; let sent ← walk o pid item false; after o pid sent) := by
  unfold CompletionEffects.completeWith before walk iteration after
  simp only [bind_assoc,Queues.TxDisposition.bind_ite,pure_bind]

theorem walk_nil (o : CompletionEffects.Ops E) (pid : PeerId) (dataSent : Bool) :
    walk o pid [] dataSent = pure dataSent := rfl

theorem walk_cons (o : CompletionEffects.Ops E) (pid : PeerId) (id : SkbId)
    (item : List SkbId) (dataSent : Bool) :
    walk o pid (id :: item) dataSent =
      (do let next ← iteration o pid id dataSent; walk o pid item next) := by
  simp only [walk,List.forIn_cons,bind_assoc,pure_bind]

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.CompletionFrontier
