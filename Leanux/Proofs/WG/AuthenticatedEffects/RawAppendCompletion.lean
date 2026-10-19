import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendTransport

/-! Full native TX completion projects to the direct append observer. Packet
reads, queue removal, reference repayment and timer helpers retain their native
effects, while each per-packet sender observes the original socket append. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity

def completionOps : CompletionEffects.Ops Event where
  step := fun action => liftPrefix (liftWG action)
  peer := fun pid => liftPrefix (liftWG (getPeer pid))
  modifyPeer := fun pid f => liftPrefix (liftWG (do setPeer pid (f (← getPeer pid))))
  packet := fun skb => liftPrefix (liftWG (getTxSkb skb))
  completion := fun _ _ => pure ()
  send := fun pid _ packet => transport pid packet
  drop := fun pid _ => liftPrefix (liftWG (do
    setPeer pid {(← getPeer pid) with txQueue := (← getPeer pid).txQueue.dropPeeked}))
  dispose := fun pid item key => liftPrefix (liftWG (TxDisposition.disposeSource pid item key))
  traversal := fun pid => liftPrefix (liftWG (timersTraversal pid))
  sent := fun pid => liftPrefix (liftWG (timersAnyAuthenticatedPacketSent pid))
  dataSent := fun pid => liftPrefix (liftWG (timersDataSent pid))
  fresh := fun pid => liftPrefix (liftWG (keepKeyFresh pid))

theorem completion_ops_projects :
    CompletionEffects.Ops.Projects completion? CompletionEffects.native completionOps where
  step := fun _ => projectsPrefix_lift completion? _
  peer := fun _ => access_projects _ _ (getPeerMixed_erases _)
  modifyPeer := fun _ _ => access_projects _ _ (modifyPeerKeysPrefix_erases _ _)
  packet := fun _ => access_projects _ _ (getTxSkbPrefix_erases _)
  completion := fun _ _ => projectsPrefix_emit completion? _
  send := transport_projects
  drop := fun _ _ => projectsPrefix_focus_other _ _ completion? (fun _ => rfl) (TxDisposition.drop_erases _ _)
  dispose := fun _ _ _ => projectsPrefix_focus_other _ _ completion? (fun _ => rfl) (TxDisposition.dispose_erases _ _ _)
  traversal := fun _ => access_projects _ _ (timersTraversalPrefix_erases _)
  sent := fun _ => access_projects _ _ (timersAnyAuthenticatedPacketSentPrefix_erases _)
  dataSent := fun _ => access_projects _ _ (timersDataSentPrefix_erases _)
  fresh := fun _ => access_projects _ _ (keepKeyFreshPrefix_erases _)

def completion (pid : PeerId) : PrefixM Event Bool :=
  CompletionEffects.stepWith completionOps pid

theorem completion_projects (pid : PeerId) :
    ProjectsPrefix completion? id (Completion.step pid) (completion pid) :=
  CompletionEffects.step_projects completion? completion_ops_projects pid

end Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
