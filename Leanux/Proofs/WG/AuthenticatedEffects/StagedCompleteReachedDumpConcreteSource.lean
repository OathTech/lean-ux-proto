import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecycleConcreteRunner
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDumpMetadataCanonical

/-! Fixed dump source witnesses reuse the lifecycle source syntax. Their
ordinary certificate excludes creation, reset and stronger staging entries.
Native header/walk trees keep the landed cancellation behavior; cursor release
uses the counted peer source. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.DumpConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal NetlinkDump Driver NestedPeerRelease
open Lifecycle.Points

abbrev Source (action : WGPrefix Event α) :=
  {shape : Shape (liftWGObserver action) // Ordinary shape}

noncomputable def pureSource (value : α) : Source (pure value) := by
  change {shape : Shape (liftWGObserver (pure value)) // Ordinary shape}
  rw [liftWGObserver_pure]
  exact ⟨.pure value,True.intro⟩

noncomputable def nativeSource (action : WG.M α) (source : PeerMetadata.Shape action) :
    Source (liftWGPrefix action) := by
  change {shape : Shape (liftWGObserver (liftWGPrefix action)) // Ordinary shape}
  rw [liftWGObserver_lift]
  exact ⟨.native (.metadata action source),True.intro⟩

noncomputable def releaseSource (peer : Option PeerId) : Source (hooks.peerRelease peer) :=
  ⟨.child (.family (.release peer)),True.intro⟩

noncomputable def bindSource {body : WGPrefix Event α} {next : α → WGPrefix Event β}
    (head : Source body) (tail : ∀value,Source (next value)) : Source (body >>= next) := by
  change {shape : Shape (liftWGObserver (body >>= next)) // Ordinary shape}
  rw [liftWGObserver_bind]
  exact ⟨.bind head.1 (fun value=>(tail value).1),head.2,fun value=>(tail value).2⟩

noncomputable def conditionalSource (test : Prop) [Decidable test]
    {yes no : WGPrefix Event α} (left : test → Source yes) (right : ¬test → Source no) :
    Source (if test then yes else no) := by
  split
  · exact left ‹_›
  · exact right ‹_›

noncomputable def listSource (items : List ι) (initial : σ)
    (body : ι → σ → WGPrefix Event (ForInStep σ))
    (sources : ∀item acc,Source (body item acc)) : Source (forIn items initial body) := by
  change {shape : Shape (liftWGObserver (forIn items initial body)) // Ordinary shape}
  rw [observer_list]
  exact ⟨listShape items initial _ (fun item acc=>(sources item acc).1),
    list_ordinary (fun item acc=>(sources item acc).2)⟩

elab "dump_source_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Source do Lean.throwError "not a dump source"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  let .const actual _ := action.consumeMData.headBeta.getAppFn | Lean.throwError "not a source head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("."++name) do
    Lean.throwError "different source head"

macro "dump_source_step" : tactic => `(tactic| first
  | (dump_source_head liftWGPrefix; apply nativeSource; repeat' first
      | (metadata_source_head RxCredits.DumpReservation.walkSource; exact PeerMetadata.dumpWalkShape _ _ _)
      | (metadata_source_head deviceDumpHeaderSource; exact PeerMetadata.dumpHeaderShape _ _ _ _)
      | (metadata_source_head getNlSock; exact PeerMetadata.dumpSocketReadShape _)
      | (metadata_source_head setNlSock; exact PeerMetadata.dumpSocketWriteShape _ _)
      | (metadata_source_head lookupInterface; exact PeerMetadata.interfaceShape _)
      | (metadata_source_head coalesce; exact PeerMetadata.dumpCoalesceShape _)
      | (metadata_source_head peerGet; exact PeerMetadata.peerGetShape _)
      | dump_metadata_step)
  | (dump_source_head Hooks.peerRelease; exact releaseSource _)
  | (dump_source_head Pure.pure; exact pureSource _)
  | (dump_source_head Bind.bind; apply bindSource)
  | (dump_source_head ite; apply conditionalSource)
  | (dump_source_head ForIn.forIn; apply listSource)
  | intro value
  | split
  | (dsimp +failIfUnchanged only))

noncomputable def doneSource (ctx : DumpCtx) : Source (dumpDoneWith (nestedOps hooks) ctx) := by
  unfold dumpDoneWith
  simp only [nestedOps]
  repeat' dump_source_step

noncomputable def replaceSource (ctx : DumpCtx) (nextCursor : Option PeerId) (done : Bool) :
    Source (dumpReplaceWith (nestedOps hooks) ctx nextCursor done) := by
  unfold dumpReplaceWith
  simp only [nestedOps]
  repeat' dump_source_step

noncomputable def finishSource (seq : UInt32) (ctx : DumpCtx) (nextCursor : Option PeerId)
    (skb : NlSkb) (flags : Nat) (attrs : List (String × Lean.Json)) (done : Bool)
    (peers : Option (Array PeerDumpAttrs)) :
    Source (dumpFinishWith (nestedOps hooks) seq ctx nextCursor skb flags attrs done peers) := by
  unfold dumpFinishWith
  simp only [nestedOps]
  repeat' first
    | (dump_source_head dumpReplaceWith; exact replaceSource _ _ _)
    | dump_source_step

noncomputable def tailSource (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) :
    Source (dumpTailWith (nestedOps hooks) d ctx skb flags attrs) := by
  unfold dumpTailWith
  simp only [nestedOps]
  repeat' first
    | (dump_source_head dumpFinishWith; exact finishSource _ _ _ _ _ _ _ _)
    | dump_source_step

noncomputable def chunkSource (ctx : DumpCtx) (seq : UInt32) (skb : NlSkb) :
    Source (dumpChunkWith (nestedOps hooks) ctx seq skb) := by
  unfold dumpChunkWith
  simp only [nestedOps]
  repeat' first
    | (dump_source_head dumpTailWith; exact tailSource _ _ _ _ _)
    | dump_source_step

noncomputable def socketSource (fd : Nat) : Source (dumpSocketWith (nestedOps hooks) fd) := by
  unfold dumpSocketWith
  simp only [nestedOps]
  repeat' first
    | (dump_source_head dumpChunkWith; exact chunkSource _ _ _)
    | (dump_source_head dumpDoneWith; exact doneSource _)
    | dump_source_step

noncomputable def startSource (fd : Nat) (ref : DeviceRef) :
    Source (dumpStartWith (nestedOps hooks) fd ref) := by
  unfold dumpStartWith
  simp only [nestedOps]
  repeat' first
    | (dump_source_head dumpSocketWith; exact socketSource _)
    | dump_source_step

noncomputable def receiveSource (fd : Nat) : Source (dumpReceiveWith (nestedOps hooks) fd) := by
  unfold dumpReceiveWith
  simp only [nestedOps]
  repeat' first
    | (dump_source_head dumpSocketWith; exact socketSource _)
    | dump_source_step

noncomputable def deviceSource (ref : DeviceRef) : Source (dumpDeviceWith (nestedOps hooks) ref) := by
  unfold dumpDeviceWith
  simp only [nestedOps,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (dump_source_head dumpStartWith; exact startSource _ _)
    | (dump_source_head dumpReceiveWith; exact receiveSource _)
    | dump_source_step

inductive Root where
  | device (ref : DeviceRef)
  | start (fd : Nat) (ref : DeviceRef)
  | receive (fd : Nat)

def Root.Result : Root → Type
  | .device _ => Except Int Lean.Json
  | .start .. => Unit
  | .receive _ => Option (List NlMessage)

def Root.action (root : Root) : WGPrefix Event root.Result := match root with
  | .device ref => dumpDeviceWith (nestedOps hooks) ref
  | .start fd ref => dumpStartWith (nestedOps hooks) fd ref
  | .receive fd => dumpReceiveWith (nestedOps hooks) fd

noncomputable def canonical (root : Root) : Source root.action := match root with
  | .device ref => deviceSource ref
  | .start fd ref => startSource fd ref
  | .receive fd => receiveSource fd

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.DumpConcrete
