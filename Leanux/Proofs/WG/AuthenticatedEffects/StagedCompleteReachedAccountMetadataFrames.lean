import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAccountMetadataSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryReceiveFrames

/-! Allocation geometry is preserved alongside the same packet ledger.
The peer identity used by a write comes from its original successful read. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.AccountMetadata
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity CausalJournal

theorem update_frame (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p,(f p).internalId=p.internalId ∧ (f p).staged=p.staged ∧ (f p).txQueue=p.txQueue) :
    SameView view (getPeer pid >>= fun p=>setPeer pid (f p)) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b performed
  have packets := (ProjectedAction.iff_run_ambient _ _ _).mp (Queued.update pid f same) _ _ _ _ _ performed
  rw [MaterialOrigin.bind_ok_ambient] at performed
  obtain ⟨p,u,c,read,write⟩ := performed
  obtain ⟨rfl,rfl,live⟩ := Peers.getPeer_current pid w u p a c read
  cases value
  have identity := setPeer_identity pid (f p) _ v _ b (by simpa only [(same p).1] using live) write
  have metadata := (ProjectedAction.iff_run_ambient _ _ _).mp (setPeer_metadata pid (f p)) _ _ () v b write
  exact Prod.ext packets (Prod.ext identity metadata)

theorem Shape.frame (source : Shape action) : SameView view action := by
  induction source with
  | pure value => exact SameView.pure _ _
  | reading source =>
      apply (ProjectedAction.iff_run_ambient _ _ _).mpr
      intro w a value v b performed
      exact congrArg view (ReadGetter.normal source performed).1
  | ambient body => exact fun initial=>hoare_liftAmbient body (fun w=>view w=initial)
  | write update same => exact fun initial=>hoare_modify update (fun w before=>(same w).trans before)
  | update pid f same => exact update_frame pid f same
  | bind head tail ihHead ihTail => exact SameView.bind ihHead ihTail

theorem Point.projection (point : Point source w a v b) : view v=view w := by
  induction point with
  | entry source => rfl
  | returned source performed => exact (ProjectedAction.iff_run_ambient _ _ _).mp source.frame _ _ _ _ _ performed
  | reading point => exact congrArg view point.state.1
  | updateRead same point => exact congrArg view point.state.1
  | left tail point ih => exact ih
  | right head tail leading point ih => exact ih.trans ((ProjectedAction.iff_run_ambient _ _ _).mp head.frame _ _ _ _ _ leading)

theorem carrier_transport (h : List Event) (w v : World)
    (same : view v.wg=view w.wg) (before : CompleteProduct.Carrier h w) : CompleteProduct.Carrier h v := by
  obtain ⟨⟨ledger,accounted⟩,history,allocated⟩ := before
  exact ⟨⟨ledger,accounted.same_view (congrArg Prod.fst same)⟩,history,
    allocated.congr (congrArg (fun s=>s.2.1) same) (congrArg (fun s=>s.2.2) same)⟩

theorem device_view (f : Device → Device)
    (epoch : ∀ d,(f d).ifindex=d.ifindex) (peers : ∀ d,(f d).peers=d.peers)
    (frontier : ∀ d,(f d).nextSkb=d.nextSkb)
    (tx : ∀ d,(f d).txSkbs=d.txSkbs) (rx : ∀ d,(f d).rxSkbs=d.rxSkbs)
    (keys : ∀ d,(f d).keypairs=d.keypairs)
    (nextPeer : ∀ d,(f d).nextPeer=d.nextPeer)
    (nextKey : ∀ d,(f d).nextKeypairId=d.nextKeypairId) (w : WGWorld) :
    view {w with dev:=w.dev.map f}=view w := by
  let ambient : Ambient := {env:=fun _ _=>false,timing:=Env.timing}
  have packets := (ProjectedAction.iff_run_ambient _ _ _).mp
    (ReceiveFrames.device f epoch peers frontier tx rx) w ambient () _ ambient rfl
  apply Prod.ext packets
  apply Prod.ext
  · change identityView {w with dev:=w.dev.map f}=identityView w
    apply Prod.ext
    · simp [identityView,Peers.snapshot,Option.bind_map,Function.comp_def,peers]
    apply Prod.ext
    · funext i
      simp [identityView,Lifetimes.keypairResidents,Option.bind_map,Function.comp_def,keys]
    · funext slot
      cases slot <;>
        simp [identityView,Lifetimes.packetResidents,Option.bind_map,Function.comp_def,epoch,tx,rx]
  · simp [view,allocationMetadata,deviceAllocationMetadata,Option.map_map,
      Function.comp_def,epoch,frontier,nextPeer,nextKey]
    rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.AccountMetadata
