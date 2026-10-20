import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerAcquireSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedOwnerWriteSource

/-! The fixed index-lookup tree expands the original bucket loop, then the
actual peer acquisition and owner-word write. List points use real successful
prefixes through the native done/yield decision. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lookup
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

inductive Shape : {α : Type} → WG.M α → Type 1 where
  | access (source : Access.Shape action) : Shape action
  | acquire (peer : Option PeerId) : Shape (peerGetMaybeZero peer)
  | ownerWrite (owner : IndexOwner) (peer : Option PeerId) : Shape (owner.setPeerWord peer)
  | bind {body : WG.M α} {next : α → WG.M β} (head : Shape body) (tail : ∀value,Shape (next value)) :
      Shape (body >>= next)

noncomputable def listShape (xs : List ι) (initial : σ) (body : ι → σ → WG.M (ForInStep σ))
    (shapes : ∀value acc,Shape (body value acc)) : Shape (forIn xs initial body) :=
  List.rec (motive:=fun values=>∀acc,Shape (forIn values acc body))
    (fun acc=>.access (.pure acc))
    (fun value rest ih acc=>(List.forIn_cons body value rest acc).symm ▸
      Shape.bind (shapes value acc) (fun decision=>match decision with
        | .done final=>.access (.pure final)
        | .yield next=>ih next)) xs initial

macro "lookup_source_step" : tactic => `(tactic| first
  | exact Shape.acquire _
  | exact Shape.ownerWrite _ _
  | exact Shape.access (.pure _)
  | exact Shape.access .read
  | exact Shape.access (.ambient _)
  | (apply Shape.access; apply Access.Shape.write; apply ReceiveFrames.device <;> intro d <;> rfl)
  | apply Shape.bind
  | apply listShape
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

noncomputable def canonical (kinds : List IndexKind) (number : Nat) : Shape (indexLookup kinds number) := by
  rw [←Affiliation.indexLookupSource_eq]
  simp only [Affiliation.indexLookupSource,Affiliation.acquireOwner,IndexOwner.peerWord,
    getKeypair,getPeer,getDev,liftIndex,branch,invariant]
  repeat' lookup_source_step

inductive Point : {α : Type} → {action : WG.M α} → Shape action →
    WGWorld → Ambient → WGWorld → Ambient → Prop where
  | entry (source : Shape action) : Point source w a w a
  | returned (source : Shape action) (performed : ((action.run w).run a)=.ok ((value,v),b)) : Point source w a v b
  | access (point : Access.Point source w a v b) : Point (.access source) w a v b
  | acquire (point : PeerAcquire.Point peer w a v b) : Point (.acquire peer) w a v b
  | ownerWrite (point : OwnerWrite.Point owner peer w a v b) : Point (.ownerWrite owner peer) w a v b
  | left {body : WG.M α} {next : α → WG.M β} {head : Shape body}
      (tail : ∀value,Shape (next value)) (point : Point head w a v b) : Point (.bind head tail) w a v b
  | right {body : WG.M α} {next : α → WG.M β} (head : Shape body) (tail : ∀value,Shape (next value))
      (leading : ((body.run w).run a)=.ok ((value,u),c)) (point : Point (tail value) u c v b) :
      Point (.bind head tail) w a v b

theorem Point.remaining {α : Type} {action : WG.M α} {source : Shape action}
    (point : Point source w a v b) : ∃remaining : WG.M α,((action.run w).run a)=((remaining.run v).run b) := by
  induction point with
  | entry source=>exact ⟨_,rfl⟩
  | returned source performed=>exact ⟨pure _,performed⟩
  | access point=>exact point.remaining
  | acquire point=>exact point.remaining
  | ownerWrite point=>exact point.remaining
  | @left α β w a v b body next head tail point ih=>
      obtain ⟨rest,same⟩:=ih
      exact ⟨rest >>= next,by simp only [StateT.run_bind,same]⟩
  | right head tail leading point ih=>
      obtain ⟨rest,same⟩:=ih
      exact ⟨rest,by simp only [StateT.run_bind,leading];exact same⟩

theorem Point.observed_remaining {α E : Type} {action : WG.M α} {source : Shape action}
    {w : World} (point : Point source w.wg w.ambient v b) (h : List E) :
    ∃remaining : PrefixM E α,runPrefix (liftWGObserver (liftWGPrefix action)) w h=
      runPrefix remaining {w with wg:=v,ambient:=b} h := by
  obtain ⟨rest,same⟩:=point.remaining
  refine ⟨liftWGObserver (liftWGPrefix rest),?_⟩
  simp only [liftWGObserver_run,runWGPrefix_lift,same]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lookup
