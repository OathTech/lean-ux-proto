import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerMetadataCanonical
import Leanux.Proofs.WG.Cookies.Gate

/-! Cookie creation, MAC validation, load bookkeeping and endpoint updates retain their actual native accesses. Captures preserve the original entry while continuing from a reached point. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

noncomputable def makeCookieShape (src : SkbSource) : Shape (makeCookie src) := by
  unfold makeCookie
  repeat' metadata_source_step

noncomputable def cookieMessageShape (index : Nat) (src : SkbSource) (mac : Key) : Shape (cookieMessageCreate index src mac) := by
  unfold cookieMessageCreate
  repeat' first
    | (metadata_source_head makeCookie; exact makeCookieShape _)
    | metadata_source_step

noncomputable def limiterShape (src : SkbSource) : Shape (ratelimiterAllow src) := by
  unfold ratelimiterAllow
  repeat' first
    | (metadata_source_head modify; apply Shape.access; apply Access.Shape.write; apply KeyFrames.world; intro w; split <;> rfl)
    | metadata_source_step

noncomputable def validateCookieShape (msg : Key) (src : SkbSource) (check : Bool) : Shape (cookieValidatePacket msg src check) := by
  unfold cookieValidatePacket
  repeat' first
    | (metadata_source_head makeCookie; exact makeCookieShape _)
    | (metadata_source_head ratelimiterAllow; exact limiterShape _)
    | metadata_source_step

noncomputable def loadShape : Shape Cookies.loadPhase := by
  unfold Cookies.loadPhase
  repeat' first
    | (metadata_source_head modify; apply Shape.access; apply Access.Shape.write; exact KeyFrames.world _ (fun _=>rfl))
    | metadata_source_step

noncomputable def endpointShape (pid : PeerId) (src : SkbSource) : Shape (setPeerEndpointFromSkb pid src) := by
  unfold setPeerEndpointFromSkb setPeerEndpoint endpointFromSkb endpointEq dstCacheReset requireNotPending
  repeat' metadata_source_step

theorem Point.capture_remaining {α E : Type} {body : WG.M α} {source : Shape body}
    {w : World} (point : Point source w.wg w.ambient v b) (h : List E) :
    ∃remaining : PrefixM E (WGRunWitness α),runPrefix (liftWGObserver (captureWGRun body)) w h=
      runPrefix remaining {w with wg:=v,ambient:=b} h := by
  obtain ⟨rest,same⟩:=point.remaining
  refine ⟨liftWGObserver (captureWGRun rest >>= fun run=>pure {run with before:=w.wg,ambientBefore:=w.ambient}),?_⟩
  rw [liftWGObserver_bind,runPrefix_bind]
  simp only [liftWGObserver_run,runWGPrefix_captureWGRun,same]
  cases performed : (rest.run v).run b with
  | error stop=>rfl
  | ok out=>rcases out with ⟨⟨value,u⟩,c⟩;rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
