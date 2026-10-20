import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCookieRouteSource

/-! Cookie route points preserve the complete TX projection using the original route/cache frames and exact erasure. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CookieRoute
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open SocketInterior

theorem Point.frame (point : Point args w a v b) : StagedEntry.view v=StagedEntry.view w := by
  cases point with
  | source point=>exact point.view (SocketRoute.canonical_framed _ _ _ _ _ _ [])

theorem action_frame (args : ProtocolSocket.Args) : SameView StagedEntry.view (action args) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  have erased := route_erases args w a []
  rw [←erased] at run
  have performed : runWGPrefix
      (SocketInterior.route args.endpoint args.cache args.bytes args.ds args.exactRx args.ipv4) w a []=
      (.ok ((value,v),b),(runWGPrefix
        (SocketInterior.route args.endpoint args.cache args.bytes args.ds args.exactRx args.ipv4) w a []).2) :=
    Prod.ext run rfl
  exact (SocketRoute.canonical_framed _ _ _ _ _ _ []).normal performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CookieRoute
