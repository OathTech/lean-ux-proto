import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTrafficStoreSource
import Leanux.Proofs.WG.AuthenticatedEffects.DeliverySource

/-! Observation and netlink plumbing retain their original getter and
fixture-write steps. The netlink setter is already one literal native write. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductStore
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

macro "dispatch_store_step" : tactic => `(tactic| first
  | exact Shape.reading ProductRead.environmentShape
  | exact Shape.reading ProductRead.routingShape
  | traffic_store_step)

noncomputable def observeFrontShape : Shape DeliverySource.observeFront := by
  unfold DeliverySource.observeFront Env.requireNoCryptWork
  repeat' dispatch_store_step

noncomputable def observeFinishShape : Shape DeliverySource.observeFinish := by
  unfold DeliverySource.observeFinish
  repeat' dispatch_store_step

def netlinkReadShape (fd : Nat) : Shape (liftWG (getNlSock fd)) :=
  .reading (.wg (.bind .read (fun _=>.pure _)))

theorem netlinkWrite_source (fd : Nat) (sock : NlSock) :
    liftWG (setNlSock fd sock) = (modify fun w : World=>
      {w with wg:=if fd==8 then {w.wg with nlSock8:=sock} else {w.wg with nlSock7:=sock}}) := by
  funext w
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductStore
