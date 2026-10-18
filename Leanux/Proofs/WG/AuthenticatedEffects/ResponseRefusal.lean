import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeQuietFrames

/-! Response refusal repays an actual lookup loan. The named `Borrowed`
premise is the remaining index-lookup obligation; it is not inferred from
an arbitrary endpoint's spare reference count. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.CounterWindow
open Leanux.Proofs.WG.Queues.RxCredits.HandshakeLoans
open Leanux.Proofs.WG.Cookies
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private def ResponseRestores (initial : WGStoreView) (result : Option PeerId) (w : WGWorld) : Prop :=
  result = none → PeerBorrow.view w = (PeerBorrow.outsidePeers initial,PeerBorrow.resident initial)

private theorem chain {α β : Type} (P : WGWorld → Prop) (Q : β → WGWorld → Prop)
    (action : WG.M α) (next : α → WG.M β) (ha : Preserves P action)
    (tail : ∀ x, Hoare (next x) P Q) : Hoare (action >>= next) P Q :=
  hoare_bind action next ha tail

theorem responseTail_refusal_restores (msg : Key) (identity : StaticIdentity)
    (pid : PeerId) (initial : WGStoreView) :
    Hoare (responseTail msg identity pid)
      (fun w => PeerBorrow.Borrowed initial (some pid) (wgStoreView w)) (ResponseRestores initial) := by
  let P := fun w => PeerBorrow.Borrowed initial (some pid) (wgStoreView w)
  have read (q : PeerId) : Preserves P (getPeer q) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b hi run
    rw [(Leanux.Proofs.WG.Queues.getPeer_normal q w v p a b run).1]
    exact hi
  have failed : Hoare (do peerPut (some pid); pure (none : Option PeerId)) P (ResponseRestores initial) := by
    apply hoare_bind _ _ (PeerBorrow.repay_spec (some pid) initial)
    intro doneUnit
    apply hoare_consequence (hoare_pure none _)
    · exact fun _ h => h
    · intro result w h _
      exact h.2
  have success (p : Peer) : Hoare (do setPeer pid p; pure (some pid)) P (ResponseRestores initial) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi run none
    simp only [setPeer,modifyDev,StateT.run_bind,StateT.run_modify,StateT.run_pure,
      except_ok_bind,except_pure] at run
    cases run
    cases none
  have ambient {α : Type} (action : AmbientM α) : Preserves P (monadLift action : WG.M α) :=
    hoare_liftAmbient action P
  have stop (message : String) : Hoare (invariant message : WG.M (Option PeerId)) P (ResponseRestores initial) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi run
    cases run
  unfold responseTail
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | with_reducible exact failed
    | with_reducible exact success _
    | with_reducible exact stop _
    | with_reducible exact read _
    | with_reducible exact ambient _
    | receive_crypto P
    | cookie_source_step
    | with_reducible apply chain P
    | (session_origin_intro_forall; try dsimp only)
    | split

/-- The original response consumer restores the supplied pre-lookup store
when its actual successful lookup carries the named loan and Noise refuses. -/
theorem response_refusal_after_lookup (msg : Key) (w u v : WGWorld) (d : Device)
    (owner pid : PeerId) (a b c : Ambient)
    (device : w.dev = some d) (identity : d.staticIdentity.hasIdentity = true)
    (lookup : ((indexLookup [.handshake] (u32le msg 8)).run w).run
      (record a .crespNoIdentity false) = .ok ((some (.handshake owner,pid),u),b))
    (borrowed : PeerBorrow.Borrowed (wgStoreView w) (some pid) (wgStoreView u))
    (refused : ((consumeResponse msg).run w).run a = .ok ((none,v),c)) :
    PeerBorrow.view v = PeerBorrow.view w := by
  rw [consumeResponse_factor] at refused
  simp [getDev,device,StateT.run_bind,branch,branch_run,identity,lookup] at refused
  exact (hoare_iff_run_ambient _ _ _).mp
    (responseTail_refusal_restores msg d.staticIdentity pid (wgStoreView w))
    u _ none v c borrowed refused rfl

end Leanux.Proofs.WG.AuthenticatedEffects
