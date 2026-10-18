import Leanux.Proofs.WG.AuthenticatedEffects.CookieProtocol
import Leanux.Proofs.WG.Packets.PublicationIdentity

/-! Exact normal native decrypt effects. The sole state-changing arm is the
existing receive-policy invalidation before AEAD; all other normal outcomes,
including ciphertext authentication failure, preserve the entire WG world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.CounterWindow
open Leanux.Proofs.WG.MaterialOrigin Leanux.Proofs.WG.KeyTimes
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem decryptPacket_effect (pkt : RxPacket) (result : Option RxPacket)
    (w v : WGWorld) (a b : Ambient)
    (run : ((decryptPacket pkt).run w).run a = .ok ((result,v),b)) :
    v = w ∨ result = none ∧ ∃ d k c,
      w.dev = some d ∧ d.keypairs[pkt.keypair]? = some k ∧
      ((receiveReject k).run w).run (record a .decNoKeypair false) = .ok ((true,w),c) ∧
      v = CounterWindow.store w pkt.keypair {k with receiving := {k.receiving with isValid := false}} := by
  rw [decryptPacket_factor] at run
  simp only [branch,StateT.run_monadLift,monadLift_self,StateT.run_bind,branch_run,
    except_ok_bind,StateT.run_pure,except_pure,Bool.false_eq_true,↓reduceIte] at run
  cases read : ((getKeypair pkt.keypair).run w).run (record a .decNoKeypair false) with
  | error err => simp [read] at run
  | ok readOut =>
    rcases readOut with ⟨⟨k,u⟩,c⟩
    obtain ⟨world,ambient,d,hd,hk⟩ := getKeypair_return pkt.keypair w u k _ c read
    subst u
    subst c
    simp only [read,except_ok_bind] at run
    cases policy : ((receiveReject k).run w).run (record a .decNoKeypair false) with
    | error err => simp [policy] at run
    | ok policyOut =>
      rcases policyOut with ⟨⟨reject,u⟩,c⟩
      have world := (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
        (Leanux.Proofs.WG.Origins.receiveReject_sameWGWorld k) w _ reject u c policy
      change u = w at world
      subst u
      cases reject with
      | false =>
        simp only [policy,except_ok_bind,Bool.false_eq_true,↓reduceIte] at run
        exact Or.inl ((Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
          (Leanux.Proofs.WG.Origins.receiveTail_sameWGWorld pkt k) w c result v b run)
      | true =>
        simp only [policy,except_ok_bind,↓reduceIte] at run
        simp [getKeypair,getDev,setKeypair,modifyDev,hd,hk,StateT.run_bind] at run
        obtain ⟨⟨resultEq,worldEq⟩,_⟩ := run
        exact Or.inr ⟨resultEq.symm,d,k,c,hd,hk,policy,by simpa [CounterWindow.store,hd] using worldEq.symm⟩

theorem decryptPacket_peer_and_sent (pkt : RxPacket) (result : Option RxPacket)
    (w v : WGWorld) (a b : Ambient)
    (run : ((decryptPacket pkt).run w).run a = .ok ((result,v),b)) :
    PeerBorrow.resident (wgStoreView v) = PeerBorrow.resident (wgStoreView w) ∧ v.sent = w.sent := by
  rcases decryptPacket_effect pkt result w v a b run with same | changed
  · subst v
    exact ⟨rfl,rfl⟩
  · obtain ⟨_,d,k,c,hd,_,_,same⟩ := changed
    subst v
    refine ⟨?_,rfl⟩
    funext pid
    simp [CounterWindow.store,wgStoreView,PeerBorrow.resident,hd]

end Leanux.Proofs.WG.AuthenticatedEffects
