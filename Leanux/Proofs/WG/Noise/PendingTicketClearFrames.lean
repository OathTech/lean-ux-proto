import Leanux.Proofs.WG.Noise.PendingTicketRetentionFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing

/-- Updating a peer can retain or clear its pending slot, but cannot install
another slot. Surviving tickets therefore retain the same allocation stamp. -/
theorem modifyPeer_retained (pid : PeerId) (f : Peer → Peer)
    (next : ∀ p kid, (f p).keypairNext = some kid → p.keypairNext = some kid) :
    RetainsCall (do setPeer pid (f (← getPeer pid))) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v after run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,current,inputs,read,write⟩ := run
  obtain ⟨rfl,rfl,d,device,resident⟩ := Origins.getPeer_return pid w current p ambient inputs read
  simp [setPeer,modifyDev,device] at write
  obtain ⟨⟨rfl,rfl⟩,rfl⟩ := write
  refine ⟨rfl,?_⟩
  intro tracked stamp has
  by_cases same : pid = tracked
  · subst tracked
    change pending {d with peers := d.peers.insert pid (f p)} pid = some stamp at has
    simp only [view,device,Option.bind_some]
    simp only [pending,Std.TreeMap.getElem?_insert_self,resident,bind,Option.bind] at has ⊢
    obtain ⟨kid,hnext,hkey⟩ := Option.bind_eq_some_iff.mp has
    exact Option.bind_eq_some_iff.mpr ⟨kid,next p kid hnext,hkey⟩
  · simpa [view,device,pending,Std.TreeMap.getElem?_insert,same] using has

private theorem getPeer_frame (pid : PeerId) : SameView view (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient p v after run
  exact congrArg view (Origins.getPeer_return pid w v p ambient after run).1

theorem keypairsClear_retained (pid : PeerId) : RetainsCall (keypairsClear pid) := by
  unfold keypairsClear
  apply retains_bind (retained_of_frame (getPeer_frame pid))
  intro p
  apply retains_bind (modifyPeer_retained pid (fun p => {p with keypairNext := none})
    (by intro p kid h; cases h))
  intro _
  apply retains_bind (keypairPut_retained p.keypairNext true)
  intro _
  apply retains_bind (retained_of_frame (getPeer_frame pid))
  intro p
  apply retains_bind (modifyPeer_retained pid (fun p => {p with keypairPrevious := none})
    (by intro p kid h; exact h))
  intro _
  apply retains_bind (keypairPut_retained p.keypairPrevious true)
  intro _
  apply retains_bind (retained_of_frame (getPeer_frame pid))
  intro p
  apply retains_bind (modifyPeer_retained pid (fun p => {p with keypairCurrent := none})
    (by intro p kid h; exact h))
  intro _
  exact keypairPut_retained p.keypairCurrent true

/-- The whole clear worker removes pending tickets through its actual ordered
key releases and final peer release. Failed releases remain original Stops. -/
theorem queuedExpiredZeroKeyMaterial_retained (pid : PeerId) :
    RetainsCall (queuedExpiredZeroKeyMaterial pid) := by
  unfold queuedExpiredZeroKeyMaterial
  apply retains_bind (retained_of_frame (handshakeClear_frame pid))
  intro _
  apply retains_bind (keypairsClear_retained pid)
  intro _
  exact peerPut_retained (some pid)

end Leanux.Proofs.WG.Noise.PendingTickets
