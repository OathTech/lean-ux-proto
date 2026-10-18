import Leanux.Proofs.WG.RetirementSecurity.SlotPayments

/-! Native read, branch and peer-update rules for transferring key references
between publication slots and source locals without changing their funding. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing

theorem read_bind_account (pid : PeerId) (p : Peer) (credits : Credits.Ledger)
    (f : Peer → WG.M α) (post : α → WGWorld → Prop)
    (body : Hoare (f p) (PeerAccount pid p credits) post) :
    Hoare (getPeer pid >>= f) (PeerAccount pid p credits) post := by
  apply hoare_bind _ _ (read_peer_account pid p credits)
  intro actual
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  obtain ⟨equal,hi⟩ := hi
  subst actual
  exact (hoare_iff_run_ambient _ _ _).mp body w a result v b hi run

theorem branch_bind (decision : Decision) (value : Bool) (P : WGWorld → Prop)
    (f : Bool → WG.M α) (post : α → WGWorld → Prop) (body : Hoare (f value) P post) :
    Hoare ((branch decision value : WG.M Bool) >>= f) P post := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  simp only [branch,StateT.run_monadLift,monadLift_self,StateT.run_bind,
    CounterWindow.branch_run,CounterWindow.except_ok_bind] at run
  exact (hoare_iff_run_ambient _ _ _).mp body w _ result v b hi run

def updatePeer (pid : PeerId) (f : Peer → Peer) : WG.M Unit := do
  let p ← getPeer pid
  setPeer pid (f p)

theorem update_peer_account (pid : PeerId) (p : Peer) (credits : Credits.Ledger)
    (f : Peer → Peer) : Hoare (updatePeer pid f) (PeerAccount pid p credits)
      (fun _ => PeerAccount pid (f p) credits) :=
  read_bind_account pid p credits _ _ (write_peer_account pid p (f p) credits)

theorem PeerAccount.perm (hi : PeerAccount pid p credits w) (order : credits.Perm other) :
    PeerAccount pid p other w := ⟨hi.1,hi.2.perm order⟩

end Leanux.Proofs.WG.RetirementSecurity
