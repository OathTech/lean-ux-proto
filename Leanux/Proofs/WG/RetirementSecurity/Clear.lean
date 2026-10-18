import Leanux.Proofs.WG.RetirementSecurity.Frames
import Leanux.Proofs.WG.Keypairs.MaterialOrigin

/-! Normal key clearing empties the three published peer slots. This does
not imply removal of allocations still retained by packet references. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing

def peerProperty (pid : PeerId) (P : Peer → Prop) (w : WGWorld) : Prop :=
  ∀ p, (w.dev.bind fun d => d.peers[pid]?) = some p → P p

private theorem put_peerProperty (pid : PeerId) (P : Peer → Prop)
    (kp : Option KeypairId) (now : Bool) :
    Preserves (peerProperty pid P) (keypairPut kp now) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases result
  have equal := congrArg (fun maps => maps.bind fun peers => peers[pid]?)
    (put_peers kp now w v a b run)
  simp only [peersAt,Option.bind_map,Function.comp_def] at equal
  intro p found
  exact hi p (equal.symm.trans found)

private theorem update_peerProperty (pid : PeerId) (P Q : Peer → Prop)
    (f : Peer → Peer) (step : ∀ p, P p → Q (f p)) :
    Hoare (do let p ← getPeer pid; setPeer pid (f p))
      (peerProperty pid P) (fun _ => peerProperty pid Q) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,read,write⟩ := run
  cases device : w.dev with
  | none => simp [getPeer,getDev,device,invariant,AmbientM.invariant] at read; cases read
  | some d =>
    cases stored : d.peers[pid]? with
    | none => simp [getPeer,getDev,device,stored,invariant,AmbientM.invariant] at read; cases read
    | some old =>
      simp [getPeer,getDev,device,stored] at read
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := read
      cases write
      intro p found
      have eq : f old = p := by simpa [device] using found
      subst p
      exact step old (hi old (by simp [device,stored]))

def SlotsCleared (pid : PeerId) : WGWorld → Prop :=
  peerProperty pid fun p => p.keypairNext = none ∧
    p.keypairPrevious = none ∧ p.keypairCurrent = none

theorem clear_slots (pid : PeerId) :
    Hoare (keypairsClear pid) (fun _ => True) (fun _ => SlotsCleared pid) := by
  let next : Peer → Prop := fun p => p.keypairNext = none
  let previous : Peer → Prop := fun p => p.keypairNext = none ∧ p.keypairPrevious = none
  let done : Peer → Prop := fun p => p.keypairNext = none ∧
    p.keypairPrevious = none ∧ p.keypairCurrent = none
  unfold keypairsClear
  apply hoare_bind _ _ (getPeer_preserves pid (fun _ => True))
  intro p
  apply hoare_bind _ _ (hoare_consequence
    (update_peerProperty pid (fun _ => True) next (fun p => {p with keypairNext := none})
      (fun _ _ => rfl)) (fun _ _ _ _ => True.intro) (fun _ _ h => h))
  intro _
  apply hoare_bind _ _ (put_peerProperty pid next p.keypairNext true)
  intro _
  apply hoare_bind _ _ (getPeer_preserves pid (peerProperty pid next))
  intro p
  apply hoare_bind _ _ (update_peerProperty pid next previous
    (fun p => {p with keypairPrevious := none}) (fun _ h => ⟨h,rfl⟩))
  intro _
  apply hoare_bind _ _ (put_peerProperty pid previous p.keypairPrevious true)
  intro _
  apply hoare_bind _ _ (getPeer_preserves pid (peerProperty pid previous))
  intro p
  apply hoare_bind _ _ (update_peerProperty pid previous done
    (fun p => {p with keypairCurrent := none}) (fun _ h => ⟨h.1,h.2,rfl⟩))
  intro _
  exact put_peerProperty pid done p.keypairCurrent true

end Leanux.Proofs.WG.RetirementSecurity
