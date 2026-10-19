import Leanux.Proofs.Framing.WGTime
import Leanux.Proofs.Framing.WGOwned
import Leanux.Proofs.Framing.Tools
import Leanux.WG.Socket

/-! Canonical socket-control frames. Only the two socket labels and incoming
port are masked. The other eleven-field observations and complete resident
objects remain; actual Ambient inputs and outputs are unrestricted. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

def socketDevice (d : Device) : Device :=
  {d with sock4 := none, sock6 := none, incomingPort := 0}

def socketView (g : WGWorld) : WGOwnedView :=
  {wgOwnedView g with dev := g.dev.map socketDevice}

abbrev SameSocket (a : WG.M α) := SameView socketView a

theorem modifyDev_socket_spec (P : WGOwnedView → Prop) (f : Device → Device)
    (hf : ∀ d, socketDevice (f d) = socketDevice d) :
    ⦃fun w => ⌜P (socketView w)⌝⦄ modifyDev f
    ⦃⇓? _ w => ⌜P (socketView w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hp hr
  cases hr
  simpa [socketView, wgOwnedView, wgStoreView, modifyDev,
    Option.map_map, Function.comp_def, hf] using hp

theorem sockFree_sameWGWorld (sock : Option Nat) :
    SameView (id : WGWorld → WGWorld) (sockFree sock) := by
  unfold sockFree
  apply SameView.bind (fun initial => hoare_liftAmbient
    (AmbientM.branch .sockFreeNull sock.isNone) (fun w => w = initial))
  intro isNull
  split
  · exact SameView.pure _ _
  · exact fun initial => hoare_liftAmbient (AmbientM.iputReport true) (fun w => w = initial)

theorem socketReinit_sameSocket (new4 new6 : Option Nat) :
    SameSocket (socketReinit new4 new6) := by
  have read : SameSocket getDev := by
    apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient d v ambient' hr
    cases hd : w.dev <;> simp [getDev, hd, invariant, AmbientM.invariant] at hr
    · cases hr
    · cases hr
      rfl
  have edit (f : Device → Device) (hf : ∀ d, socketDevice (f d) = socketDevice d) :
      SameSocket (modifyDev f) := fun initial => modifyDev_socket_spec (fun s => s = initial) f hf
  have hb (d : Decision) (b : Bool) : SameSocket (branch d b) :=
    fun initial => hoare_liftAmbient (AmbientM.branch d b) (fun w => socketView w = initial)
  have hi {α : Type} (message : String) : SameSocket (invariant message : WG.M α) :=
    fun initial => hoare_liftAmbient (AmbientM.invariant message) (fun w => socketView w = initial)
  unfold socketReinit
  apply SameView.bind read
  intro d
  dsimp only
  apply SameView.bind (edit (fun old => {old with sock4 := new4, sock6 := new6}) (fun _ => rfl))
  intro _
  apply SameView.bind (hb _ _)
  intro has
  split
  · split
    · rename_i port
      apply SameView.bind (edit (fun old => {old with incomingPort := port}) (fun _ => rfl))
      intro _
      exact SameView.bind ((sockFree_sameWGWorld _).factor socketView)
        (fun _ => (sockFree_sameWGWorld _).factor socketView)
    · apply SameView.bind (hi "unreachable" : SameSocket (invariant "unreachable" : WG.M Unit))
      intro _
      exact SameView.bind ((sockFree_sameWGWorld _).factor socketView)
        (fun _ => (sockFree_sameWGWorld _).factor socketView)
  · exact SameView.bind ((sockFree_sameWGWorld _).factor socketView)
      (fun _ => (sockFree_sameWGWorld _).factor socketView)

theorem socketInit_sameSocket (port : Nat) : SameSocket (socketInit port) := by
  have read : SameSocket getDev := by
    apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient d v ambient' hr
    cases hd : w.dev <;> simp [getDev, hd, invariant, AmbientM.invariant] at hr
    · cases hr
    · cases hr
      rfl
  have getWorld : SameSocket (get : WG.M WGWorld) := by
    apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient d v ambient' hr
    cases hr
    rfl
  have ambient {α : Type} (a : AmbientM α) : SameSocket (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => socketView w = initial)
  unfold socketInit
  apply SameView.bind read
  intro d
  split
  · exact SameView.pure _ _
  · apply SameView.bind getWorld
    intro w
    split
    · apply SameView.bind (ambient (AmbientM.hidden .udpPortDraw))
      intro bytes
      dsimp only
      simp only [pure_bind]
      split
      · exact SameView.bind
          (ambient (AmbientM.unsupported "the random port draw collides with a bound port") :
            SameSocket (unsupported "the random port draw collides with a bound port" : WG.M Unit))
          (fun _ => SameView.bind (socketReinit_sameSocket _ _) (fun _ => SameView.pure _ _))
      · exact SameView.bind (socketReinit_sameSocket _ _) (fun _ => SameView.pure _ _)
    · dsimp only
      simp only [pure_bind]
      split
      · exact SameView.bind (ambient (AmbientM.iputReport true)) (fun _ => SameView.pure _ _)
      · exact SameView.bind (socketReinit_sameSocket _ _) (fun _ => SameView.pure _ _)

end Leanux.Proofs.Framing
