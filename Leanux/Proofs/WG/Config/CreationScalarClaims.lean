import Leanux.Proofs.WG.Config.CreationCommandSource
import Leanux.Proofs.WG.Config.ScalarCommandClaims

/-! Projected original-call scalar claims. Creation is not assumed: normal public-command execution may take UPDATE_ONLY or self-key quiet exits, return allocation refusal, or create and complete the mixed update. REMOVE_ME is handled by the separate removal result. No totality or stopped-state claim. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.CreationScalar
open Leanux Leanux.WG Noise Lifetimes Leanux.Proofs.Framing Std.Do Queues Queues.RxCredits
open PeerScalarRetention Leanux.Proofs.WG.Configuration

theorem original_create (key : Key) (psk : Option Key)
    (initial : Campaign2.State) (d : Device) (present : initial.device=some d) :
    Campaign2.Ensures (peerCreate key psk) (fun s=>s.wg=initial)
      (fun result s=>match result with
      | .error code=>code=-ENOMEM ∧ s.wg=initial
      | .ok pid=>pid=d.nextPeer ∧ observation s pid=
        some (initCell psk (newbornCell (initial.peerCounter+1)))) := by
  intro g a result final b pre run
  have device : g.dev=some d:=by
    have h:=congrArg (fun s : Campaign2.State=>s.device) pre
    exact h.trans present
  have effect:=create_selected key psk g d device g a result final b rfl run
  cases result with
  | error code=>
    obtain ⟨codeEq,same⟩:=effect
    subst final
    exact ⟨codeEq,pre⟩
  | ok pid=>
    have selected:=(peerCreate_geometry key psk g final (.ok pid) a b run).2.2
    have chosen : pid=d.nextPeer:=by simpa only [device,Option.map_some,Option.some.injEq] using selected.symm
    refine ⟨chosen,?_⟩
    have counter : g.peerCounter=initial.peerCounter:=congrArg (fun s : Campaign2.State=>s.peerCounter) pre
    change view final pid=some (initCell psk (newbornCell (initial.peerCounter+1)))
    simpa only [counter] using effect

theorem original_missing_command (cs : Ledger) (loans : Reservations)
    (attrs : PeerAttrs) (key : Key) (initial : Campaign2.State) (before : Device)
    (present : initial.device=some before)
    (pubkey : attrs.publicKey=some key)
    (valid : attrs.flags.getD 0 &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (keep : attrs.flags.getD 0 &&& WGPEER_F_REMOVE_ME=0)
    (missing : before.peerHashtable.find? (·.1 == key)=none) :
    Campaign2.Ensures (setPeerCmd attrs)
      (fun s=>Index.View.ConfigurationInput cs loans s ∧ s.wg=initial)
      (fun ret s=>Index.View.ConfigurationInput cs loans s ∧ CommandEffect attrs key initial ret s) := by
  intro g a result final b pre run
  have device : g.dev=some before :=
    (congrArg (fun s : Campaign2.State=>s.device) pre.2).trans present
  have counter : g.peerCounter=initial.peerCounter :=
    congrArg (fun s : Campaign2.State=>s.peerCounter) pre.2
  obtain ⟨account,effect⟩:=missing_command cs loans attrs key before pubkey valid protocol keep
    missing g device ((Index.configurationInput_snapshot cs loans g a).mp pre.1)
      g a result final b rfl run
  refine ⟨(Index.configurationInput_snapshot cs loans final b).mpr account,?_⟩
  rcases effect with ⟨same,value⟩ | ⟨pid,selected,scalar⟩
  · subst final
    exact Or.inl ⟨pre.2,value⟩
  · refine Or.inr ⟨pid,?_,?_⟩
    · simpa only [device,present] using selected
    · change view final pid=_
      simpa only [counter] using scalar

end Leanux.Proofs.WG.Config.CreationScalar
