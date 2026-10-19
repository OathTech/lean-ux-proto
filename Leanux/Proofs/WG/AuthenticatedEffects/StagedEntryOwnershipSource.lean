import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryOwnershipHistory

/-! The physical receipt invariant follows the actual check, lookup, selection
and splice spine. Stop retains the same native-cut history as ledger accounting. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front.Ownership
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal
set_option pp.structureInstances false
variable {initial : WGWorld} {base : List Event}

theorem decision (d : Decision) (value : Bool) : SameView view (branch d value : WG.M Bool) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  simp [branch,AmbientM.branch] at run
  rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
  rfl

theorem conjunction (x y : Bool) :
    SameView view (WG.andM (branch .xmitEndpointNotInet x) (branch .xmitEndpointNotInet6 y)) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  cases x <;> cases y
  all_goals simp [WG.andM,branch,AmbientM.branch] at run
  all_goals rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; rfl

theorem environment (site : EnvSite) : SameView view (envOk site : WG.M Bool) := by
  intro initial
  exact hoare_liftAmbient (AmbientM.envOk site) _

theorem unreachable : SameView view (invariant "unreachable" : WG.M α) := by
  intro initial
  exact hoare_liftAmbient (AmbientM.invariant "unreachable") _

theorem step_checked (action : WG.M α) (f : α → WGPrefix Event β)
    (frame : SameView view action)
    (next : ∀ x, StatePrefixEnsures (State base initial) (Checked base initial) (f x) (fun _ => State base initial)) :
    StatePrefixEnsures (State base initial) (Checked base initial) (liftWGPrefix action >>= f) (fun _ => State base initial) :=
  StatePrefixEnsures.bind (native frame) next

theorem select_checked (family : Nat) (packets : List Packet) (mtu : Nat)
    (peer : Option PeerId) :
    StatePrefixEnsures (State base initial) (Checked base initial)
      (HandshakeSecurity.StagedConservation.Front.selectWith ops family packets mtu peer)
      (fun _ => State base initial) := by
  have pureCarry (result : Except Int (PeerId × List Packet)) :
      StatePrefixEnsures (State base initial) (Checked base initial) (pure result) (fun _ => State base initial) :=
    StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)
  have refusal (code : Int) :
      StatePrefixEnsures (State base initial) (Checked base initial)
        (do let err ← liftWGPrefix (Packets.txError family (packets.head?.getD {bytes := []}) code)
            pure (.error err : Except Int (PeerId × List Packet))) (fun _ => State base initial) := by
    apply step_checked _ _ (error _ _ _)
    intro err
    exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)
  have afterRelease (code : Int) :
      StatePrefixEnsures (State base initial) (Checked base initial)
        (do let err ← liftWGPrefix (Packets.txError family (packets.head?.getD {bytes := []}) code)
            pure (.error err : Except Int (PeerId × List Packet))) (fun _ => State base initial) :=
    StatePrefixEnsures.bind (native (error _ _ _)) (fun err => pureCarry (.error err))
  have tail (pid : PeerId) :
      StatePrefixEnsures (State base initial) (Checked base initial)
        (do let selected ← ops.step (Packets.txWalk packets mtu [])
            let _ ← ops.step (branch .xmitWalk false)
            ops.trim pid
            pure (.ok (pid,selected) : Except Int (PeerId × List Packet))) (fun _ => State base initial) := by
    apply step_checked _ _ (walk _ _ _)
    intro selected
    apply step_checked (branch .xmitWalk false) _ (decision _ _)
    intro ignored
    exact StatePrefixEnsures.bind (trim_checked pid) (fun _ => pureCarry (.ok (pid,selected)))
  unfold HandshakeSecurity.StagedConservation.Front.selectWith
  apply step_checked (branch .xmitNoPeer peer.isNone) _ (decision _ _)
  intro noPeer
  split
  · apply step_checked (branch .xmitNoPeerInet (family == 4)) _ (decision _ _)
    intro inet
    dsimp only
    split
    · apply step_checked (branch .xmitNoPeerInet6 (family == 6)) _ (decision _ _)
      intro ignored
      exact refusal (-ENOKEY)
    · exact refusal (-ENOKEY)
  · cases peer with
    | some pid =>
      apply step_checked _ _ (read_peer _)
      intro p
      dsimp only
      apply step_checked _ _ (conjunction _ _)
      intro invalidEndpoint
      split
      · exact StatePrefixEnsures.bind (put_checked (some pid)) (fun _ => afterRelease (-EDESTADDRREQ))
      · apply step_checked (branch .xmitValidDst true) _ (decision _ _)
        intro ignored
        apply step_checked (branch .xmitNotGso (packets.length < 2)) _ (decision _ _)
        intro notGso
        try dsimp only
        split
        · apply step_checked (envOk .skbSegment) _ (environment _)
          intro segment
          apply step_checked (branch .xmitGsoError (!segment)) _ (decision _ _)
          intro error
          split
          · exact StatePrefixEnsures.bind (put_checked (some pid)) (fun _ => afterRelease (-ENOMEM))
          · exact tail pid
        · exact tail pid
    | none =>
      exact (native (action := invariant "unreachable") unreachable).consequence
        (fun _ _ _ hi => hi) (fun _ _ _ _ hi => hi)


theorem body_checked (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StatePrefixPreserves (State base initial) (Checked base initial) (body family addr packets mtu) := by
  unfold body HandshakeSecurity.StagedConservation.Front.frontWith
  apply StatePrefixEnsures.bind (native (check family addr packets mtu))
  intro accepted
  split
  · exact pure_checked _
  · apply StatePrefixEnsures.bind (native (lookup family addr))
    intro peer
    apply StatePrefixEnsures.bind (select_checked family packets mtu peer)
    intro result
    cases result with
    | error err => exact pure_checked _
    | ok pair =>
      rcases pair with ⟨pid,selected⟩
      exact StatePrefixEnsures.bind (native (splice pid selected)) (fun _ => pure_checked _)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front.Ownership
