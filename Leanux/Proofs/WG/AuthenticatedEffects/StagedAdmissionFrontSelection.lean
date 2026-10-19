import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionFrontCallbacks

/-! Actual selection reaches either the original ledger or its one native
staged-disposal checkpoint. Both normal errors and Stop retain that history. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem conjunction (x y : Bool) :
    Preserves (QueueInv history ledger)
      (WG.andM (branch .xmitEndpointNotInet x) (branch .xmitEndpointNotInet6 y)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  cases x <;> cases y
  all_goals simp [WG.andM,branch,AmbientM.branch] at run
  all_goals rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact before

theorem decision (d : Decision) (value : Bool) :
    Preserves (QueueInv history ledger) (branch d value : WG.M Bool) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  simp [branch,AmbientM.branch] at run
  rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
  exact before

theorem environment (site : EnvSite) :
    Preserves (QueueInv history ledger) (envOk site : WG.M Bool) :=
  hoare_liftAmbient (AmbientM.envOk site) (QueueInv history ledger)

theorem unreachable :
    Preserves (QueueInv history ledger) (invariant "unreachable" : WG.M α) :=
  hoare_liftAmbient (AmbientM.invariant "unreachable") (QueueInv history ledger)

theorem idle_step (action : WG.M α) (f : α → WGPrefix Event β)
    (frame : ∀ h l, Preserves (QueueInv h l) action)
    (next : ∀ x, StatePrefixEnsures (Idle entry) (Safe entry) (f x) (fun _ => Carry entry)) :
    StatePrefixEnsures (Idle entry) (Safe entry) (liftWGPrefix action >>= f) (fun _ => Carry entry) :=
  StatePrefixEnsures.bind (idle_native frame) next

theorem select_checked (family : Nat) (packets : List Packet) (mtu : Nat)
    (peer : Option PeerId) :
    StatePrefixEnsures (Idle entry) (Safe entry)
      (HandshakeSecurity.StagedConservation.Front.selectWith ops family packets mtu peer)
      (fun _ => Carry entry) := by
  have pureCarry (result : Except Int (PeerId × List Packet)) :
      StatePrefixEnsures (Carry entry) (Safe entry) (pure result) (fun _ => Carry entry) :=
    StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.safe) (fun _ _ _ hi => hi)
  have refusal (code : Int) :
      StatePrefixEnsures (Idle entry) (Safe entry)
        (do let err ← liftWGPrefix (Packets.txError family (packets.head?.getD {bytes := []}) code)
            pure (.error err : Except Int (PeerId × List Packet))) (fun _ => Carry entry) := by
    apply idle_step _ _ (fun _ _ => Native.error _ _ _)
    intro err
    exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.carry.safe) (fun _ _ _ hi => hi.carry)
  have afterRelease (code : Int) :
      StatePrefixEnsures (Carry entry) (Safe entry)
        (do let err ← liftWGPrefix (Packets.txError family (packets.head?.getD {bytes := []}) code)
            pure (.error err : Except Int (PeerId × List Packet))) (fun _ => Carry entry) :=
    StatePrefixEnsures.bind (carry_native (fun _ _ => Native.error _ _ _)) (fun err => pureCarry (.error err))
  have tail (pid : PeerId) :
      StatePrefixEnsures (Idle entry) (Safe entry)
        (do let selected ← ops.step (Packets.txWalk packets mtu [])
            let _ ← ops.step (branch .xmitWalk false)
            ops.trim pid
            pure (.ok (pid,selected) : Except Int (PeerId × List Packet))) (fun _ => Carry entry) := by
    apply idle_step _ _ (fun _ _ => Native.walk _ _ _)
    intro selected
    apply idle_step (branch .xmitWalk false) _ (fun _ _ => decision _ _)
    intro ignored
    exact StatePrefixEnsures.bind (trim_checked pid) (fun _ => pureCarry (.ok (pid,selected)))
  unfold HandshakeSecurity.StagedConservation.Front.selectWith
  apply idle_step (branch .xmitNoPeer peer.isNone) _ (fun _ _ => decision _ _)
  intro noPeer
  split
  · apply idle_step (branch .xmitNoPeerInet (family == 4)) _ (fun _ _ => decision _ _)
    intro inet
    dsimp only
    split
    · apply idle_step (branch .xmitNoPeerInet6 (family == 6)) _ (fun _ _ => decision _ _)
      intro ignored
      exact refusal (-ENOKEY)
    · exact refusal (-ENOKEY)
  · cases peer with
    | some pid =>
      apply idle_step _ _ (fun _ _ => QueueNative.read_peer _)
      intro p
      dsimp only
      apply idle_step _ _ (fun _ _ => conjunction _ _)
      intro invalidEndpoint
      split
      · exact StatePrefixEnsures.bind (put_checked (some pid)) (fun _ => afterRelease (-EDESTADDRREQ))
      · apply idle_step (branch .xmitValidDst true) _ (fun _ _ => decision _ _)
        intro ignored
        apply idle_step (branch .xmitNotGso (packets.length < 2)) _ (fun _ _ => decision _ _)
        intro notGso
        try dsimp only
        split
        · apply idle_step (envOk .skbSegment) _ (fun _ _ => environment _)
          intro segment
          apply idle_step (branch .xmitGsoError (!segment)) _ (fun _ _ => decision _ _)
          intro error
          split
          · exact StatePrefixEnsures.bind (put_checked (some pid)) (fun _ => afterRelease (-ENOMEM))
          · exact tail pid
        · exact tail pid
    | none =>
      exact (idle_native (action := invariant "unreachable") (fun _ _ => unreachable)).consequence
        (fun _ _ _ hi => hi) (fun _ _ _ _ hi => hi.carry)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front
