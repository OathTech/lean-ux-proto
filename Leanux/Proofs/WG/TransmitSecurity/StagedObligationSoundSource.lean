import Leanux.Proofs.WG.TransmitSecurity.StagedObligationSelectionCarrier
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationSoundHeld

/-! The actual staged selection retains semantic terminal evidence and
birth-to-allocation links from its take cut through borrowing and nonce checks.
The two consuming callbacks remain explicit source obligations. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.SoundHeld
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open Staged.Origins AuthenticatedEffects CausalJournal StagedProvenance
open HandshakeSecurity.StagedConservation

theorem borrow (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (Safe : List Event → Prop)
    (frontier : ∀ h, Active ledger debts generation pid peer position h → Safe h) :
    StatePrefixEnsures (Held ledger debts generation pid peer position) Safe
      (liftWGPrefix (Take.borrow (some peer)))
      (fun selected h w a => ∃ keypair, selected = some (peer,keypair) ∧
        Held ledger debts generation pid peer position h w a) := by
  intro w a h before
  obtain ⟨suffix,extended,active,post⟩ :=
    HeldFrontier.borrow_held ledger debts generation pid peer position
      (HeldFrontier.Anchor ledger debts generation pid peer position) (fun _ => id)
      w a h before.toHeld
  have justified : Justified
      (runPrefix ((liftWGPrefix (Take.borrow (some peer))).run w) a h).2 ledger := by
    rw [extended]
    exact before.justified.append suffix
  have links : AllocationLinks
      (runPrefix ((liftWGPrefix (Take.borrow (some peer))).run w) a h).2 ledger := by
    rw [extended]
    exact before.links.append suffix
  refine ⟨suffix,extended,frontier _ ⟨active,justified,links,before.only⟩,?_⟩
  cases result : (runPrefix ((liftWGPrefix (Take.borrow (some peer))).run w) a h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    rw [result] at post
    obtain ⟨keypair,selected,held⟩ := post
    exact ⟨keypair,selected,held,justified,links,before.only⟩

theorem selected_event (before : Held ledger debts generation pid peer position h w a)
    (run : WGRunWitness (Option (Peer × Option KeypairId))) :
    Held ledger debts generation pid peer position
      (h ++ [Event.old (.responder (.selected pid run))]) w a :=
  ⟨before.toHeld.views_append _ (by
      intro e member
      have same := List.mem_singleton.mp member
      subst e
      rfl) rfl rfl rfl,
    before.justified.append _,before.links.append _,before.only⟩

/-- This actual native take initializes the fixed selected ledger. Borrowing
and nonce checks retain a concrete active frontier on Stop. The same exact
ordered batch reaches the submission callback; no old successful selection
receipt or containing-call success is assumed. -/
theorem after_take (r : Take.Receipt) (native : r.Valid) (chosen : r.run.value = some peer)
    (before : Core history ledger debts r.run.before)
    (justified : Justified history ledger) (links : AllocationLinks history ledger)
    (idle : NoSelected ledger)
    (Safe : List Event → Prop) (Post : List Event → WGWorld → Ambient → Prop)
    (postSafe : ∀ h w a, Post h w a → Safe h) :
    ∃ after generation, Step ledger after ∧
      ((∀ h, Active after debts generation r.pid peer history.length h → Safe h) →
      (∀ kp invalid, StatePrefixEnsures
        (Held after debts generation r.pid peer history.length) Safe (HeldSource.noKey r.pid peer kp invalid) (fun _ => Post)) →
      (∀ kid packets, StatePrefixEnsures
        (fun h w a => Held after debts generation r.pid peer history.length h w a ∧
          BatchPayload.Shape r.pid kid peer.staged packets) Safe (HeldSource.submit r.pid kid packets) (fun _ => Post)) →
      let out := runWGPrefix (Driver.stagingObserved hooks r.pid) r.run.before r.run.ambientBefore history
      ∃ suffix, out.2 = (history ++ [.stagingTaken r]) ++ suffix ∧ Safe out.2 ∧
        match out.1 with
        | .error _ => True
        | .ok ((_,w),a) => Post out.2 w a) := by
  obtain ⟨after,generation,step,held⟩ := taken r native chosen before justified links idle
  refine ⟨after,generation,step,?_⟩
  intro frontier rejected submitted
  exact SelectionCarrier.after_take r native chosen
    (Held after debts generation r.pid peer history.length) Safe
    (fun _ _ _ before => frontier _ before.active) held
    (borrow after debts generation r.pid peer history.length Safe frontier)
    (fun _ _ _ run before => selected_event before run) Post
    (fun keypair => checked after debts generation r.pid peer history.length keypair Safe frontier
      Post postSafe (HeldSource.noKey r.pid peer) (HeldSource.submit r.pid) rejected submitted)


end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.SoundHeld
