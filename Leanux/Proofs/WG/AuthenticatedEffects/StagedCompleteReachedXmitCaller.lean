import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedXmitFrames

/-! Concrete caller certificates for the direct transmit syscall. All worlds
are actual returned native prefix states. A stopped prefix retains its real
worldAt and failed run, without fabricating an exception endpoint. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Xmit
open Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Configuration TransmitSecurity CausalJournal CompleteProduct

def entryHistory (family addr : Nat) (packets : List Packet) (mtu : Nat) (history : List Event) : List Event :=
  history++[.scope (.entered ⟨history.length,.fixture (.transmit family addr packets mtu)⟩)]

structure Path (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts)
    (history : List Event) (w : World) (fd : Fd) (acquired : World)
    (packets : List Packet) (mtu : Nat) (worldAt : World) : Prop where
  acquisition : (liftFS (fdget SENDER_FD)).run w=.ok (fd,acquired)
  present : fd.file.isNone=false
  prepared : runPrefix (prepare family addr payload opts) acquired history=
    (.ok (.ready packets mtu,worldAt),history)

theorem Path.literal
    (path : Path family addr payload opts history w fd acquired packets mtu worldAt) :
    runPrefix (callPrefix family addr payload opts) w history=
      (.ok (.transmit fd packets mtu history.length,worldAt),entryHistory family addr packets mtu history) := by
  unfold callPrefix
  rw [runPrefix_bind,runPrefix_lift,path.acquisition]
  simp only [path.present,Bool.false_eq_true,ite_false]
  rw [runPrefix_bind,path.prepared]
  dsimp only
  rw [runPrefix_bind,entered_run]
  rfl

theorem Path.continuation
    (path : Path family addr payload opts history w fd acquired packets mtu worldAt) :
    runPrefix (Driver.syscallXmitObserved hooks family addr payload opts) w history=
      runPrefix (callTail family addr payload (.transmit fd packets mtu history.length)) worldAt
        (entryHistory family addr packets mtu history) := by
  rw [whole_factor,runPrefix_bind,path.literal]

theorem Path.entry
    (path : Path family addr payload opts history w fd acquired packets mtu worldAt)
    (before : Carrier history w) : Carrier (entryHistory family addr packets mtu history) worldAt := by
  have got : runPrefix (liftPrefix (liftFS (fdget SENDER_FD)) : PrefixM Event Fd) w history=
      (.ok (fd,acquired),history) := by rw [runPrefix_lift,path.acquisition]
  have obtained:=normal (fs (fdget SENDER_FD)) before got
  have prepared:=normal (prepare_checked family addr payload opts) obtained path.prepared
  exact normal (entered_checked family addr packets mtu) prepared (entered_run family addr packets mtu worldAt history)

theorem Path.accounted
    (path : Path family addr payload opts history w fd acquired packets mtu worldAt)
    (before : Carrier history w) :
    ∃ ledger, CompleteCarrier.Accounted (entryHistory family addr packets mtu history) ledger [] [] worldAt.wg :=
  (path.entry before).1

/-- An actual guarded failure after descriptor acquisition. The native
multicast/route/packet preparation has not emitted a fixture worldAt. -/
structure PreparationStopped (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts)
    (history : List Event) (w : World) (fd : Fd) (acquired : World) (stop : Stop) : Prop where
  acquisition : (liftFS (fdget SENDER_FD)).run w=.ok (fd,acquired)
  present : fd.file.isNone=false
  stopped : runPrefix (prepare family addr payload opts) acquired history=(.error stop,history)

theorem PreparationStopped.whole
    (path : PreparationStopped family addr payload opts history w fd acquired stop) :
    runPrefix (Driver.syscallXmitObserved hooks family addr payload opts) w history=(.error stop,history) := by
  rw [whole_factor,runPrefix_bind]
  unfold callPrefix
  rw [runPrefix_bind,runPrefix_lift,path.acquisition]
  simp only [path.present,Bool.false_eq_true,ite_false]
  rw [runPrefix_bind,path.stopped]

theorem PreparationStopped.entry
    (path : PreparationStopped family addr payload opts history w fd acquired stop)
    (before : Carrier history w) : Carrier history acquired := by
  apply normal (fs (fdget SENDER_FD)) before
  rw [runPrefix_lift,path.acquisition]

/-- Ordinary errno branches have a completed preparation world and still
owe the original fdput. Its Stop, if any, is retained by this continuation. -/
structure Refused (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts)
    (history : List Event) (w : World) (fd : Fd) (acquired worldAt : World) (error : Int) : Prop where
  acquisition : (liftFS (fdget SENDER_FD)).run w=.ok (fd,acquired)
  present : fd.file.isNone=false
  prepared : runPrefix (prepare family addr payload opts) acquired history=
      (.ok (.routeRefused error,worldAt),history) ∨
    runPrefix (prepare family addr payload opts) acquired history=
      (.ok (.packetsRefused error,worldAt),history)

theorem Refused.literal
    (path : Refused family addr payload opts history w fd acquired worldAt error) :
    runPrefix (callPrefix family addr payload opts) w history=(.ok (.refused fd error,worldAt),history) := by
  unfold callPrefix
  rw [runPrefix_bind,runPrefix_lift,path.acquisition]
  simp only [path.present,Bool.false_eq_true,ite_false]
  rw [runPrefix_bind]
  rcases path.prepared with route|packets
  · rw [route]; rfl
  · rw [packets]; rfl

theorem Refused.continuation
    (path : Refused family addr payload opts history w fd acquired worldAt error) :
    runPrefix (Driver.syscallXmitObserved hooks family addr payload opts) w history=
      runPrefix (callTail family addr payload (.refused fd error)) worldAt history := by
  rw [whole_factor,runPrefix_bind,path.literal]

theorem Refused.entry
    (path : Refused family addr payload opts history w fd acquired worldAt error)
    (before : Carrier history w) : Carrier history worldAt := by
  have obtained : Carrier history acquired := by
    apply normal (fs (fdget SENDER_FD)) before
    rw [runPrefix_lift,path.acquisition]
  rcases path.prepared with route|packets
  · exact normal (prepare_checked family addr payload opts) obtained route
  · exact normal (prepare_checked family addr payload opts) obtained packets

/-- Exhaustive source classification, requiring no success premise and no
incoming reachability assertion beyond the concrete caller carrier. -/
theorem caller_cases (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts)
    (history : List Event) (w : World) (before : Carrier history w) :
    (∃ stop, (liftFS (fdget SENDER_FD)).run w=.error stop ∧
      runPrefix (Driver.syscallXmitObserved hooks family addr payload opts) w history=(.error stop,history)) ∨
    (∃ fd v, (liftFS (fdget SENDER_FD)).run w=.ok (fd,v) ∧ fd.file.isNone=true ∧
      runPrefix (Driver.syscallXmitObserved hooks family addr payload opts) w history=(.ok (-EBADF,v),history) ∧
      Carrier history v) ∨
    (∃ fd acquired stop, PreparationStopped family addr payload opts history w fd acquired stop ∧
      Carrier history acquired) ∨
    (∃ fd acquired worldAt error, Refused family addr payload opts history w fd acquired worldAt error ∧
      Carrier history worldAt) ∨
    (∃ fd acquired packets mtu worldAt, Path family addr payload opts history w fd acquired packets mtu worldAt ∧
      Carrier (entryHistory family addr packets mtu history) worldAt) := by
  cases got : (liftFS (fdget SENDER_FD)).run w with
  | error stop=>
    refine Or.inl ⟨stop,rfl,?_⟩
    rw [whole_factor,runPrefix_bind]
    unfold callPrefix
    rw [runPrefix_bind,runPrefix_lift,got]
  | ok pair=>
    obtain ⟨fd,acquired⟩:=pair
    have kept : Carrier history acquired := by
      apply normal (fs (fdget SENDER_FD)) before
      rw [runPrefix_lift,got]
    cases present : fd.file.isNone with
    | true=>
      refine Or.inr (Or.inl ⟨fd,acquired,rfl,present,?_,kept⟩)
      rw [whole_factor,runPrefix_bind]
      unfold callPrefix
      rw [runPrefix_bind,runPrefix_lift,got]
      simp only [present,ite_true,runPrefix_pure,callTail]
    | false=>
      have unchanged:=prepare_history family addr payload opts acquired history
      cases run : runPrefix (prepare family addr payload opts) acquired history with
      | mk result last=>
        rw [run] at unchanged
        dsimp only at unchanged
        subst last
        cases result with
        | error stop=>exact Or.inr (Or.inr (Or.inl ⟨fd,acquired,stop,⟨got,present,run⟩,kept⟩))
        | ok pair=>
          obtain ⟨prepared,worldAt⟩:=pair
          cases prepared with
          | routeRefused err=>
            have path : Refused family addr payload opts history w fd acquired worldAt err:=⟨got,present,Or.inl run⟩
            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨fd,acquired,worldAt,err,path,path.entry before⟩)))
          | packetsRefused err=>
            have path : Refused family addr payload opts history w fd acquired worldAt err:=⟨got,present,Or.inr run⟩
            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨fd,acquired,worldAt,err,path,path.entry before⟩)))
          | ready packets mtu=>
            have path : Path family addr payload opts history w fd acquired packets mtu worldAt:=⟨got,present,run⟩
            exact Or.inr (Or.inr (Or.inr (Or.inr ⟨fd,acquired,packets,mtu,worldAt,path,path.entry before⟩)))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Xmit
