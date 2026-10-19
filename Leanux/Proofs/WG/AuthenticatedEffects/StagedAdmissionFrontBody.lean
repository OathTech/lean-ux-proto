import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionFrontSelection
import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionNative

/-! The actual front composes native checks, lookup, enriched selection and
splice. A successful result carries its own splice-entry checkpoint; no
intermediate-state or connected-cut equation is a caller hypothesis. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal
set_option pp.structureInstances false

abbrev body (family addr : Nat) (packets : List Packet) (mtu : Nat) :=
  HandshakeSecurity.StagedConservation.Front.frontWith ops family addr packets mtu

def Selected (entry : Entry) (peer : Option PeerId) (packets : List Packet) (mtu : Nat)
    (result : Except Int (PeerId × List Packet)) (h : List Event) (w : WGWorld) (a : Ambient) : Prop :=
  Carry entry h w a ∧ Packets.TxSelected peer packets mtu result

theorem select_data (family : Nat) (packets : List Packet) (mtu : Nat) (peer : Option PeerId) :
    StatePrefixEnsures (Idle entry) (Safe entry)
      (HandshakeSecurity.StagedConservation.Front.selectWith ops family packets mtu peer)
      (Selected entry peer packets mtu) := by
  intro w a h before
  obtain ⟨suffix,history,safe,normal⟩ := select_checked family packets mtu peer w a h before
  refine ⟨suffix,history,safe,?_⟩
  cases run : runWGPrefix
      (HandshakeSecurity.StagedConservation.Front.selectWith ops family packets mtu peer) w a h with
  | mk result hist =>
    change runPrefix
      ((HandshakeSecurity.StagedConservation.Front.selectWith ops family packets mtu peer).run w) a h = _ at run
    rw [run] at normal ⊢
    cases result with
    | error stop => trivial
    | ok out =>
      rcases out with ⟨⟨selected,v⟩,b⟩
      have erased := HandshakeSecurity.StagedConservation.Front.select_erases
        (HandshakeSecurity.StagedConservation.Front.observedOps_erases Event.stagedDisposal stagedDisposal?)
        family packets mtu peer w a h
      rw [run] at erased
      have data := (hoare_iff_run_ambient _ _ _).mp (Packets.txSelect_spec family packets mtu peer)
        w a selected v b True.intro erased.symm
      exact ⟨normal,data⟩

def Spliced (entry : Entry) (pid : PeerId) (packets : List Packet)
    (h : List Event) (v : WGWorld) (b : Ambient) : Prop :=
  ∃ w a, Carry entry h w a ∧
    ((Lifetimes.xmitSplice pid packets).run w).run a = .ok (((),v),b)

theorem Spliced.safe (before : Spliced entry pid packets h v b) : Safe entry h := by
  obtain ⟨w,a,carry,_⟩ := before
  exact carry.safe

def BodyPost (entry : Entry) (packets : List Packet) (mtu : Nat)
    (result : Except Int PeerId) (h : List Event) (w : WGWorld) (a : Ambient) : Prop :=
  match result with
  | .error _ => Carry entry h w a
  | .ok pid => Spliced entry pid (packets.map (fun p => {p with mtu})) h w a

theorem body_checked (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StatePrefixEnsures (Idle entry) (Safe entry) (body family addr packets mtu)
      (BodyPost entry packets mtu) := by
  unfold body HandshakeSecurity.StagedConservation.Front.frontWith
  apply StatePrefixEnsures.bind (idle_native (fun _ _ => Native.check family addr packets mtu))
  intro accepted
  split
  · exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.carry.safe) (fun _ _ _ hi => hi.carry)
  · apply StatePrefixEnsures.bind (idle_native (fun _ _ => Native.lookup family addr))
    intro peer
    apply StatePrefixEnsures.bind (select_data family packets mtu peer)
    intro result
    cases result with
    | error err =>
      exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1.safe) (fun _ _ _ hi => hi.1)
    | ok pair =>
      rcases pair with ⟨pid,selected⟩
      have splice : StatePrefixEnsures (Selected entry peer packets mtu (.ok (pid,selected)))
          (Safe entry) (ops.splice pid selected)
          (fun _ => Spliced entry pid (packets.map (fun p => {p with mtu}))) := by
        apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1.safe)
        intro h w a value v b before run
        refine ⟨w,a,before.1,?_⟩
        have equal : selected = packets.map (fun p => {p with mtu}) := before.2.2
        rw [←equal]
        cases value
        exact run
      exact StatePrefixEnsures.bind splice (fun _ =>
        StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.safe) (fun _ _ _ hi => hi))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front
