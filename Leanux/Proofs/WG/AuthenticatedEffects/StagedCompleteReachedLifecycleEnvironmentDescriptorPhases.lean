import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecycleEnvironmentDescriptorCanonical

/-! Concrete native descriptor prefixes preserve exactly the caller's input.
After the lifecycle callback returns, only its actual packet account is needed
for fd repayments. No native reset is treated as a terminal disposition. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Environment.Descriptor
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity Driver Points
set_option maxHeartbeats 600000

theorem socket_result_framing (stable : Stable P) (f : Fd) (body : Shape action)
    (bodyFramed : Framing P body) (missing : Bool) : Framing P (socketResultShape f body missing) := by
  cases missing with
  | true => exact pure_framing stable _
  | false =>
    apply body_bind _ bodyFramed
    intro ret
    exact atom_bind stable_account _ _ (fun _=>pure_framing stable_account ret)

theorem socket_framing (stable : Stable P) (fd : Nat) (body : Shape action)
    (bodyFramed : Framing P body) : Framing P (socketShape fd body) :=
  atom_bind stable _ _ (fun f=>socket_result_framing stable f body bodyFramed _)

theorem callback_framing (stable : Stable P) (body : Shape action)
    (bodyFramed : Framing P body) : Framing P (requestCallbackShape body) := by
  apply atom_bind stable
  intro _
  apply body_bind _ bodyFramed
  intro ret
  exact atom_bind stable_account _ _ (fun _=>pure_framing stable_account ret)

theorem finish_framing (fd fid : Nat) (ret : Int) : Framing Account (requestFinishShape fd fid ret) := by
  apply body_bind _ (socket_framing stable_account fd (.pure 0) (pure_framing stable_account 0))
  intro _
  apply atom_bind stable_account
  intro _
  apply atom_bind stable_account
  intro _
  apply atom_bind stable_account
  intro _
  exact atom_bind stable_account _ _ (fun _=>pure_framing stable_account ret)

theorem install_framing (stable : Stable P) (fd fid : Nat) (body : Shape action)
    (bodyFramed : Framing P body) : Framing P (requestInstallShape fd fid body) := by
  apply atom_bind stable
  intro _
  apply atom_bind stable
  intro _
  apply atom_bind stable
  intro _
  apply atom_bind stable
  intro _
  apply atom_bind stable
  intro _
  exact body_bind _ (socket_framing stable fd _ (callback_framing stable body bodyFramed))
    (finish_framing fd fid)

theorem limit_framing (stable : Stable P) (exceeded : Bool) : Framing P (limitShape exceeded) := by
  cases exceeded with
  | true => exact atom_framing stable (Atom.ambient (AmbientM.unsupported _))
  | false => exact pure_framing stable ()

theorem limit_normal (stable : Stable P) (exceeded : Bool) (before : P h w)
    (performed : runPrefix (limit exceeded) w h=(.ok (value,v),last)) : P last v := by
  cases exceeded with
  | true => exact stable.normal (Atom.ambient (AmbientM.unsupported _)) before performed
  | false => cases performed; exact before

theorem chosen_framing (stable : Stable P) (fd : Nat) (body : Shape action)
    (bodyFramed : Framing P body) : Framing P (requestChosenShape fd body) := by
  apply atom_bind stable
  intro task h w before
  refine ⟨limit_framing stable _ h w before,?_⟩
  intro value v last performed
  have after : P last v := limit_normal stable _ before performed
  have next : Framing P (.bind Atom.read.shape (fun saved=>requestInstallShape fd saved.fs.nextFile body)) :=
    atom_bind stable Atom.read (fun saved=>requestInstallShape fd saved.fs.nextFile body)
      (fun saved=>install_framing stable fd saved.fs.nextFile body bodyFramed)
  exact next last v after

theorem choice_framing (stable : Stable P) (body : Shape action)
    (bodyFramed : Framing P body) (choice : Option Nat) : Framing P (requestChoiceShape body choice) := by
  cases choice with
  | none => exact atom_framing stable (Atom.ambient (AmbientM.unsupported _))
  | some fd => exact chosen_framing stable fd body bodyFramed

theorem request_framing (stable : Stable P) (body : Shape action)
    (bodyFramed : Framing P body) : Framing P (requestShape body) :=
  atom_bind stable _ _ (fun _=>choice_framing stable body bodyFramed _)

theorem original_socket_framing (stable : Stable P) (fd : Nat) (body : Shape action)
    (bodyFramed : Framing P body) : Framing P (originalSocket fd body) :=
  fun h w before=>Framed.source_mpr (socket_source fd action) (socket_framing stable fd body bodyFramed h w before)

theorem original_request_framing (stable : Stable P) (body : Shape action)
    (bodyFramed : Framing P body) : Framing P (originalRequest body) :=
  fun h w before=>Framed.source_mpr (request_source action) (request_framing stable body bodyFramed h w before)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Environment.Descriptor
