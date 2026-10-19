import Leanux.Proofs.WG.Config.UpdateOnlySource
import Leanux.Proofs.WG.Config.QueuedRemoveSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.UpdateOnly
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Leanux.Proofs.WG.Config.OwnerConfiguration

/-- For an actual funded existing target, setting UPDATE_ONLY preserves the
entire original outcome, including errors and decision logs. Both requests
supply an explicit flags attribute; an absent flags attribute logs differently. -/
theorem original_existing (cs : Ledger) (loans : Reservations)
    (attrs : PeerAttrs) (key : Key) (flags : UInt32) (pid : PeerId) (d : Device)
    (pubkey : attrs.publicKey=some key)
    (valid : flags &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (found : d.peerHashtable.find? (·.1 == key)=some (key,pid)) :
    Campaign2.AgreesOn (fun s=>ProjectedEntry cs loans s ∧ s.wg.device=some d)
      (setPeerCmd {attrs with flags:=some (flags ||| WGPEER_F_UPDATE_ONLY)})
      (setPeerCmd {attrs with flags:=some flags}) := by
  intro g a pre
  obtain ⟨p,resident,positive⟩ := QueuedRemove.lookup_target cs loans key pid d g
    ((entry_snapshot cs loans g a).mp pre.1) pre.2 found
  exact congrArg Campaign2.observeResult
    (existing_run attrs key flags pid d p pubkey valid protocol found resident positive g a pre.2)

/-- A valid UPDATE_ONLY request with no table match returns zero without changing
WG state. Later attributes are arbitrary; the normal decision log is retained. -/
theorem original_absent (attrs : PeerAttrs) (key : Key) (flags : UInt32)
    (initial : Campaign2.State) (d : Device)
    (device : initial.device=some d)
    (pubkey : attrs.publicKey=some key) (valid : flags &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (missing : d.peerHashtable.find? (·.1 == key)=none) :
    Campaign2.Returns
      (setPeerCmd {attrs with flags:=some (flags ||| WGPEER_F_UPDATE_ONLY)})
      (fun s=>s.wg=initial) (fun ret s=>ret=0 ∧ s.wg=initial) := by
  intro g a pre
  have current : g.dev=some d := (congrArg (fun s : Campaign2.State => s.device) pre).trans device
  obtain ⟨b,run⟩ := absent_run attrs key flags d pubkey valid protocol missing g a current
  exact ⟨0,g,b,run,rfl,pre⟩

/-- Header validation follows public-key, flag, then protocol priority. Its
refusal returns before lookup and preserves WG state, with the actual decisions. -/
theorem original_validation (attrs : PeerAttrs) (code : Int)
    (refused : validationError attrs=some code) (initial : Campaign2.State) :
    Campaign2.Returns (setPeerCmd attrs) (fun s=>s.wg=initial)
      (fun ret s=>ret=code ∧ s.wg=initial) := by
  intro g a pre
  obtain ⟨b,run⟩ := validation_run attrs code refused g a
  exact ⟨code,g,b,run,rfl,pre⟩

end Leanux.Proofs.WG.Config.UpdateOnly
