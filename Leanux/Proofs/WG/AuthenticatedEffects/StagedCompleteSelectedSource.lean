import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSelectedFrames

/-! Borrowing and nonce traversal retain the paired selected carrier, using
the existing generic proof of the original source choices. Consuming callbacks
receive that same carrier; their terminal effects remain separate obligations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSelected
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open AllocatedObligation CausalJournal StagedTerminalComplete CompleteCarrier
open HandshakeSecurity.StagedConservation

theorem borrow (ledger : Ledger) (debts : List CleanupDebt) (locals : List RetirementSecurity.TxLocalBatch)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat) (Safe : List Event → Prop)
    (frontier : ∀ h, Active ledger debts generation pid peer position h → Safe h) :
    StatePrefixEnsures (Ready ledger debts locals generation pid peer position) Safe
      (liftWGPrefix (Take.borrow (some peer)))
      (fun selected h w a => ∃ keypair, selected = some (peer,keypair) ∧
        Ready ledger debts locals generation pid peer position h w a) := by
  intro w a h before
  obtain ⟨suffix,extended,active,post⟩ := ReadyCarrier.borrow ledger debts locals generation pid peer position
    (SoundHeld.Active ledger debts generation pid peer position) (fun _ => id) w a h before.toReady
  obtain ⟨_,_,complete,_⟩ := Driver.History.state_lift (Safe := fun h => Complete h ledger)
    (Take.borrow (some peer)) w a h before.complete
  have anchor : NativeAnchor position (runPrefix ((liftWGPrefix (Take.borrow (some peer))).run w) a h).2 := by
    rw [extended]
    exact before.nativeAnchor.append suffix
  refine ⟨suffix,extended,frontier _ ⟨active,complete,anchor⟩,?_⟩
  cases result : (runPrefix ((liftWGPrefix (Take.borrow (some peer))).run w) a h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    rw [result] at post
    obtain ⟨keypair,chosen,ready⟩ := post
    exact ⟨keypair,chosen,ready,complete,anchor⟩

theorem selected_event (before : Ready ledger debts locals generation pid peer position h w a)
    (run : WGRunWitness (Option (Peer × Option KeypairId))) :
    Ready ledger debts locals generation pid peer position
      (h ++ [Event.old (.responder (.selected pid run))]) w a :=
  ⟨ReadyCarrier.selected_event before.toReady run,before.complete.append_quiet
    (fun _ member => by cases List.mem_singleton.mp member; intro pos; rfl),before.nativeAnchor.append _⟩

theorem checked (ledger : Ledger) (debts : List CleanupDebt) (locals : List RetirementSecurity.TxLocalBatch)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat) (keypair : Option KeypairId)
    (Safe : List Event → Prop)
    (frontier : ∀ h, Active ledger debts generation pid peer position h → Safe h)
    (Post : List Event → WGWorld → Ambient → Prop) (postSafe : ∀ h w a, Post h w a → Safe h)
    (noKey : Option KeypairId → Bool → WGPrefix Event Unit)
    (submit : KeypairId → List DataPacket → WGPrefix Event Unit)
    (rejected : ∀ kp invalid, StatePrefixEnsures (Ready ledger debts locals generation pid peer position) Safe
      (noKey kp invalid) (fun _ => Post))
    (submitted : ∀ kid packets, StatePrefixEnsures
      (fun h w a => Ready ledger debts locals generation pid peer position h w a ∧
        BatchPayload.Shape pid kid peer.staged packets) Safe (submit kid packets) (fun _ => Post)) :
    StatePrefixEnsures (Ready ledger debts locals generation pid peer position) Safe
      (RestoreEntry.checkedWith liftWGPrefix (fun kid => state (Journal.reserve kid)) noKey submit pid peer keypair)
      (fun _ => Post) :=
  CheckedCarrier.checked (Ready ledger debts locals generation pid peer position) pid peer keypair Safe
    (fun _ _ _ before => frontier _ before.active)
    (ambient frontier) (world frontier) (read_key frontier) (reserve frontier)
    Post postSafe noKey submit rejected submitted

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSelected
