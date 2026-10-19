import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAllocationReceipt
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteStaging

/-! Fixed source factors up to the actual staging callback. The decision
prefix runs exactly the original guards and ordered nonce loop. It neither
allocates nor runs a rejection callback; the original callback follows at
the cut chosen by those guards, including the explicit unreachable arm. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Obligations CausalJournal

inductive Decision where
  | rejected (keypair : Option KeypairId) (invalid : Bool)
  | submit (kid : KeypairId) (packets : List DataPacket)
  | unreachable

def finishWith [Monad m] (step : {α : Type}→WG.M α→m α)
    (noKey : Option KeypairId→Bool→m Unit) (submit : KeypairId→List DataPacket→m Unit) :
    Decision→m Unit
  | .rejected kp invalid=>noKey kp invalid
  | .submit kid packets=>submit kid packets
  | .unreachable=>step (invariant "unreachable")

def walkWith [Monad m] (step : {α : Type}→WG.M α→m α)
    (reserve : KeypairId→m Nat) (pid : PeerId) (kid : KeypairId) :
    List Packet→List DataPacket→m Decision
  | [],packets=>do
    _←step (branch .stagedNonceIterate false)
    pure (.submit kid packets)
  | packet::rest,packets=>do
    _←step (branch .stagedNonceIterate true)
    let ds←step (ipTunnelEcnEncap packet)
    let nonce←reserve kid
    if ←step (branchCmp .stagedNonceRejected (nonce≥REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES) then
      pure (.rejected (some kid) true)
    else walkWith step reserve pid kid rest (packets++[{peer:=pid,keypair:=kid,nonce,plaintext:=packet,ds}])

def prefixWith [Monad m] (step : {α : Type}→WG.M α→m α)
    (reserve : KeypairId→m Nat) (pid : PeerId) (peer : Peer) (keypair : Option KeypairId) : m Decision := do
  if ←step (branch .stagedNoKeypair keypair.isNone) then
    return .rejected keypair false
  let some kid:=keypair | pure .unreachable
  let key←step (getKeypair kid)
  if ←step (branch .stagedKeyInvalid !key.sending.isValid) then
    return .rejected keypair false
  if ←step (branchExpired .stagedBirthdateExpired key.sending.birthdate REJECT_AFTER_TIME) then
    return .rejected keypair true
  walkWith step reserve pid kid peer.staged []

def nonceWith [Monad m] (step : {α : Type}→WG.M α→m α)
    (reserve : KeypairId→m Nat) (noKey : Option KeypairId→Bool→m Unit)
    (submit : KeypairId→List DataPacket→m Unit) (pid : PeerId) (kid : KeypairId)
    (remaining : List Packet) (packets : List DataPacket) : m Unit := do
  let mut packetsCb:=packets
  for packet in remaining do
    _←step (branch .stagedNonceIterate true)
    let ds←step (ipTunnelEcnEncap packet)
    let nonce←reserve kid
    if ←step (branchCmp .stagedNonceRejected (nonce≥REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES) then
      return ←noKey (some kid) true
    packetsCb:=packetsCb++[{peer:=pid,keypair:=kid,nonce,plaintext:=packet,ds}]
  _←step (branch .stagedNonceIterate false)
  submit kid packetsCb

theorem nonce_factor [Monad m] [LawfulMonad m] (step : {α : Type}→WG.M α→m α)
    (reserve : KeypairId→m Nat) (noKey : Option KeypairId→Bool→m Unit)
    (submit : KeypairId→List DataPacket→m Unit) (pid : PeerId) (kid : KeypairId)
    (remaining : List Packet) (packets : List DataPacket) :
    nonceWith step reserve noKey submit pid kid remaining packets=
      (walkWith step reserve pid kid remaining packets >>= finishWith step noKey submit) := by
  induction remaining generalizing packets with
  | nil=>simp only [nonceWith,walkWith,List.forIn_nil,pure_bind,bind_assoc,finishWith]
  | cons packet rest ih=>
    simp only [nonceWith,walkWith,List.forIn_cons,bind_assoc]
    congr 1
    funext iterate
    congr 1
    funext ds
    congr 1
    funext nonce
    congr 1
    funext over
    cases over <;> simp only [Bool.false_eq_true,ite_false,ite_true,pure_bind,bind_assoc,finishWith]
    · exact ih _
    · exact bind_pure _

theorem checked_factor [Monad m] [LawfulMonad m] (step : {α : Type}→WG.M α→m α)
    (reserve : KeypairId→m Nat) (noKey : Option KeypairId→Bool→m Unit)
    (submit : KeypairId→List DataPacket→m Unit) (pid : PeerId) (peer : Peer)
    (keypair : Option KeypairId) :
    RestoreEntry.checkedWith step reserve noKey submit pid peer keypair=
      (prefixWith step reserve pid peer keypair >>= finishWith step noKey submit) := by
  unfold RestoreEntry.checkedWith prefixWith
  simp only [bind_assoc]
  congr 1
  funext missing
  cases missing <;> simp only [Bool.false_eq_true,ite_false,ite_true,pure_bind,finishWith]
  cases keypair with
  | none=>simp only [pure_bind,finishWith]
  | some kid=>
    dsimp only
    simp only [bind_assoc]
    congr 1
    funext key
    congr 1
    funext invalid
    cases invalid <;> simp only [Bool.false_eq_true,ite_false,ite_true,pure_bind,finishWith]
    simp only [bind_assoc]
    congr 1
    funext expired
    cases expired <;> simp only [Bool.false_eq_true,ite_false,ite_true,pure_bind,finishWith]
    exact nonce_factor step reserve noKey submit pid kid peer.staged []

def checkedPrefix (pid : PeerId) (peer : Peer) (keypair : Option KeypairId) : WGPrefix Event Decision :=
  prefixWith liftWGPrefix (fun kid=>state (Journal.reserve kid)) pid peer keypair

def finish (pid : PeerId) (peer : Peer) : Decision→WGPrefix Event Unit :=
  finishWith liftWGPrefix (HeldSource.noKey pid peer) (HeldSource.submit pid)

/-- The only additional native calls before allocation are the original
key owner read and strict peer acquisition. Their order remains literal. -/
def allocationPrefix (pid : PeerId) (peer : Peer) (keypair : Option KeypairId) : WGPrefix Event Decision := do
  let decision←checkedPrefix pid peer keypair
  match decision with
  | .submit kid packets=>
    let owner←liftWGPrefix (IndexOwner.peerDeref (.keypair kid))
    liftWGPrefix (peerGet owner)
    pure (.submit kid packets)
  | other=>pure other

def allocationTail (pid : PeerId) (peer : Peer) : Decision→WGPrefix Event Unit
  | .submit _ packets=>do
    let items←state (Journal.allocate packets)
    CausalJournal.create pid items
  | .rejected kp invalid=>HeldSource.noKey pid peer kp invalid
  | .unreachable=>liftWGPrefix (invariant "unreachable")

theorem submit_factor (pid : PeerId) (peer : Peer) (keypair : Option KeypairId) :
    (checkedPrefix pid peer keypair >>= finish pid peer)=
      (allocationPrefix pid peer keypair >>= allocationTail pid peer) := by
  simp only [allocationPrefix,bind_assoc]
  congr 1
  funext decision
  cases decision <;> simp only [finish,finishWith,allocationTail,HeldSource.submit,bind_assoc,pure_bind]

theorem staging_factor (pid : PeerId) : Driver.stagingObserved hooks pid=(do
    let chosen←CausalJournal.selection pid
    match chosen with
    | none=>pure ()
    | some (peer,keypair)=>checkedPrefix pid peer keypair >>= finish pid peer) := by
  rw [HeldSource.staging_factor]
  congr 1
  funext chosen
  cases chosen with
  | none=>rfl
  | some pair=>exact checked_factor _ _ _ _ _ _ _

theorem allocation_factor (pid : PeerId) : Driver.stagingObserved hooks pid=(do
    let chosen←CausalJournal.selection pid
    match chosen with
    | none=>pure ()
    | some (peer,keypair)=>allocationPrefix pid peer keypair >>= allocationTail pid peer) := by
  rw [staging_factor]
  congr 1
  funext chosen
  cases chosen with
  | none=>rfl
  | some pair=>exact submit_factor _ _ _

/-- This literal prefix starts at the staging caller, before take. -/
def stagingPrefix (pid : PeerId) : WGPrefix Event (Option (Peer×Decision)) := do
  let chosen←CausalJournal.selection pid
  match chosen with
  | none=>pure none
  | some (peer,keypair)=>do
    let decision←allocationPrefix pid peer keypair
    pure (some (peer,decision))

def stagingTail (pid : PeerId) : Option (Peer×Decision)→WGPrefix Event Unit
  | none=>pure ()
  | some (peer,decision)=>allocationTail pid peer decision

theorem whole_factor (pid : PeerId) :
    Driver.stagingObserved hooks pid=(stagingPrefix pid >>= stagingTail pid) := by
  rw [allocation_factor]
  simp only [stagingPrefix,bind_assoc]
  congr 1
  funext chosen
  cases chosen with
  | none=>simp only [pure_bind,stagingTail]
  | some pair=>simp only [bind_assoc,pure_bind,stagingTail]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging
