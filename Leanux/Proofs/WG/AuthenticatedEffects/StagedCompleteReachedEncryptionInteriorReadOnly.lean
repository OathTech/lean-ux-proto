import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionPacketEntry

/-! The original preparation and AEAD key-read sites contain no WG mutation.
Each listed primitive preserves the full WG projection on its own successful
run. A failure has no returned world; the statements do not manufacture one. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity

inductive Primitive : Type → Type 1 where
  | ambient (action : AmbientM α) : Primitive α
  | padding (len mtu : Nat) : Primitive Nat
  | checksum (packet : Packet) : Primitive Packet
  | key (slot : KeypairId) : Primitive Keypair
  | txRead (skb : SkbId) : Primitive DataPacket

def Primitive.native : Primitive α → Leanux.M α
  | .ambient action => monadLift action
  | .padding len mtu => liftWG (calculateSkbPadding len mtu)
  | .checksum packet => Env.checksumHelp packet
  | .key slot => liftWG (getKeypair slot)
  | .txRead skb => liftWG (getTxSkb skb)

theorem Primitive.frame (action : Primitive α) : SameView (fun w : World => w.wg) action.native := by
  cases action with
  | ambient action =>
    intro initial
    exact productAmbient_spec action (fun w : World => w.wg = initial) (fun _ _ same => same)
  | padding len mtu =>
    exact sameView_liftWG (fun w : World => w.wg) id _ (calculateSkbPadding_sameWGWorld len mtu)
      (fun _ _ _ same => same)
  | checksum packet => exact (checksumHelp_sameWorld packet).factor (fun w => w.wg)
  | key slot =>
    apply sameView_liftWG (fun w : World => w.wg) id _ _ (fun _ _ _ same => same)
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a key v b run
    exact (Keypairs.getKeypair_current slot w v a b key run).1
  | txRead skb =>
    apply sameView_liftWG (fun w : World => w.wg) id _ _ (fun _ _ _ same => same)
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a packet v b run
    exact (Packets.getTxSkb_current skb w v packet a b run).1

inductive Site where
  | hash | padding | cowHead | cowHeadGuard | checksumGuard | checksumAllocation
  | checksumAllocationGuard | checksum | cowData | cowDataGuard | fragments | key | scatter

def prepareWith [Monad m] (step : {α : Type} → Site → Primitive α → m α) (packet : DataPacket) :
    m (Option Encryption.Prepared) := do
  step .hash (.ambient (skipCut [.flowHashSecret]))
  let padding ← step .padding (.padding packet.plaintext.bytes.length packet.plaintext.mtu)
  if ← step .cowHeadGuard (.ambient (branch .encCowHeadFailed !(← step .cowHead (.ambient (hiddenAlloc .skbCowHead))))) then
    return none
  let mut inner := packet.plaintext
  if ← step .checksumGuard (.ambient (branch .encChecksumPartial inner.csum.isSome)) then
    if ← step .checksumAllocationGuard (.ambient (branch .encChecksumHelpFailed
        !(← step .checksumAllocation (.ambient (hiddenAlloc .skbChecksumHelp))))) then return none
    inner ← step .checksum (.checksum inner)
  let cowOk ← step .cowData (.ambient (hiddenAlloc .skbCowDataTx))
  if ← step .cowDataGuard (.ambient (branch .encCowDataFailed !cowOk)) then return none
  if ← step .fragments (.ambient (branch .encTooManyFrags false)) then return none
  pure (some ⟨inner,padding⟩)

def finishWith [Monad m] (step : {α : Type} → Site → Primitive α → m α)
    (slot : KeypairId) (packet : DataPacket) (prepared : Option Encryption.Prepared) : m (Option (List UInt8)) := do
  let some value := prepared | return none
  let key ← step .key (.key slot)
  if ← step .scatter (.ambient (branch .encSgvecFailed false)) then return none
  pure (some (dataMessage key.remoteIndex packet.nonce key.sending.key
    (value.inner.bytes ++ List.replicate value.padding 0)))

theorem prepare_native (packet : DataPacket) :
    prepareWith (fun _ action => action.native) packet = Encryption.prepare Env.checksumHelp packet := rfl

theorem finish_native (slot : KeypairId) (packet : DataPacket) (prepared : Option Encryption.Prepared) :
    finishWith (fun _ action => action.native) slot packet prepared = Encryption.finish slot packet prepared := rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionInterior
