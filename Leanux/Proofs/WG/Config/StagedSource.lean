import Leanux.Proofs.WG.Config.QueuedHandshake

set_option pp.structureInstances false
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def stagedFallback (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) : WG.M Unit := do
  if invalid then
    let some id := keypair | invariant "unreachable"
    let k ← getKeypair id
    setKeypair id { k with sending := { k.sending with isValid := false } }
  keypairPut keypair false
  for _ in packets do _ ← branch .stagedOrphanWalk true   -- skb_orphan
  _ ← branch .stagedOrphanWalk false
  -- skb_queue_splice: the packets go back at the head of the staged queue
  setPeer pid { (← getPeer pid) with staged := packets ++ (← getPeer pid).staged }
  sendQueuedHandshakeInitiation pid false

def stagedAfterGet (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId) : WG.M Unit := do
  if ← branch .stagedNoKeypair keypair.isNone then return ← stagedFallback pid packets keypair false
  let some id := keypair | invariant "unreachable"
  let k ← getKeypair id
  if ← branch .stagedKeyInvalid !k.sending.isValid then return ← stagedFallback pid packets keypair false
  if ← branchExpired .stagedBirthdateExpired k.sending.birthdate REJECT_AFTER_TIME then
    return ← stagedFallback pid packets keypair true
  -- the nonces and `ds`, in queue order
  let mut packetsCb : List DataPacket := []
  for pkt in packets do
    _ ← branch .stagedNonceIterate true
    -- `PACKET_CB(skb)->ds = ip_tunnel_ecn_encap(0, ip_hdr(skb), skb)`
    let ds ← ipTunnelEcnEncap pkt
    let k ← getKeypair id
    let nonce := k.sendingCounter   -- atomic64_inc_return(&sending_counter) - 1
    setKeypair id { k with sendingCounter := k.sendingCounter + 1 }
    -- `nonce >= REJECT_AFTER_MESSAGES`, a u64 compare against the constant
    -- (the built code tests `> R - 1`; the check's `ge` shift absorbs it)
    if ← branchCmp .stagedNonceRejected (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES then return ← stagedFallback pid packets keypair true
    packetsCb := packetsCb ++ [{ peer := pid, keypair := id, nonce, plaintext := pkt, ds }]
  _ ← branch .stagedNonceIterate false
  -- `packets.prev->next = NULL`; wg_peer_get(keypair->entry.peer);
  -- PACKET_CB(packets.next)->keypair = keypair: the skbs enter the store
  -- (review 4.2) as the list `wg_packet_create_data` takes
  peerGet (← IndexOwner.peerDeref (.keypair id))
  let item ← packetsCb.mapM newTxSkb
  createData pid item

def stagedSource (pid : PeerId) : WG.M Unit := do
  let p ← getPeer pid
  if ← branch .stagedEmpty p.staged.isEmpty then return
  let packets := p.staged
  setPeer pid { p with staged := [] }
  let keypair ← keypairGet p.keypairCurrent
  stagedAfterGet pid packets keypair

theorem sendStaged_source (pid : PeerId) : stagedSource pid = sendStagedPackets pid := by
  simp [stagedSource, stagedAfterGet, stagedFallback, sendStagedPackets]
  rfl

end Leanux.Proofs.WG.Config
