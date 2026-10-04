import Leanux.Runner

/-!
# The data send path on a constructed state (D1 stream C)

Not part of the model build. Run with

    scripts/in-bundle lake env lean Leanux/Tests/DataPath.lean

A peer with a current keypair and the keepalive staged at `wg_up` (as the
initiator has after consuming a response) sends the keepalive: the staged
packets get a nonce, `wg_packet_create_data` queues it, and the environment
runs the encrypt and tx workers, whose datagram reaches the fixture's sender.
Clock reads are placeholders (`hiddenPlaceholders`), which advance from
1000 s. The bytes are `dataMessage`'s, whose vectors Data.lean pins against
harness/noise.py.
-/

namespace Leanux.Tests
open Leanux Leanux.WG

def key : List UInt8 := (List.range 32).map UInt8.ofNat

def world (birthdate : Int) (env : EnvSite → Nat → Bool := fun _ _ => true) : World :=
  let peer : Peer := { remoteStatic := List.replicate 32 9, presharedKey := List.replicate 32 0,
                       precomputedStaticStatic := List.replicate 32 0, internalId := 1,
                       endpoint := some { family := AF_INET, addr := 0x7f000001, port := Env.SENDER_PORT },
                       persistentKeepaliveInterval := 25, staged := [0], keypairCurrent := some 0 }
  let kp : Keypair := { sending := { key, birthdate, isValid := true }, iAmTheInitiator := true,
                        remoteIndex := 0x04030201, peer := 0 }
  let k := Runner.initialKernel 1024 true
  let dev := (k.wg.getD { ifindex := 3, ifname := "wg0" })
  let dev := { dev with running := true, incomingPort := 51820, peerList := [0], numPeers := 1, nextPeer := 1,
                        peers := Std.TreeMap.ofList [(0, peer)], keypairs := Std.TreeMap.ofList [(0, kp)],
                        nextKeypairId := 1 }
  { k := { k with wg := some dev }, env, timing := Env.timing, hiddenPlaceholders := true }

/-- The keepalive sent from the handshake receive worker, then the crypt
    workers: the world afterwards and the decisions taken. -/
def run (w : World) : Except Stop World := do
  let ((), w) ← (do WG.sendKeepalive 0; Env.runCryptWorkers).run w
  return w

def labels (w : World) : List String := w.steps.toList.map Step.label

def dev (w : World) : Device := w.k.wg.getD { ifindex := 0, ifname := "" }
def peer (w : World) (f : Peer → α) : Option α := ((dev w).peers.get? 0).map f
def kp (w : World) (f : Keypair → α) : Option α := ((dev w).keypairs.get? 0).map f

-- The keepalive reaches the fixture's sender with the expected bytes, and
-- every reference taken is dropped.
#guard match run (world 1000000000000) with
  | .ok w =>
    w.senderInbox == [dataMessage 0x04030201 0 key []]
    && (dev w).encryptQueue.isEmpty && (dev w).txWorkQueue.isEmpty
    && peer w (·.txQueue.isEmpty) == some true
    && peer w (·.staged.isEmpty) == some true
    && peer w (·.refcount) == some 1
    && peer w (·.serialWorkCpu) == some (some 0)
    && peer w (·.txBytes) == some 32
    && kp w (·.refcount) == some 1
    && kp w (·.sendingCounter) == some 1
    && (dev w).encryptLastCpu == 0
  | .error _ => false

-- The C's decisions, in order: wg_packet_send_staged_packets and
-- wg_packet_create_data (in the receive worker), the encrypt worker, the tx
-- worker.
#guard match run (world 1000000000000) with
  | .ok w => labels w == [
      "wg_packet_send_keepalive.staged_empty=0",
      "wg_packet_send_staged_packets.empty=0",
      "wg_noise_keypair_get.null=0",
      "__refcount_add_not_zero.old_zero=0",
      "__refcount_add_not_zero.cmpxchg_failed=0",
      "__refcount_add_not_zero.old_negative=0",
      "__refcount_add_not_zero.wraps=0",
      "wg_noise_keypair_get.refcount_zero=0",
      "wg_packet_send_staged_packets.no_keypair=0",
      "wg_packet_send_staged_packets.key_invalid=0",
      "wg_packet_send_staged_packets.birthdate_expired=0",
      "wg_packet_send_staged_packets.nonce_iterate=1",
      "wg_packet_send_staged_packets.nonce_rejected=0",
      "wg_packet_send_staged_packets.nonce_iterate=0",
      "__refcount_add.old_zero=0",
      "__refcount_add.old_negative=0",
      "__refcount_add.wraps=0",
      "wg_packet_create_data.dead=0",
      "wg_queue_enqueue_per_device_and_peer.peer_queue_full=0",
      "wg_cpumask_next_online.wrap=0",
      "wg_queue_enqueue_per_device_and_peer.ring_full=0",
      "wg_packet_create_data.epipe=0",
      "wg_packet_create_data.ok=1",
      "wg_packet_encrypt_worker.consumed=1",
      "wg_packet_encrypt_worker.skb_iterate=1",
      "calculate_skb_padding.no_mtu=0",
      "calculate_skb_padding.over_mtu=0",
      "encrypt_packet.cow_head_failed=0",
      "encrypt_packet.checksum_partial=0",
      "encrypt_packet.cow_data_failed=0",
      "encrypt_packet.too_many_frags=0",
      "encrypt_packet.sgvec_failed=0",
      "wg_packet_encrypt_worker.encrypted=1",
      "wg_packet_encrypt_worker.skb_iterate=0",
      "__refcount_add.old_zero=0",
      "__refcount_add.old_negative=0",
      "__refcount_add.wraps=0",
      "wg_cpumask_choose_online.cpu_invalid=1",
      "wg_cpumask_choose_online.index_iterate=0",
      "wg_peer_put.null=0",
      "__refcount_sub_and_test.old_positive=1",
      "__refcount_sub_and_test.old_equals_i=0",
      "__refcount_sub_and_test.old_nonpositive=0",
      "__refcount_sub_and_test.underflow=0",
      "wg_peer_put.kref_put_released=0",
      "wg_packet_encrypt_worker.need_resched=0",
      "wg_packet_encrypt_worker.consumed=0",
      "wg_prev_queue_peek.peeked=0",
      "wg_packet_tx_worker.packet=1",
      "wg_packet_tx_worker.not_uncrypted=1",
      "wg_packet_tx_worker.crypted=1",
      "wg_timers_any_authenticated_packet_traversal.keepalive=1",
      "mod_peer_timer.running=1",
      "mod_peer_timer.alive=1",
      "wg_packet_create_data_done.skb_iterate=1",
      "wg_socket_send_skb_to_peer.inet=1",
      "wg_socket_send_skb_to_peer.sent=1",
      "wg_packet_create_data_done.sent=1",
      "wg_packet_create_data_done.not_keepalive=0",
      "wg_packet_create_data_done.skb_iterate=0",
      "wg_packet_create_data_done.data_sent=0",
      "keep_key_fresh.keypair=1",
      "keep_key_fresh.valid=1",
      "keep_key_fresh.counter=0",
      "keep_key_fresh.initiator=1",
      "keep_key_fresh.birthdate_expired=0",
      "keep_key_fresh.send=0",
      "wg_noise_keypair_put.null=0",
      "wg_noise_keypair_put.unreference_now=0",
      "__refcount_sub_and_test.old_positive=1",
      "__refcount_sub_and_test.old_equals_i=0",
      "__refcount_sub_and_test.old_nonpositive=0",
      "__refcount_sub_and_test.underflow=0",
      "wg_noise_keypair_put.kref_put_released=0",
      "wg_peer_put.null=0",
      "__refcount_sub_and_test.old_positive=1",
      "__refcount_sub_and_test.old_equals_i=0",
      "__refcount_sub_and_test.old_nonpositive=0",
      "__refcount_sub_and_test.underflow=0",
      "wg_peer_put.kref_put_released=0",
      "wg_packet_tx_worker.need_resched=0",
      "wg_prev_queue_peek.peeked=0",
      "wg_packet_tx_worker.packet=0"]
  | .error _ => false

-- REJECT_AFTER_TIME passed: out_invalid. The key is invalidated, the
-- keepalive goes back on the staged queue, and a handshake is queued.
#guard match run (world 0) with
  | .ok w =>
    w.senderInbox.isEmpty
    && peer w (·.staged) == some [0]
    && kp w (·.sending.isValid) == some false
    && kp w (·.refcount) == some 1
    && (dev w).sendWorkQueue == [0]
    && (labels w).contains "wg_packet_send_staged_packets.birthdate_expired=1"
  | .error _ => false

-- skb_to_sgvec fails: the packet is dead, the tx worker frees it and drops
-- the references, and nothing is sent.
#guard match run (world 1000000000000 (fun s _ => s != .skbToSgvec)) with
  | .ok w =>
    w.senderInbox.isEmpty
    && peer w (·.refcount) == some 1
    && kp w (·.refcount) == some 1
    && (labels w).contains "encrypt_packet.sgvec_failed=1"
    && (labels w).contains "wg_packet_tx_worker.crypted=0"
  | .error _ => false

end Leanux.Tests
