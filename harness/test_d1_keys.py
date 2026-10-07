"""D1 stream B: the mirror's initiator role against an independent Noise
computation.

The mirror (built `Leanux` library) runs wg0's handshake functions on fixed
hidden records: it creates an initiation, consumes a response that this file
computes in Python (`harness/noise.py` primitives plus a minimal local
responder, `_respond`), and begins the session. The test compares the
initiation bytes, the session keys `kdf(ck_final, "")` in the initiator's
order, the keypair store, the index table and `walltime_last_handshake`.
It also covers the failure arms of `consume_response` (a tampered
`encrypted_nothing`, a wrong receiver index), and a responder session
followed by an initiator session (`add_new_keypair` demotes the pending next
keypair).

Run with `scripts/in-bundle python3 -m unittest harness.test_d1_keys` after
`lake build`; it runs `lake env lean` on a generated driver.
"""
import hashlib
import json
import os
import struct
import subprocess
import tempfile
import unittest
from pathlib import Path

from . import noise

ROOT = Path(__file__).resolve().parents[1]


def _h(data):
    return hashlib.blake2s(data).digest()


def _mac1(body, public):
    return hashlib.blake2s(body, key=_h(noise.LABEL_MAC1 + public), digest_size=16).digest()


def _initiate(responder_public, initiator_private, ephemeral_private, timestamp, sender_index):
    """The initiation, and the chaining key and hash both sides hold after it."""
    ck = _h(noise.CONSTRUCTION)
    h = _h(_h(ck + noise.IDENTIFIER) + responder_public)
    e = noise.public_key(ephemeral_private)
    h = _h(h + e)
    (ck,) = noise._kdf(ck, e, 1)
    ck, k = noise._kdf(ck, noise.x25519(ephemeral_private, responder_public), 2)
    enc_static = noise.aead_encrypt(k, noise._nonce(0), noise.public_key(initiator_private), h)
    h = _h(h + enc_static)
    ck, k = noise._kdf(ck, noise.x25519(initiator_private, responder_public), 2)
    enc_time = noise.aead_encrypt(k, noise._nonce(0), timestamp, h)
    h = _h(h + enc_time)
    body = struct.pack("<II", 1, sender_index) + e + enc_static + enc_time
    return body + _mac1(body, responder_public) + bytes(16), ck, h


def _respond(ck, h, initiator_ephemeral, initiator_static, ephemeral_private, psk, sender_index, receiver_index):
    """A handshake response (92 bytes) and the final chaining key."""
    e = noise.public_key(ephemeral_private)
    h = _h(h + e)
    (ck,) = noise._kdf(ck, e, 1)
    (ck,) = noise._kdf(ck, noise.x25519(ephemeral_private, initiator_ephemeral), 1)
    (ck,) = noise._kdf(ck, noise.x25519(ephemeral_private, initiator_static), 1)
    ck, temp, k = noise._kdf(ck, psk, 3)
    h = _h(h + temp)
    enc_nothing = noise.aead_encrypt(k, noise._nonce(0), b"", h)
    body = struct.pack("<III", 2, sender_index, receiver_index) + e + enc_nothing
    return body + _mac1(body, initiator_static) + bytes(16), ck


def _session(ck):
    """`kdf(ck, "")`: the initiator's sending, then receiving key."""
    return noise._kdf(ck, b"", 2)


def _tai64n(sec, nsec):
    return struct.pack(">QI", 0x400000000000000a + sec, nsec - nsec % (1 << 24))


def _clock(ns):
    return struct.pack("<q", ns).hex()


def _timespec(sec, nsec):
    return struct.pack("<qq", sec, nsec).hex()


WG0_PRIVATE = bytes(range(1, 33))
PEER_PRIVATE = bytes(range(101, 133))
WG0_PUBLIC = noise.public_key(WG0_PRIVATE)
PEER_PUBLIC = noise.public_key(PEER_PRIVATE)
PSK = bytes([0x5a] * 32)
INIT_EPHEMERAL = bytes(range(33, 65))      # wg0's raw draw (the mirror clamps)
RESP_EPHEMERAL = bytes(range(201, 233))    # the peer's
WG0_INDEX = 0x11223344
PEER_INDEX = 0x0badf00d
NOW = (1767225600, 987654321)               # wg0's tai64n_now read
WALL = (1767225601, 123456789)              # walltime_last_handshake
RESET, BIRTH = 10 ** 12, 3 * 10 ** 12


DRIVER = r'''
import Leanux.Runner
open Leanux Leanux.WG Lean

def hx (s : String) : List UInt8 :=
  let digit (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let cs := s.toList
  (List.range (cs.length / 2)).map fun i => UInt8.ofNat (digit cs[2 * i]! * 16 + digit cs[2 * i + 1]!)

def hs (bs : List UInt8) : String :=
  let d := "0123456789abcdef".toList
  String.join (bs.map fun b => String.ofList [d[b.toNat / 16]!, d[b.toNat % 16]!])

def rec (s : HiddenSite) (hex : String) : HiddenRecord :=
  let bs := hx hex
  ⟨s.info.id, bs ++ List.replicate ((8 - bs.length % 8) % 8) 0⟩

def keypairJson (id : KeypairId) : M Json := do
  let k ← getKeypair id
  return Json.mkObj [("id", toJson id), ("sending", toJson (hs k.sending.key)),
    ("receiving", toJson (hs k.receiving.key)),
    ("birthdates", toJson [k.sending.birthdate, k.receiving.birthdate]),
    ("valid", toJson [k.sending.isValid, k.receiving.isValid]),
    ("initiator", toJson k.iAmTheInitiator), ("remote_index", toJson k.remoteIndex),
    ("refcount", toJson k.refcount), ("internal_id", toJson k.internalId), ("counter", toJson k.sendingCounter)]

def stateJson (pid : PeerId) : M Json := do
  let p ← getPeer pid
  let d ← getDev
  let kps ← d.keypairs.toList.mapM fun (id, _) => keypairJson id
  return Json.mkObj [("current", toJson p.keypairCurrent), ("previous", toJson p.keypairPrevious),
    ("next", toJson p.keypairNext), ("keypairs", toJson kps),
    ("index_table", toJson (d.indexTable.map fun e =>
      Json.mkObj [("index", toJson e.index), ("keypair", toJson e.keypair),
                  ("kind", toJson (if e.kind == .handshake then "handshake" else "keypair"))])),
    ("handshake_state", toJson p.handshakeState), ("handshake_remote_index", toJson p.remoteIndex),
    ("chaining_key", toJson (hs p.chainingKey)),
    ("walltime", toJson (timespec p.walltimeLastHandshake)), ("refcount", toJson p.refcount)]

def runM (records : List HiddenRecord) (act : M Json) : String :=
  let w : World := { k := Runner.initialKernel 1024 true, timing := Env.timing,
                     hidden := some records }
  match act.run w with
  | .ok (j, w) => (Json.mkObj [("result", j), ("steps", toJson (w.steps.toList.map (·.label))),
                               ("left", toJson (w.hidden.getD []).length)]).compress
  | .error e => (Json.mkObj [("stop", toJson e.message)]).compress

def setup (wg0 peer psk : String) : M PeerId := do
  setStaticIdentityPrivateKey (hx wg0)
  let .ok pid ← peerCreate (hx peer) (some (hx psk)) | invariant "wg_peer_create failed"
  return pid

def initiateThenConsume (wg0 peer psk resp : String) : M Json := do
  let pid ← setup wg0 peer psk
  let some init ← createInitiation pid | invariant "no initiation"
  let init ← addMacToPacket pid init
  let consumed ← consumeResponse (hx resp)
  let begun ← match consumed with
    | some p => do
      let b ← beginSession p
      if b then timersHandshakeComplete p
      pure b
    | none => pure false
  return Json.mkObj [("initiation", toJson (hs init)), ("consumed", toJson consumed.isSome),
    ("begun", toJson begun), ("state", ← stateJson pid)]

def respondThenInitiate (wg0 peer psk peerInit resp : String) : M Json := do
  let pid ← setup wg0 peer psk
  let some _ ← consumeInitiation (hx peerInit) | invariant "initiation not consumed"
  let some r ← createResponse pid | invariant "no response"
  let b1 ← beginSession pid
  let middle ← stateJson pid
  let some init ← createInitiation pid | invariant "no initiation"
  let init ← addMacToPacket pid init
  let some _ ← consumeResponse (hx resp) | invariant "response not consumed"
  let b2 ← beginSession pid
  timersHandshakeComplete pid
  return Json.mkObj [("response", toJson (hs r)), ("initiation", toJson (hs init)),
    ("begun", toJson [b1, b2]), ("after_response", middle), ("state", ← stateJson pid)]
'''


def _lean_string(s):
    return '"' + s + '"'


def _records(*pairs):
    return "[" + ", ".join(f"rec .{site} {_lean_string(value)}" for site, value in pairs) + "]"


class D1KeysTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.init_msg, cls.init_ck, cls.init_h = _initiate(
            PEER_PUBLIC, WG0_PRIVATE, INIT_EPHEMERAL, _tai64n(*NOW), WG0_INDEX)
        cls.response, cls.final_ck = _respond(
            cls.init_ck, cls.init_h, noise.public_key(INIT_EPHEMERAL), WG0_PUBLIC, RESP_EPHEMERAL, PSK,
            PEER_INDEX, WG0_INDEX)
        tampered = bytearray(cls.response)
        tampered[59] ^= 1
        wrong_index = bytearray(cls.response)
        wrong_index[8:12] = struct.pack("<I", WG0_INDEX ^ 0x10000)
        initiator_records = [("resetLastSent", _clock(RESET)), ("initEphemeral", INIT_EPHEMERAL.hex()),
                             ("tai64nNow", _timespec(*NOW)), ("indexDraw", struct.pack("<I", WG0_INDEX).hex())]
        session_records = [("deriveKeysBirthdate", _clock(BIRTH)), ("walltimeLastHandshake", _timespec(*WALL))]

        # respond, then initiate: the peer initiates first, wg0 responds
        cls.peer_ts = bytes(11) + b"\x01"
        cls.peer_init, ck, h = _initiate(WG0_PUBLIC, PEER_PRIVATE, RESP_EPHEMERAL[::-1], cls.peer_ts, 0x5150)
        cls.wg0_resp_ephemeral = bytes(range(64, 96))
        cls.wg0_resp_index = 0x00aa0001
        cls.wg0_response, cls.responder_ck = _respond(
            ck, h, noise.public_key(RESP_EPHEMERAL[::-1]), PEER_PUBLIC, cls.wg0_resp_ephemeral, PSK,
            cls.wg0_resp_index, 0x5150)
        responder_records = [("resetLastSent", _clock(RESET)), ("floodNow", _clock(2 * RESET)),
                             ("consumptionNow", _clock(2 * RESET)), ("respEphemeral", cls.wg0_resp_ephemeral.hex()),
                             ("indexDraw", struct.pack("<I", cls.wg0_resp_index).hex()),
                             ("deriveKeysBirthdate", _clock(BIRTH - 1))]
        second_records = [("initEphemeral", INIT_EPHEMERAL.hex()), ("tai64nNow", _timespec(*NOW)),
                          ("indexDraw", struct.pack("<I", WG0_INDEX).hex())] + session_records

        args = f'{_lean_string(WG0_PRIVATE.hex())} {_lean_string(PEER_PUBLIC.hex())} {_lean_string(PSK.hex())}'
        evals = [
            f'#eval IO.println (runM {_records(*initiator_records, *session_records)} '
            f'(initiateThenConsume {args} {_lean_string(cls.response.hex())}))',
            f'#eval IO.println (runM {_records(*initiator_records)} '
            f'(initiateThenConsume {args} {_lean_string(bytes(tampered).hex())}))',
            f'#eval IO.println (runM {_records(*initiator_records)} '
            f'(initiateThenConsume {args} {_lean_string(bytes(wrong_index).hex())}))',
            f'#eval IO.println (runM {_records(*responder_records, *second_records)} '
            f'(respondThenInitiate {args} {_lean_string(cls.peer_init.hex())} {_lean_string(cls.response.hex())}))',
        ]
        with tempfile.TemporaryDirectory(dir=os.environ.get("TMPDIR")) as tmp:
            driver = Path(tmp) / "D1Keys.lean"
            driver.write_text(DRIVER + "\n".join(evals) + "\n")
            run = subprocess.run(["lake", "env", "lean", str(driver)], cwd=ROOT, capture_output=True, text=True,
                                 timeout=600)
        if run.returncode != 0:
            raise AssertionError(f"lean driver failed:\n{run.stdout}\n{run.stderr}")
        cls.runs = [json.loads(line) for line in run.stdout.splitlines() if line.startswith("{")]
        if len(cls.runs) != len(evals):
            raise AssertionError(f"expected {len(evals)} results:\n{run.stdout}")

    def result(self, index):
        run = self.runs[index]
        self.assertNotIn("stop", run, run.get("stop"))
        self.assertEqual(run["left"], 0, "records left unconsumed")
        return run["result"], run["steps"]

    def test_initiation_matches_harness(self):
        expected = noise.initiation(PEER_PUBLIC, WG0_PRIVATE, INIT_EPHEMERAL, _tai64n(*NOW), WG0_INDEX)
        self.assertEqual(expected, self.init_msg)
        result, _ = self.result(0)
        self.assertEqual(result["initiation"], expected.hex())

    def test_initiator_session(self):
        result, steps = self.result(0)
        self.assertTrue(result["consumed"])
        self.assertTrue(result["begun"])
        sending, receiving = _session(self.final_ck)
        state = result["state"]
        self.assertEqual(state["current"], 0)
        self.assertIsNone(state["previous"])
        self.assertIsNone(state["next"])
        (kp,) = state["keypairs"]
        self.assertEqual(kp["sending"], sending.hex())
        self.assertEqual(kp["receiving"], receiving.hex())
        self.assertEqual(kp["birthdates"], [BIRTH, BIRTH])
        self.assertEqual(kp["valid"], [True, True])
        self.assertTrue(kp["initiator"])
        self.assertEqual(kp["remote_index"], PEER_INDEX)
        self.assertEqual((kp["refcount"], kp["internal_id"], kp["counter"]), (1, 1, 0))
        # the keypair's entry took the handshake's index
        self.assertEqual(state["index_table"], [{"index": WG0_INDEX, "keypair": 0, "kind": "keypair"}])
        self.assertEqual((state["handshake_state"], state["handshake_remote_index"]), (0, 0))
        self.assertEqual(state["chaining_key"], "00" * 32)
        self.assertEqual(state["walltime"], list(WALL))
        self.assertEqual(state["refcount"], 2)   # the lookup's reference, put by the receive epilogue
        for label in ("wg_noise_handshake_consume_response.state_changed=0",
                      "wg_noise_handshake_begin_session.initiator=1", "add_new_keypair.initiator=1",
                      "add_new_keypair.has_next_keypair=0"):
            self.assertIn(label, steps)

    def test_tampered_response(self):
        result, steps = self.result(1)
        self.assertFalse(result["consumed"])
        self.assertIn("message_decrypt.failed=1", steps)
        self.assertIn("wg_noise_handshake_consume_response.decrypt_failed=1", steps)
        state = result["state"]
        self.assertEqual(state["handshake_state"], 1)
        self.assertEqual(state["keypairs"], [])
        self.assertEqual(state["index_table"], [{"index": WG0_INDEX, "keypair": None, "kind": "handshake"}])
        self.assertEqual(state["refcount"], 1)   # the failure path put the lookup's reference

    def test_wrong_receiver_index(self):
        result, steps = self.result(2)
        self.assertFalse(result["consumed"])
        self.assertIn("wg_noise_handshake_consume_response.no_handshake=1", steps)
        self.assertEqual(result["state"]["refcount"], 1)

    def test_respond_then_initiate(self):
        result, steps = self.result(3)
        self.assertEqual(result["begun"], [True, True])
        self.assertEqual(result["response"][:120], self.wg0_response[:60].hex())
        middle = result["after_response"]
        self.assertEqual((middle["current"], middle["previous"], middle["next"]), (None, None, 0))
        r_first, r_second = _session(self.responder_ck)
        (kp0,) = middle["keypairs"]
        self.assertEqual((kp0["receiving"], kp0["sending"]), (r_first.hex(), r_second.hex()))
        self.assertFalse(kp0["initiator"])
        self.assertEqual(kp0["remote_index"], 0x5150)
        self.assertEqual(result["initiation"], self.init_msg.hex())
        state = result["state"]
        # the pending next keypair is demoted to previous; the new one is current
        self.assertEqual((state["current"], state["previous"], state["next"]), (1, 0, None))
        kp0, kp1 = state["keypairs"]
        sending, receiving = _session(self.final_ck)
        self.assertEqual((kp1["sending"], kp1["receiving"]), (sending.hex(), receiving.hex()))
        self.assertEqual((kp0["internal_id"], kp1["internal_id"]), (1, 2))
        self.assertEqual(sorted((e["index"], e["keypair"]) for e in state["index_table"]),
                         sorted([(self.wg0_resp_index, 0), (WG0_INDEX, 1)]))
        self.assertIn("add_new_keypair.has_next_keypair=1", steps)
        self.assertIn("add_new_keypair.initiator=0", steps)


if __name__ == "__main__":
    unittest.main()
