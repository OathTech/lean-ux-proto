"""WireGuard Noise_IKpsk2 for the harness: valid handshake initiations to
inject (stage C), and responses to wg0's own initiations with the session
keys and keepalive both sides derive (stage D1). Pure Python: X25519 (RFC 7748),
ChaCha20-Poly1305 (RFC 8439), BLAKE2s and HMAC-BLAKE2s from the standard
library. Everything is deterministic: the caller chooses the static and
ephemeral private keys, the timestamp and the sender index.

    initiation(responder_public, initiator_private, ephemeral_private,
               timestamp, sender_index) -> 148 bytes

The responder's checks (consume_initiation in drivers/net/wireguard/noise.c)
accept the result iff the responder has the initiator's public key as a peer
and the timestamp is newer than that peer's last one.

    response(initiation, responder_static_private, responder_ephemeral_private,
             psk, sender_index) -> Response (92 bytes and the session keys)
    consume_response(...)  the initiator's checks of a response (raises)
    keepalive(sending_key, receiver_index) -> 32 bytes (wg0's keepalive)
    tai64n(sec, nsec)      the timestamp tai64n_now encodes from a clock read
"""
from dataclasses import dataclass
import hashlib
import hmac
import struct

P = 2**255 - 19
CONSTRUCTION = b"Noise_IKpsk2_25519_ChaChaPoly_BLAKE2s"
IDENTIFIER = b"WireGuard v1 zx2c4 Jason@zx2c4.com"
LABEL_MAC1 = b"mac1----"


def x25519(scalar, point):
    k = bytearray(scalar)
    k[0] &= 248
    k[31] = (k[31] & 127) | 64
    k = int.from_bytes(k, "little")
    u = int.from_bytes(point, "little") & ((1 << 255) - 1)
    x1, x2, z2, x3, z3, swap = u, 1, 0, u, 1, 0
    for t in reversed(range(255)):
        bit = (k >> t) & 1
        swap ^= bit
        if swap:
            x2, x3, z2, z3 = x3, x2, z3, z2
        swap = bit
        a, b = (x2 + z2) % P, (x2 - z2) % P
        aa, bb = a * a % P, b * b % P
        e = (aa - bb) % P
        c, d = (x3 + z3) % P, (x3 - z3) % P
        da, cb = d * a % P, c * b % P
        x3, z3 = (da + cb) ** 2 % P, x1 * (da - cb) ** 2 % P
        x2, z2 = aa * bb % P, e * (aa + 121665 * e) % P
    if swap:
        x2, z2 = x3, z3
    return (x2 * pow(z2, P - 2, P) % P).to_bytes(32, "little")


def public_key(private):
    return x25519(private, (9).to_bytes(32, "little"))


def _quarter(s, a, b, c, d):
    def rotl(v, n):
        return ((v << n) | (v >> (32 - n))) & 0xffffffff
    s[a] = (s[a] + s[b]) & 0xffffffff; s[d] = rotl(s[d] ^ s[a], 16)
    s[c] = (s[c] + s[d]) & 0xffffffff; s[b] = rotl(s[b] ^ s[c], 12)
    s[a] = (s[a] + s[b]) & 0xffffffff; s[d] = rotl(s[d] ^ s[a], 8)
    s[c] = (s[c] + s[d]) & 0xffffffff; s[b] = rotl(s[b] ^ s[c], 7)


def chacha20_block(key, counter, nonce):
    state = [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574, *struct.unpack("<8I", key), counter,
             *struct.unpack("<3I", nonce)]
    s = list(state)
    for _ in range(10):
        for a, b, c, d in ((0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15),
                           (0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14)):
            _quarter(s, a, b, c, d)
    return struct.pack("<16I", *((x + y) & 0xffffffff for x, y in zip(s, state)))


def chacha20(key, counter, nonce, data):
    out = bytearray()
    for i in range(0, len(data), 64):
        block = chacha20_block(key, counter + i // 64, nonce)
        out += bytes(x ^ y for x, y in zip(data[i:i + 64], block))
    return bytes(out)


def poly1305(key, message):
    r = int.from_bytes(key[:16], "little") & 0x0ffffffc0ffffffc0ffffffc0fffffff
    s = int.from_bytes(key[16:], "little")
    acc, p = 0, (1 << 130) - 5
    for i in range(0, len(message), 16):
        n = int.from_bytes(message[i:i + 16] + b"\x01", "little")
        acc = (acc + n) * r % p
    return ((acc + s) % (1 << 128)).to_bytes(16, "little")


def aead_encrypt(key, nonce, plaintext, aad):
    otk = chacha20_block(key, 0, nonce)[:32]
    ciphertext = chacha20(key, 1, nonce, plaintext)
    pad = lambda b: b + bytes(-len(b) % 16)
    tag = poly1305(otk, pad(aad) + pad(ciphertext) + struct.pack("<QQ", len(aad), len(ciphertext)))
    return ciphertext + tag


def _hash(data):
    return hashlib.blake2s(data).digest()


def _hmac(key, data):
    return hmac.new(key, data, hashlib.blake2s).digest()


def _kdf(key, data, n):
    t0 = _hmac(key, data)
    out, prev = [], b""
    for i in range(1, n + 1):
        prev = _hmac(t0, prev + bytes([i]))
        out.append(prev)
    return out


def _nonce(counter):
    return bytes(4) + struct.pack("<Q", counter)


def _flip_last(data):
    return data[:-1] + bytes([data[-1] ^ 1])


def initiation(responder_public, initiator_private, ephemeral_private, timestamp, sender_index, *,
               ephemeral_public=None, static_public=None, mac1_key=None, tamper=None):
    """A handshake initiation (MESSAGE_HANDSHAKE_INITIATION, 148 bytes) to
    `responder_public`, with a valid MAC1 and no MAC2. For negative traces:
    `ephemeral_public` and `static_public` replace the values sent (the
    initiator's own computations still use its private keys), `mac1_key`
    replaces the MAC1 key (a device without an identity uses zeros), and
    `tamper` ('static' or 'timestamp') flips a bit of that field's tag."""
    if len(timestamp) != 12:
        raise ValueError("TAI64N timestamps are 12 bytes")
    if tamper not in (None, "static", "timestamp"):
        raise ValueError(f"unknown tamper target {tamper!r}")
    ck = _hash(CONSTRUCTION)
    h = _hash(_hash(ck + IDENTIFIER) + responder_public)
    e_pub = public_key(ephemeral_private) if ephemeral_public is None else ephemeral_public
    (ck,) = _kdf(ck, e_pub, 1)
    h = _hash(h + e_pub)
    ck, k = _kdf(ck, x25519(ephemeral_private, responder_public), 2)
    s_pub = public_key(initiator_private) if static_public is None else static_public
    enc_static = aead_encrypt(k, _nonce(0), s_pub, h)
    if tamper == "static":
        enc_static = _flip_last(enc_static)
    h = _hash(h + enc_static)
    ck, k = _kdf(ck, x25519(initiator_private, responder_public), 2)
    enc_time = aead_encrypt(k, _nonce(0), timestamp, h)
    if tamper == "timestamp":
        enc_time = _flip_last(enc_time)
    body = struct.pack("<II", 1, sender_index) + e_pub + enc_static + enc_time
    key = _hash(LABEL_MAC1 + responder_public) if mac1_key is None else mac1_key
    mac1 = hashlib.blake2s(body, key=key, digest_size=16).digest()
    return body + mac1 + bytes(16)


# Stage D1: wg0 initiates. The functions below mirror noise.c's
# consume_initiation (as the responder would check wg0's initiation),
# create_response, consume_response and derive_keys, and send.c's
# encrypt_packet for a zero-length keepalive.

class HandshakeError(ValueError):
    """A message the receiving side of noise.c would reject."""


@dataclass(frozen=True)
class Response:
    """A handshake response and the session it establishes. derive_keys
    (noise.c:391-402) splits kdf(chaining_key, "") into two outputs; the
    initiator sends with the first (begin_session, noise.c:832-837) and the
    responder receives with it."""
    message: bytes
    initiator_public: bytes
    initiator_index: int        # the initiation's sender index: the response's receiver index
    responder_index: int        # the response's sender index: the keepalive's key_idx
    initiator_sending: bytes
    initiator_receiving: bytes

    @property
    def responder_sending(self):
        return self.initiator_receiving

    @property
    def responder_receiving(self):
        return self.initiator_sending


def clamp(secret):
    """curve25519_clamp_secret (include/crypto/curve25519.h:61-65)."""
    if len(secret) != 32:
        raise ValueError("Curve25519 secrets are 32 bytes")
    return bytes([secret[0] & 248]) + secret[1:31] + bytes([(secret[31] & 127) | 64])


INITIATIONS_PER_SECOND = 50
TAI64N_NSEC_ALIGN = 1 << 24   # rounddown_pow_of_two(NSEC_PER_SEC / INITIATIONS_PER_SECOND)


def timespec64(sec, nsec):
    """A struct timespec64 (s64 tv_sec, long tv_nsec) as ktime_get_real_ts64
    writes it on x86-64: the value a `tai64n_now` steering entry carries."""
    return struct.pack("<qq", sec, nsec)


def tai64n(sec, nsec):
    """tai64n_now (noise.c:498-514): the nanoseconds rounded down to 2^24,
    then big-endian 0x400000000000000a + sec and nsec."""
    nsec -= nsec % TAI64N_NSEC_ALIGN
    return struct.pack(">QI", (0x400000000000000a + sec) % 2**64, nsec)


def aead_decrypt(key, nonce, ciphertext, aad):
    """ChaCha20-Poly1305 open; raises HandshakeError on a bad tag."""
    if len(ciphertext) < 16:
        raise HandshakeError("ciphertext shorter than its tag")
    body = ciphertext[:-16]
    plaintext = chacha20(key, 1, nonce, body)
    if not hmac.compare_digest(aead_encrypt(key, nonce, plaintext, aad), ciphertext):
        raise HandshakeError("authentication tag mismatch")
    return plaintext


def _dh(private, public):
    """curve25519 (include/crypto/curve25519.h): the null point fails mix_dh."""
    shared = x25519(private, public)
    if shared == bytes(32):
        raise HandshakeError("Diffie-Hellman result is the null point")
    return shared


def _mac1(body, public):
    return hashlib.blake2s(body, key=_hash(LABEL_MAC1 + public), digest_size=16).digest()


def consume_initiation(message, responder_static_private):
    """consume_initiation (noise.c:583-665) up to the peer lookup, with the
    MAC1 check that precedes it (cookie.c): returns (initiator static public,
    sender index, timestamp, chaining key, hash). The replay and flood checks
    depend on the responder's history and are left to the caller."""
    if len(message) != 148 or message[:4] != struct.pack("<I", 1):
        raise HandshakeError("not a handshake initiation")
    responder_public = public_key(responder_static_private)
    if not hmac.compare_digest(_mac1(message[:116], responder_public), message[116:132]):
        raise HandshakeError("MAC1 mismatch")
    ck = _hash(CONSTRUCTION)
    h = _hash(_hash(ck + IDENTIFIER) + responder_public)
    e = message[8:40]
    (ck,) = _kdf(ck, e, 1)
    h = _hash(h + e)
    ck, k = _kdf(ck, _dh(responder_static_private, e), 2)
    enc_static = message[40:88]
    s = aead_decrypt(k, _nonce(0), enc_static, h)
    h = _hash(h + enc_static)
    ck, k = _kdf(ck, _dh(responder_static_private, s), 2)   # the precomputed static-static DH
    enc_time = message[88:116]
    t = aead_decrypt(k, _nonce(0), enc_time, h)
    h = _hash(h + enc_time)
    return s, struct.unpack("<I", message[4:8])[0], t, e, ck, h


def _psk(psk):
    psk = bytes(32) if psk is None else psk
    if len(psk) != 32:
        raise ValueError("preshared keys are 32 bytes")
    return psk


def response(initiation, responder_static_private, responder_ephemeral_private, psk, sender_index, *,
             initiator_public=None, timestamp=None, tamper=None, receiver_index=None):
    """The response (MESSAGE_HANDSHAKE_RESPONSE, 92 bytes) that the peer
    holding `responder_static_private` sends to `initiation`, built as
    create_response (noise.c:667-725) does, with MAC1 keyed by the
    initiator's public key and no MAC2. The initiation is first verified as
    the responder would (consume_initiation); a rejected initiation raises
    HandshakeError, as does an initiator other than `initiator_public` or a
    timestamp other than `timestamp` when given. `psk` None is the zero key.
    `tamper='nothing'` flips a bit of encrypted_nothing's tag (MAC1 stays
    valid); `tamper='mac1'` flips a bit of MAC1. `receiver_index` replaces
    the receiver index sent (the initiation's sender index)."""
    if tamper not in (None, "nothing", "mac1"):
        raise ValueError(f"unknown tamper target {tamper!r}")
    s, receiver, t, e_init, ck, h = consume_initiation(initiation, responder_static_private)
    if initiator_public is not None and s != initiator_public:
        raise HandshakeError("the initiation's static key is not the expected initiator's")
    if timestamp is not None and t != timestamp:
        raise HandshakeError("the initiation's timestamp is not the expected one")
    e_pub = public_key(responder_ephemeral_private)
    if e_pub == bytes(32):
        raise HandshakeError("ephemeral public key is the null point")
    h = _hash(h + e_pub)                                       # message_ephemeral
    (ck,) = _kdf(ck, e_pub, 1)
    (ck,) = _kdf(ck, _dh(responder_ephemeral_private, e_init), 1)   # ee
    (ck,) = _kdf(ck, _dh(responder_ephemeral_private, s), 1)        # se
    ck, temp, k = _kdf(ck, _psk(psk), 3)                       # mix_psk
    h = _hash(h + temp)
    enc_nothing = aead_encrypt(k, _nonce(0), b"", h)
    if tamper == "nothing":
        enc_nothing = _flip_last(enc_nothing)
    sent_receiver = receiver if receiver_index is None else receiver_index
    body = struct.pack("<III", 2, sender_index, sent_receiver) + e_pub + enc_nothing
    mac1 = _mac1(body, s)
    if tamper == "mac1":
        mac1 = _flip_last(mac1)
    sending, receiving = _kdf(ck, b"", 2)                      # derive_keys, initiator's order
    return Response(body + mac1 + bytes(16), s, receiver, sender_index, sending, receiving)


def consume_response(message, initiation, initiator_private, ephemeral_private, responder_public, psk):
    """The initiator's checks of a response to its `initiation` (MAC1 under
    its own public key, then consume_response, noise.c:727-814): returns
    (responder's sender index, initiator sending key, initiator receiving
    key), or raises HandshakeError where the kernel drops the message."""
    if len(message) != 92 or message[:4] != struct.pack("<I", 2):
        raise HandshakeError("not a handshake response")
    initiator_public = public_key(initiator_private)
    if not hmac.compare_digest(_mac1(message[:60], initiator_public), message[60:76]):
        raise HandshakeError("MAC1 mismatch")
    if message[8:12] != initiation[4:8]:
        raise HandshakeError("receiver index names no pending initiation")
    # The initiator's state after create_initiation, recomputed from its message.
    ck = _hash(CONSTRUCTION)
    h = _hash(_hash(ck + IDENTIFIER) + responder_public)
    e_init = initiation[8:40]
    (ck,) = _kdf(ck, e_init, 1)
    h = _hash(h + e_init)
    ck, _ = _kdf(ck, _dh(ephemeral_private, responder_public), 2)
    h = _hash(h + initiation[40:88])
    ck, _ = _kdf(ck, _dh(initiator_private, responder_public), 2)
    h = _hash(h + initiation[88:116])
    e = message[12:44]
    h = _hash(h + e)
    (ck,) = _kdf(ck, e, 1)
    (ck,) = _kdf(ck, _dh(ephemeral_private, e), 1)        # ee
    (ck,) = _kdf(ck, _dh(initiator_private, e), 1)        # se
    ck, temp, k = _kdf(ck, _psk(psk), 3)
    h = _hash(h + temp)
    aead_decrypt(k, _nonce(0), message[44:60], h)
    sending, receiving = _kdf(ck, b"", 2)
    return struct.unpack("<I", message[4:8])[0], sending, receiving


def keepalive(sending_key, receiver_index, counter=0):
    """A zero-length data message as encrypt_packet (send.c:166-220) builds
    it: le32 4, le32 key_idx (the remote index), le64 counter, then the
    ChaCha20-Poly1305 tag of the empty plaintext with nonce counter and no
    associated data. A zero-length payload takes no padding."""
    header = struct.pack("<IIQ", 4, receiver_index, counter)
    return header + aead_encrypt(sending_key, _nonce(counter), b"", b"")


def open_data(message, receiving_key):
    """The receiver's view of a data message: (receiver index, counter,
    plaintext), or HandshakeError on a bad tag."""
    if len(message) < 32 or message[:4] != struct.pack("<I", 4):
        raise HandshakeError("not a data message")
    index, counter = struct.unpack("<IQ", message[4:16])
    return index, counter, aead_decrypt(receiving_key, _nonce(counter), message[16:], b"")


def steered_initiation(responder_public, initiator_private, ephemeral_raw, sec, nsec, sender_index):
    """The initiation create_initiation (noise.c:516-581) builds from steered
    values: `ephemeral_raw` is the random draw before the clamp, (sec, nsec)
    the clock read tai64n_now rounds, `sender_index` the index draw."""
    return initiation(responder_public, initiator_private, clamp(ephemeral_raw), tai64n(sec, nsec), sender_index)
