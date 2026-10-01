"""A WireGuard Noise_IKpsk2 initiator, for building valid handshake
initiations to inject (stage C). Pure Python: X25519 (RFC 7748),
ChaCha20-Poly1305 (RFC 8439), BLAKE2s and HMAC-BLAKE2s from the standard
library. Everything is deterministic: the caller chooses the static and
ephemeral private keys, the timestamp and the sender index.

    initiation(responder_public, initiator_private, ephemeral_private,
               timestamp, sender_index) -> 148 bytes

The responder's checks (consume_initiation in drivers/net/wireguard/noise.c)
accept the result iff the responder has the initiator's public key as a peer
and the timestamp is newer than that peer's last one.
"""
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
