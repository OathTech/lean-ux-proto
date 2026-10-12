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

Stage D2 (the data plane, docs/2026-10-04-d2-data-plane.md, sections 2, 4, 6):

    initiator_session(response) / responder_session(response) -> Session
                           wg0's keys and indices for either role
    wg0_response(...)      the response wg0 sends to a peer's initiation
    data_message(sending_key, receiver_index, counter, plaintext)
                           a message_data, padded as encrypt_packet pads
    ipv4_udp(...) / ipv6_udp(...)
                           inner packets, honest or dishonest
    xmit_packet(family, dst, payload)
                           the inner packet the fixture's stack hands wg_xmit
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


# Stage D2: the data plane. A session from wg0's side, data messages in both
# directions, and the inner IP packets they carry.

DEVICE_MTU = 1420                 # wg0's MTU, and the route's dst MTU (design section 2)
MESSAGE_PADDING_MULTIPLE = 16
MESSAGE_DATA_HEADER = 16          # le32 type, le32 key_idx, le64 counter
COUNTER_BITS_TOTAL = 8192
COUNTER_WINDOW_SIZE = COUNTER_BITS_TOTAL - 64          # COUNTER_REDUNDANT_BITS = BITS_PER_LONG
REJECT_AFTER_MESSAGES = 2**64 - 1 - COUNTER_WINDOW_SIZE - 1   # messages.h: U64_MAX - window - 1

# The fixture (harness/guest.c): wg0's addresses (route_into_wg0), the
# sender's port (SEND_FD, bound to [::]:51998) and the port wg_xmit sends to.
WG0_ADDR4 = bytes([10, 255, 254, 1])
WG0_ADDR6 = bytes.fromhex("fd00ffff000000000000000000000001")
SENDER_PORT = 51998
SEND_PORT = 40000
CSUM_MANGLED_0 = 0xffff


@dataclass(frozen=True)
class Session:
    """A session as wg0 holds it. `sending`/`receiving` are wg0's keys;
    `local_index` is wg0's index (the key_idx of messages to wg0) and
    `remote_index` the peer's (the key_idx of wg0's messages)."""
    sending: bytes
    receiving: bytes
    local_index: int
    remote_index: int
    initiator: bool

    def to_wg0(self, counter, plaintext, **kw):
        """The message_data the peer sends to wg0 (see data_message)."""
        return data_message(self.receiving, self.local_index, counter, plaintext, **kw)

    def from_wg0(self, counter, plaintext, **kw):
        """The message_data wg0 sends with this session."""
        return data_message(self.sending, self.remote_index, counter, plaintext, **kw)

    def open_from_wg0(self, message):
        """Decrypt wg0's message_data: (counter, padded plaintext); raises
        HandshakeError on another key_idx or a bad tag."""
        index, counter, plaintext = open_data(message, self.sending)
        if index != self.remote_index:
            raise HandshakeError("key_idx is not the peer's index")
        return counter, plaintext


def initiator_session(response):
    """wg0 initiated: `response` is the peer's (noise.response to wg0's
    initiation). wg0 sends with the first derived key (begin_session's
    initiator order) to the peer's sender index."""
    return Session(response.initiator_sending, response.initiator_receiving, response.initiator_index,
                   response.responder_index, True)


def responder_session(response):
    """wg0 responded: `response` is wg0's own (wg0_response). wg0 receives
    with the first derived key, which the peer sends with."""
    return Session(response.responder_sending, response.responder_receiving, response.responder_index,
                   response.initiator_index, False)


def wg0_response(peer_initiation, wg0_private, resp_ephemeral_raw, psk, wg0_index):
    """The response wg0 (holding `wg0_private`) builds to a peer's initiation
    from its steered draws: `resp_ephemeral_raw` (the `resp_ephemeral` draw,
    before curve25519_generate_secret's clamp, which x25519 applies anyway)
    and `wg0_index` (the `index_draw`). Feed it to responder_session."""
    return response(peer_initiation, wg0_private, clamp(resp_ephemeral_raw), psk, wg0_index)


def padding(length, mtu=DEVICE_MTU):
    """calculate_skb_padding (send.c:141-160) for an skb of `length` bytes."""
    align = lambda n: -(-n // MESSAGE_PADDING_MULTIPLE) * MESSAGE_PADDING_MULTIPLE
    if not mtu:
        return align(length) - length
    last_unit = length % mtu if length > mtu else length
    return min(mtu, align(last_unit)) - last_unit


def data_message(sending_key, receiver_index, counter, plaintext, *, mtu=DEVICE_MTU, tamper=False):
    """A message_data as encrypt_packet (send.c:162-219) builds it: le32 4,
    le32 receiver_index (the receiver's key index), le64 counter, then the
    ChaCha20-Poly1305 encryption of the plaintext padded with zeros as
    calculate_skb_padding pads it (ALIGN(len, 16) clamped by the MTU), with
    the nonce `4 zero bytes || le64 counter` and no associated data.
    `tamper` flips a bit of the tag."""
    if not 0 <= counter < 2**64:
        raise ValueError("the counter is a u64")
    padded = plaintext + bytes(padding(len(plaintext), mtu))
    sealed = aead_encrypt(sending_key, _nonce(counter), padded, b"")
    if tamper:
        sealed = _flip_last(sealed)
    return struct.pack("<IIQ", 4, receiver_index, counter) + sealed


def message_data_len(plaintext_len):
    """message_data_len (messages.h): what update_rx_stats adds for a
    decrypted skb of `plaintext_len` bytes (padding included)."""
    return MESSAGE_DATA_HEADER + plaintext_len + 16


# Inner packets. Addresses are bytes (4 or 16); every multi-byte field is
# big-endian.

def _sum16(data):
    if len(data) % 2:
        data += b"\0"
    total = sum(struct.unpack(f">{len(data) // 2}H", data))
    while total >> 16:
        total = (total & 0xffff) + (total >> 16)
    return total


def inet_checksum(data):
    """The Internet checksum (RFC 1071): the complement of the folded
    one's-complement sum."""
    return ~_sum16(data) & 0xffff


def _udp(src, dst, sport, dport, payload, checksum, ulen, pseudo):
    ulen = 8 + len(payload) if ulen is None else ulen
    header = struct.pack(">HHHH", sport, dport, ulen, 0)
    correct = inet_checksum(pseudo(ulen) + header + payload) or CSUM_MANGLED_0
    if checksum == "correct":
        value = correct
    elif checksum == "wrong":   # nonzero, and not the correct sum in either representation of zero
        value = 0x1234 if correct != 0x1234 else 0x4321
    elif checksum == "zero":
        value = 0
    elif type(checksum) is int and 0 <= checksum <= 0xffff:
        value = checksum
    else:
        raise ValueError(f"unknown checksum {checksum!r}")
    return header[:6] + struct.pack(">H", value) + payload


def ipv4_udp(src, dst, sport, dport, payload, *, checksum="correct", tot_len=None, ulen=None, version=4,
             ttl=64, ident=0, df=True, tos=0, protocol=17):
    """An IPv4/UDP packet without options: version/ihl `version`/5, the
    header checksum correct over the header as written. `tot_len`, `ulen`
    and `version` override the honest values (the dishonest variants);
    `checksum` is the UDP checksum: "correct" (0 sent as CSUM_MANGLED_0),
    "wrong" (nonzero and incorrect), "zero", or a value."""
    if len(src) != 4 or len(dst) != 4:
        raise ValueError("IPv4 addresses are 4 bytes")
    pseudo = lambda n: src + dst + struct.pack(">BBH", 0, protocol, n)
    udp = _udp(src, dst, sport, dport, payload, checksum, ulen, pseudo)
    tot_len = 20 + len(udp) if tot_len is None else tot_len
    header = struct.pack(">BBHHHBBH4s4s", (version << 4) | 5, tos, tot_len, ident, 0x4000 if df else 0, ttl,
                         protocol, 0, src, dst)
    header = header[:10] + struct.pack(">H", inet_checksum(header)) + header[12:]
    return header + udp


def ipv6_udp(src, dst, sport, dport, payload, *, checksum="correct", payload_len=None, ulen=None, version=6,
             hop_limit=64, flow_label=0, traffic_class=0, next_header=17):
    """An IPv6/UDP packet without extension headers. `payload_len`, `ulen`
    and `version` override the honest values; `checksum` as for ipv4_udp
    (a zero UDP checksum is dropped on IPv6)."""
    if len(src) != 16 or len(dst) != 16:
        raise ValueError("IPv6 addresses are 16 bytes")
    pseudo = lambda n: src + dst + struct.pack(">I3xB", n, next_header)
    udp = _udp(src, dst, sport, dport, payload, checksum, ulen, pseudo)
    payload_len = len(udp) if payload_len is None else payload_len
    first = (version << 28) | (traffic_class << 20) | flow_label
    return struct.pack(">IHBB", first, payload_len, next_header, hop_limit) + src + dst + udp


def ipv4_tcp(src, dst, sport, dport, seq, ack_seq, flags, payload=b"", *, tos=0, ttl=64, ident=0, df=True,
             window=8192, doff=5, checksum="correct"):
    """An IPv4/TCP segment without IP options and, with `doff` 5, without
    TCP options (W6, docs/2026-10-06-w5-w6-receive.md 2.4.1): `flags` is the
    TCP flag byte (FIN 1, SYN 2, RST 4, PSH 8, ACK 16). A `doff` above 5
    pads the header with zero option bytes (the stack still answers; the
    mirror refuses the shape). The TCP checksum is correct unless
    `checksum` is "wrong" (wg marks the skb CHECKSUM_UNNECESSARY, so Linux
    answers either)."""
    if len(src) != 4 or len(dst) != 4:
        raise ValueError("IPv4 addresses are 4 bytes")
    options = bytes(4 * (doff - 5))
    tcp_len = 4 * doff + len(payload)
    header = struct.pack(">HHIIBBHHH", sport, dport, seq, ack_seq, doff << 4, flags, window, 0, 0) + options
    pseudo = src + dst + struct.pack(">BBH", 0, 6, tcp_len)
    value = inet_checksum(pseudo + header + payload)
    if checksum == "wrong":
        value = 0x1234 if value != 0x1234 else 0x4321
    tcp = header[:16] + struct.pack(">H", value) + header[18:] + payload
    tot_len = 20 + len(tcp)
    ip = struct.pack(">BBHHHBBH4s4s", 0x45, tos, tot_len, ident, 0x4000 if df else 0, ttl, 6, 0, src, dst)
    ip = ip[:10] + struct.pack(">H", inet_checksum(ip)) + ip[12:]
    return ip + tcp


def rst4(packet):
    """The IPv4 TCP RST Linux sends for `packet`, a segment to wg0 with no
    socket (tcp_v4_send_reset, tcp_ipv4.c:737-920; ip_send_unicast_reply,
    ip_output.c:1603-1677): dest/source swapped, doff 5, RST; with ACK:
    seq = ack_seq; without: ACK set, ack_seq = seq + syn + fin + payload
    length; window 0; the checksum folded in software; IP: tos = the inner
    tos with the ECN bits cleared, tot_len 40, id 0, DF, TTL 64, from the
    inner destination to the inner source. None when Linux sends nothing
    (a segment with RST)."""
    ihl = (packet[0] & 0xf) * 4
    src, dst = packet[12:16], packet[16:20]
    th = packet[ihl:]
    sport, dport, seq, ack_seq = struct.unpack_from(">HHII", th)
    doff, flags = th[12] >> 4, th[13]
    if flags & 4:
        return None
    if flags & 16:
        rseq, rack, rflags = ack_seq, 0, 4
    else:
        rseq, rack, rflags = 0, (seq + ((flags >> 1) & 1) + (flags & 1) + len(th) - 4 * doff) & 0xffffffff, 4 | 16
    header = struct.pack(">HHIIBBHHH", dport, sport, rseq, rack, 5 << 4, rflags, 0, 0, 0)
    pseudo = dst + src + struct.pack(">BBH", 0, 6, 20)
    tcp = header[:16] + struct.pack(">H", inet_checksum(pseudo + header)) + header[18:]
    ip = struct.pack(">BBHHHBBH4s4s", 0x45, packet[1] & ~3, 40, 0, 0x4000, 64, 6, 0, dst, src)
    ip = ip[:10] + struct.pack(">H", inet_checksum(ip)) + ip[12:]
    return ip + tcp


def to_wg0(family, src, payload, sport=12345, **kw):
    """An inner UDP packet for wg0's local address and the sender's port
    (51998), from `src`: delivered to the fixture's sender socket when the
    source is in the peer's allowed IPs and the packet passes the stack
    (design section 4)."""
    build = ipv4_udp if family == 4 else ipv6_udp
    return build(src, WG0_ADDR4 if family == 4 else WG0_ADDR6, sport, SENDER_PORT, payload, **kw)


def xmit_packet(family, dst, payload):
    """The packet the fixture's stack hands wg_xmit for a `wg_xmit` operation
    (design section 2) after skb_checksum_help: from wg0's address, port
    51998 to `dst` port 40000. IPv4: tos 0, DF (IP_PMTUDISC_DO), id 0, TTL 64.
    IPv6: traffic class and flow label 0 (IPV6_AUTOFLOWLABEL off), hop limit
    64. The UDP checksum is complete, 0 written as CSUM_MANGLED_0."""
    if family == 4:
        return ipv4_udp(WG0_ADDR4, dst, SENDER_PORT, SEND_PORT, payload)
    if family == 6:
        if dst[0] == 0xfe and dst[1] & 0xc0 == 0x80:
            raise ValueError("fe80::/10 destinations take wg0's random link-local source")
        return ipv6_udp(WG0_ADDR6, dst, SENDER_PORT, SEND_PORT, payload)
    raise ValueError("family 4 or 6")


def gso_segments(dst, payload, gso_size):
    """W4 (docs/2026-10-06-w4-w7-transmit-bulk.md section 2.1): the IPv4
    packets wg_xmit receives for one UDP_SEGMENT datagram of `payload` from
    the fixture's unconnected IP_PMTUDISC_DO/PROBE sender: equal segments of
    `gso_size` bytes, ids 0..n-1 (the super-skb's id is 0), DF, a complete
    UDP checksum per segment (0 as CSUM_MANGLED_0), as Env.gsoSegment."""
    if gso_size <= 0 or len(payload) % gso_size or not 2 <= len(payload) // gso_size <= 128:
        raise ValueError("a GSO payload is 2-128 whole segments")
    return [ipv4_udp(WG0_ADDR4, dst, SENDER_PORT, SEND_PORT, payload[i:i + gso_size], ident=i // gso_size)
            for i in range(0, len(payload), gso_size)]


def wg0_data(session, counter, family, dst, payload):
    """The message_data wg0 sends for a `wg_xmit` of `payload` to `dst`
    under `session`, with nonce `counter`."""
    return session.from_wg0(counter, xmit_packet(family, dst, payload))


# Stage E (docs/2026-10-05-e-dos.md, section 6.A): the cookie reply wg0
# consumes (cookie.c:198-236) and the MAC2 it then puts on its handshakes
# (cookie.c:156-178).

LABEL_COOKIE = b"cookie--"
COOKIE_LEN = 16
COOKIE_NONCE_LEN = 24
MESSAGE_HANDSHAKE_COOKIE = 3


def _chacha20_permute(state):
    """The 20-round ChaCha permutation of a 16-word state, without the
    feed-forward addition chacha20_block applies."""
    s = list(state)
    for _ in range(10):
        for a, b, c, d in ((0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15),
                           (0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14)):
            _quarter(s, a, b, c, d)
    return s


def hchacha20(key, nonce16):
    """HChaCha20 (lib/crypto/chacha.c hchacha_block_generic): words 0-3 and
    12-15 of the permuted state, keyed by `key` with `nonce16` in words 12-15."""
    s = _chacha20_permute([0x61707865, 0x3320646e, 0x79622d32, 0x6b206574, *struct.unpack("<8I", key),
                           *struct.unpack("<4I", nonce16)])
    return struct.pack("<8I", *s[0:4], *s[12:16])


def xchacha20poly1305_encrypt(key, nonce, plaintext, aad):
    """lib/crypto/chacha20poly1305.c xchacha_init: the subkey HChaCha20(key,
    nonce[0:16]), then ChaCha20-Poly1305 under it with the nonce 0^4 ||
    nonce[16:24]."""
    assert len(nonce) == COOKIE_NONCE_LEN
    return aead_encrypt(hchacha20(key, nonce[:16]), bytes(4) + nonce[16:], plaintext, aad)


def xchacha20poly1305_decrypt(key, nonce, sealed, aad):
    assert len(nonce) == COOKIE_NONCE_LEN
    return aead_decrypt(hchacha20(key, nonce[:16]), bytes(4) + nonce[16:], sealed, aad)


def cookie_key(public):
    """precompute_key(…, public, "cookie--") (cookie.c:33-42): the sender of
    a cookie reply encrypts under its own public key's key; the receiver
    (wg_cookie_checker_precompute_peer_keys, cookie.c:61-67) decrypts under
    its peer's."""
    return _hash(LABEL_COOKIE + public)


def last_mac1(handshake_message):
    """macs->mac1 of a handshake message (the AAD of the cookie reply)."""
    return handshake_message[-32:-16]


def cookie_message(receiver_index, cookie, nonce, mac1, sender_public, *, aad=None):
    """struct message_handshake_cookie (messages.h:98-103) as
    wg_cookie_message_create (cookie.c:180-196) builds it at the sender:
    header 3, the receiver's index, the nonce, and the cookie encrypted
    under cookie_key(sender_public) with AAD = the MAC1 of the handshake it
    answers. `aad` overrides that AAD (a reply the receiver cannot decrypt)."""
    assert len(cookie) == COOKIE_LEN and len(mac1) == COOKIE_LEN
    sealed = xchacha20poly1305_encrypt(cookie_key(sender_public), nonce, cookie, mac1 if aad is None else aad)
    return struct.pack("<II", MESSAGE_HANDSHAKE_COOKIE, receiver_index) + nonce + sealed


def consume_cookie_message(message, last_mac1_sent, sender_public):
    """The receiver's decrypt (cookie.c:216-219): the cookie, or HandshakeError."""
    if len(message) != 64 or message[:4] != struct.pack("<I", MESSAGE_HANDSHAKE_COOKIE):
        raise HandshakeError("not a cookie reply")
    return xchacha20poly1305_decrypt(cookie_key(sender_public), message[8:32], message[32:], last_mac1_sent)


def make_cookie(secret, saddr_be, sport):
    """make_cookie (cookie.c:91-117): keyed BLAKE2s-128 under the checker secret
    over the source IP (network order) and source port (network order). E-B arm
    C steers the secret so the fixture can compute a valid MAC2 offline."""
    return hashlib.blake2s(saddr_be + struct.pack(">H", sport), key=secret, digest_size=16).digest()


def mac2(handshake_message, cookie):
    """compute_mac2 (cookie.c:83-89): keyed BLAKE2s-128 under the cookie over
    the message up to mac2."""
    return hashlib.blake2s(handshake_message[:-16], key=cookie, digest_size=16).digest()


def with_mac2(handshake_message, cookie):
    """The message with mac2 = compute_mac2(message, cookie)."""
    return handshake_message[:-16] + mac2(handshake_message, cookie)
