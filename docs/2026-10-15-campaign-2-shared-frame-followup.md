# Campaign 2: additional shared-frame dependencies

This supplements the [six-family outer-removal request](2026-10-15-campaign-2-shared-frame-request.md).
It requests a proof-support scope decision, not a mirror change. No existing
campaign-1 lemma has been edited. The inventories below were independently
checked against the current original operations and proof files.

[USER 2026-10-15] Shared layers remain campaign 1's; local variants must name
the shared lemmas they replace. If an increment needs more than a few, report
the overlap before copying a layer. The original six-family decision remains
pending and does not authorize these additional families.

## State-split update, 2026-10-17

The inventory below records the pre-split overlap. With b700659, the skb store
is a separate component: the existing guarded liftSkb adapter now supplies
table/cursor preservation for allocation, updates and frees. The checked H2
consumeData continuation needs two substantive queue families, implemented
locally in Index/RxQueueFrames, with claims in ReceiveDataClaims. Its callback
is the actual empty WG callback. This bounded package does not copy the old
nine-family layer. The broader ingress/worker and H1 inventories remain open;
see the campaign report for checked scope and validation. No mirror request
or authorization to duplicate the wider shared layers is inferred.

The next packetReceive/wgReceive composition still needs four leaf families:
validateHeaderLen, prepareSkbHeader, ipTunnelGetDsfield and cpumaskNextOnline.
Campaign 1 now has native full-WG header frames in Framing/WGReceiveHeaders;
the CPU helper still requires a table/cursor-specific frame. These operations
remain WG.M, so their preservation is not supplied by type alone. The callers
have no callback parameter, and handshake receipt only enqueues its worker.
The four-family addition remains pending under the existing overlap request;
it is not implemented as a way to divide the larger shared support layer.
Decrypt/NAPI and environment closure are broader again. The independent
inventory does not expose a mirror change or relax the scope boundary.

For single-peer removal, slotSet and subtree now have AipM types. A local
guarded hoare_liftAip variant supplies table/cursor preservation for their
whole component; no per-operation frame is copied. The checked
removeByPeer_spec_tableCursor_variant and peerMakeDead_spec_tableCursor_variant
then compose existing campaign-owned exact source effects, permitting the
projected original peerRemove table claim without NodePairs or readiness.
The rootRemovePeerLists/free layer and peerRemoveAll remain pending, as does
H4's stronger initial ownership transport. This update is table-specific;
it does not settle the original request for the broader shared snapshots.

Two later bounded packages retain narrow named variants while the corresponding
retyped C1 layers are absent here. Roaming/RateLimitFrames has the three
Framing/WGCookie variants for makeCookie, ratelimiterAllow and cookieValidatePacket,
observing only the optional peer map. It adds no reply/socket layer.
Progress/BatchDrainFrames has the Device-only deliverSent_sameKernel variant
of Framing/EnvLeaves, used after the actual recorded batch completion guard.
These variants are candidates for replacement by the shared contracts on their
landing; the broader pending inventories are unchanged.

## H1: genuine reinstallation between confirmations

The proposed result concerns a finite sequence of original `consumeInitiation`,
`createResponse`, `beginSession` and `receivedWithKeypair` calls for a tracked
peer. Unlike begin/confirm alone, this admits repeated session installation.
With an initial next-slot ID below the allocation cursor, the intended claim is
that successful confirmation IDs within the sequence are distinct. This is
numeric-ID uniqueness in that operation language, not driver reachability, live
key residency, or a claim about history before the sequence. All original
rejections and errors must remain.

The required transport spans six existing structural families:

| Shared declaration | Local status |
| --- | --- |
| `Keypairs/Frames/WGBase.setPeer_spec` | Checked `Noise/RestartFrames.setPeer_spec_restart_variant` |
| `Keypairs/Frames/WGBase.peerGetMaybeZero_spec` | Checked `peerGetMaybeZero_spec_restart_variant` |
| `Keypairs/Frames/WGBase.pubkeyLookup_spec` | Checked `pubkeyLookup_spec_restart_variant` |
| `Keypairs/Frames/WGBase.peerPut_spec` | Not implemented; failed-consumer release may delete the tracked peer |
| `Keypairs/Frames/WGTransitions.consumeInitiation_spec` | Not implemented; must include every rejection after lookup |
| `Keypairs/Frames/WGTransitions.createResponse_spec` | Not implemented; must include early returns and index insertion |

`RestartModel` records the cursor and a predicate on a surviving peer's next
slot. `RestartFrames` separates preservation from claims; its pure insert/erase
facts and the three named variants are checked. No mixed executor or new H1
headline is claimed. Index-insertion transport can use campaign 2's existing
exact `indexInsert_exact` effect instead of another structural copy. Existing
session/confirmation effects support the subsequent induction.

[AGENT 2026-10-15] Defer the remaining three transports and the mixed result
pending a decision on the six-family scope. Do not treat the three completed
variants as authorization to finish the larger layer. Initial next-ID bounds
do not establish key residency: aliased releases may erase a key while its ID
remains in a slot. Bare consumer calls also retain successful lookup references;
full packet-caller cleanup is outside the proposed operation language.

## H2: data ingress and later workers

Most shared contracts here are insufficient for H2's projection, rather than
individually falsified by the index-owner change: the campaign-1 lifetime
snapshot has the keypair frontier/cells but no index table. Immediate ingress
needs nine additional operation families:

| Family | Shared declarations under `Keypairs/Frames/` |
| --- | --- |
| Rx skb allocation/update/free (three) | `WGBase.newRxSkb_sameSnapshot/spec`, `setRxSkb_sameSnapshot/spec`, `freeRxSkb_sameSnapshot/spec` |
| Device/peer Rx enqueue | `WGMore.enqueuePerDeviceAndPeerRx_sameSnapshot/spec` |
| Publication/NAPI enqueue | `WGMore.enqueuePerPeerRx_sameSnapshot`, `enqueuePerPeerRx_pure_spec` |
| Handshake CPU rotation | `WGMore.cpumaskNextOnline_sameSnapshot/spec` |
| Header handling (two) | `WGMore.validateHeaderLen_sameSnapshot/spec`, `prepareSkbHeader_sameSnapshot/spec` |
| DS-field extraction | `WGTransitions.ipTunnelGetDsfield_sameSnapshot/spec` |

Estimate: 160–230 lines of preservation support plus 70–120 lines composing
`consumeData`, `packetReceive` and `wgReceive`, subject to elaboration. Existing
campaign-2 lookup, reference/release, queue, sender and hidden-input contracts
are reusable. Enqueue publication must retain the actual
`IndexOwner.peerDeref (.keypair …)` path and its missing-owner/NULL outcomes;
packet peer identity must not be substituted for the embedded owner word.

Decrypt/NAPI continuation is larger again: decrypt, receive freshness/statistics,
allowed-IP lookup, receive timer hooks, endpoint installation, packet/ECN
classification and receive completion overlap `OrdinaryHot`, `WGBase`,
`WGMore`, `WGTransitions` and `Evolution/Observers`. Preliminary preservation
estimate: another 250–400 lines, plus substantive worker/loop composition.
Full environment closure needs its own scheduler inventory and explicit
preservation conditions for callbacks. It is not a small follow-on to ingress.

Genuinely new invariant connections include confirmation's release/filtering
effect and preservation of index/cursor fields during replay-counter validation;
the latter does not require proving the counter-window invariant. Neither
establishes owner residency or peer-word coherence by itself.

[AGENT 2026-10-15] Defer these additional structural variants pending the user's
scope decision. No ingress variant from this inventory has been implemented.
Do not divide the same planned layer into batches to evade the boundary.

## H4: initial assumptions for remove-all

Transporting node shape and listed-peer residency through `free` would move the
existing remove-all contract's assumptions from the actual post-free cut to
the initial device. It would also preserve the selected peer list and establish
root reset/sequence increment. The missing `subtree`, `rootRemovePeerLists` and
`free` families are already in the original six-family request. Renaming them
as H4 frames would not remove that overlap; general transport remains deferred.

This would still be a normal-return contract. Node shape alone gives neither
acyclicity nor traversal completion, and free need not erase unreachable nodes.
The checked post-free contract and flag-only REPLACE_PEERS composition remain
valid with their explicit scope.

Recommendation: defer the larger preservation layers until the state split,
unless the user authorizes specific local variants sooner. Continue independent
claims in the existing projection; delete structural frames made unnecessary
by the narrowed types when the split lands.

## H3: bad-MAC2 cookie-reply continuation

The actual non-cookie receiver's loaded/noCookie branch replies for initiation
and response types without running either authenticated consumer or endpoint
setter. A whole-call remote-preservation claim still needs the actual reply:
the no-cache socket path may transmit, consume hidden records, update routing
and device transmit statistics, but its cache-free branches do not write peers.

The missing shared overlap is six operation families in Keypairs/Frames:
WGBase.tunnelXmit_sameSnapshot, send4_sameSnapshot and send6_sameSnapshot;
WGMore.cookieMessageCreate_sameSnapshot, sendBufferAsReplyToSkb_sameSnapshot
and sendHandshakeCookie_sameSnapshot. C1's snapshot deliberately omits remote
endpoints, so those contracts cannot directly supply the stronger peer-map
observation. Existing campaign cookie-secret and endpoint-extraction contracts
cover their corresponding leaves. The no-cache/false-exactRx restriction removes
the cache mutation and loopback callback obligations, but the outer compositions
still span these six shared families.

[AGENT 2026-10-17] Keep this overlap inventoried pending the user's scope
decision. One architecture derives peer-map preservation through the six native
operations; a second specializes the whole reply source directly to no cache
and lax NET_RX, avoiding general socket support but duplicating the same shared
control flow. Neither is implemented as a way to divide the overlap into smaller
batches. This is a proof-support dependency, not a mirror-change request.

## H6: allocation serials across complete response callers

The checked session-arm observations identify the serial at the actual
beginSession cut. Relating consecutive complete caller executions requires
the allocation-counter origin at that cut and its preservation through every
other part of the caller. A normal outgoing call would then have final counter
equal to entry counter plus one exactly when the observed session began.
Stopped calls can allocate before failing; no returned-state delta is claimed
for them.

The missing outgoing counter-preservation sites are createResponse,
addMacToPacket, dstCacheGet, dstCacheReset, tunnelXmit, send4, send6 and
sendBufferToPeer: eight substantive sites. Existing native Ambient/Index
adapters, whole-WireGuard loopback preservation, ordinary access operations and
the exact timer effects cover the remaining components. Exposing the owned
routing adapter unchanged is possible; it does not discharge the eight sites.

Incoming response handling adds load handling, cookie generation/validation
and ratelimiting, cookie reply, lookup/consumer/release, endpoint publication
and the staged/keepalive/data/fallback path. That is a larger shared-layer
overlap, not another small leaf contract.

Two architectures were audited. Compositional native counter frames combine
with the existing exact observer factors and retain arbitrary states and
errors. Expanding the complete source instead duplicates the same eight
outgoing obligations and the incoming subtrees inline; it does not reduce the
overlap. Campaign 1's lifetime observer uses its allocation invariant and does
not directly supply this arbitrary-entry fact.

[AGENT 2026-10-17] Keep the complete-call layer inventoried rather than copy it.
Proceed only with the independently useful outgoing prefix-origin contract:
two counter variants of WGTransitions.createResponse_spec and addMacToPacket_spec, one actual prefix
bridge, one projected full-call observation claim and its literal headline.
This anchors a reached session event to the actual call's entry counter.
It does not claim final-call preservation or cross-call serial uniqueness,
and is not a first installment of the eight-site copy. The larger overlap
remains for a scope decision or shared support. This is a proof-support
dependency, not a mirror-change request.


The bounded prefix-origin package is now checked: SessionOriginFrames contains
createResponse_spec_counter_variant and addMacToPacket_spec_counter_variant;
Source/Claims and the literal terminal connect them to the original full caller.
Its five declarations do not implement the larger suffix layer.

The incoming audit identifies responseLoad; makeCookie, ratelimiterAllow,
cookieValidatePacket and cookieMessageCreate; sendBufferAsReplyToSkb and
sendHandshakeCookie; responseWithLookup/consumeResponse, indexLookup and
peerPut; setPeerEndpointFromSkb; and the staged path's sendKeepalive,
sendStagedPackets, createData, enqueuePerDeviceAndPeer, enqueuePerPeerTx,
sendQueuedHandshakeInitiation, keypairGet, peerGet and cpumaskChooseOnline.
The socket helpers also need their cache-free instantiations. Existing
keypairPut_counter, ECN/crypto and exact timer effects are reusable; the Skb
component needs one generic guarded adapter rather than copies for each leaf.
This inventory is not an implementation or a request to change the mirror.
