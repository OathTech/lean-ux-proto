# Campaign 2: outer-removal frame request

The next H2 increment would prove table/index-cursor safety through original
`peerRemove` and `peerRemoveAll`, assuming only initial `View.TablesSafe`.
These are normal-return preservation claims, not termination, trie correctness,
owner residency or whole-driver coherence claims. No mirror change is requested.

The existing campaign-1 snapshot omits the index table and allocation cursor.
Its preservation lemmas therefore cannot be projected to this property. After
reusing campaign-2 effects for `setNode`, `freeNode` and `listDel`, six original
operation families still need local variants:

| Operation | Shared declarations in `WG/Keypairs/Frames/WGBase.lean` |
| --- | --- |
| `slotSet` | `slotSet_sameSnapshot`, `slotSet_spec` |
| `removeByPeer` | `removeByPeer_sameSnapshot`, `removeByPeer_spec` |
| `peerMakeDead` | `peerMakeDead_sameSnapshot`, `peerMakeDead_spec` |
| `subtree` | `subtree_sameSnapshot`, `subtree_spec` |
| `rootRemovePeerLists` | `rootRemovePeerLists_sameSnapshot`, `rootRemovePeerLists_spec` |
| `free` | `free_sameSnapshot`, `free_spec` |

The two substantive caller compositions also correspond to campaign-1's
`WGMore.peerRemove_ordinary/spec` and `peerRemoveAll_ordinary/spec`.
New proofs would preserve the original guards, bounded loops and stopped
outcomes. They would live in `Index/AllowedIpFrames.lean` and
`Index/RemovalSource.lean`, with public projected claims in `Statements.lean`;
no existing shared file would change. Estimated support is 150–220 lines,
subject to elaboration. Variants would name the shared declarations they replace.

[AGENT 2026-10-15] Treat these six structural families as exceeding the user's
“more than a few shared lemmas” boundary. The full increment is deferred pending
that decision; no variants have been written. Narrowing the property or inlining
the same reasoning does not remove the overlap. Continue independent campaign
work meanwhile. This is a proof-support request, not a mirror defect.

Alternatives considered: existing configuration removal converses require
`NodePairs`, which would add an unnecessary shape premise to H2; existing source
factor equations do not prove preservation. Single-peer removal needs only three
of the structural families, but splitting the six across increments would not
resolve the authorization question for the planned full closure.

Recommendation: defer this outer-removal increment until the state split, whose
narrowed allowed-IP types may eliminate much of this preservation work. If the
user instead authorizes the six local variants now, retain separate frame files
and delete any frames made trivial or unstatable when retyping after the split.
The rest of H2 and the other results remain available to work on.
