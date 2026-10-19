import Leanux.Proofs.WG.RetirementSecurity.TxWorkHandshakeReceive

/-! Native handshake helper frames retain suspended scheduler activations.
Every ambient leaf is checked at its source; no arbitrary ambient action is
admitted as a frame. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

theorem index_bucket (index : Nat) : Keeps (indexBucket index) := by
  suspension_source [indexBucket] using []

theorem index_bucket_call (index : Nat) : Keeps (monadLift (indexBucket index) : WG.M (List IndexEntry)) :=
  index_lift (index_bucket index)

theorem index_insert (owner : IndexOwner) : Keeps (indexInsert owner) := by
  unfold indexInsert
  index_unfold _private.Leanux.WG.Peer.«0».Leanux.WG.unhashEntry
  index_unfold _private.Leanux.WG.Peer.«0».Leanux.WG.bucketHas
  suspension_source [] using [branch,index_bucket,record_budget,hidden,unsupported,exhausted]

theorem index_insert_call (owner : IndexOwner) : Keeps (monadLift (indexInsert owner) : WG.M Nat) :=
  index_lift (index_insert owner)

theorem index_replace (pid kid : Nat) : Keeps (indexReplaceHandshake pid kid) := by
  suspension_source [indexReplaceHandshake,indexHashed] using [branch]

theorem index_replace_call (pid kid : Nat) : Keeps (monadLift (indexReplaceHandshake pid kid) : WG.M Bool) :=
  index_lift (index_replace pid kid)

theorem owner_set (owner : IndexOwner) (value : Option PeerId) : Keeps (owner.setPeerWord value) := by
  cases owner <;> suspension_source [IndexOwner.setPeerWord] using [peer,set_peer,key,set_key]

theorem index_lookup (kinds : List IndexKind) (index : Nat) : Keeps (indexLookup kinds index) := by
  suspension_source [indexLookup] using [index_bucket_call,branch,owner_word,owner_set,peer_get_maybe,invariant]

theorem pubkey_lookup (key : Key) : Keeps (pubkeyLookup key) := by
  suspension_source [pubkeyLookup] using [device,peer_get_maybe,branch]

theorem noise_kdf (second third : Bool) (chain data : List UInt8) : Keeps (kdf second third chain data) := by
  suspension_source [kdf,WG.orM] using [branch]

theorem noise_output (outs : List (List UInt8)) (i : Nat) : Keeps (kdfOut outs i) := by
  suspension_source [kdfOut] using [invariant]

theorem noise_ephemeral (copy : Bool) (e chain hash : List UInt8) : Keeps (messageEphemeral copy e chain hash) := by
  suspension_source [messageEphemeral] using [branch,noise_kdf,noise_output]

theorem noise_dh (wantKey : Bool) (chain priv pub : List UInt8) : Keeps (mixDh wantKey chain priv pub) := by
  suspension_source [mixDh] using [branch,noise_kdf,noise_output]

theorem noise_precomputed (chain dh : List UInt8) : Keeps (mixPrecomputedDh chain dh) := by
  suspension_source [mixPrecomputedDh] using [branch,noise_kdf,noise_output]

theorem noise_decrypt (sealed key hash : List UInt8) : Keeps (messageDecrypt sealed key hash) := by
  suspension_source [messageDecrypt] using [branch,invariant]

theorem public_key (secret : List UInt8) : Keeps (generatePublic secret) := by
  suspension_source [generatePublic] using [branch]

theorem create_initiation (pid : PeerId) : Keeps (createInitiation pid) := by
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  suspension_source [] using [device,branch,peer,set_peer,hidden,public_key,invariant,noise_ephemeral,
    noise_dh,noise_precomputed,owner_deref,index_insert_call]

theorem create_response (pid : PeerId) : Keeps (createResponse pid) := by
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  suspension_source [] using [peer,set_peer,branch,hidden,public_key,invariant,noise_ephemeral,
    noise_dh,noise_kdf,noise_output,owner_deref,index_insert_call]

theorem consume_initiation (msg : List UInt8) : Keeps (consumeInitiation msg) := by
  suspension_source [consumeInitiation,WG.orM] using [device,branch,peer,set_peer,peer_put,clock,compare,
    noise_ephemeral,noise_dh,noise_precomputed,noise_decrypt,pubkey_lookup,invariant]

theorem consume_response (msg : List UInt8) : Keeps (consumeResponse msg) := by
  suspension_source [consumeResponse] using [device,branch,peer,set_peer,peer_put,index_lookup,
    noise_ephemeral,noise_dh,noise_kdf,noise_output,noise_decrypt,invariant]

theorem add_mac (pid : PeerId) (msg : List UInt8) : Keeps (addMacToPacket pid msg) := by
  suspension_source [addMacToPacket,WG.andM] using [peer,set_peer,branch,expired]

theorem handshake_zero (pid : PeerId) : Keeps (handshakeZero pid) := by
  suspension_source [handshakeZero] using [peer,set_peer]

theorem handshake_clear (pid : PeerId) : Keeps (handshakeClear pid) := by
  suspension_source [handshakeClear] using [owner_deref,index_remove_lift,handshake_zero]

theorem key_clear (pid : PeerId) : Keeps (keypairsClear pid) := by
  unfold keypairsClear
  simp only [modifyPeer_source]
  suspension_source [] using [peer,set_peer,key_put]

theorem key_create (owner : Option PeerId) : Keeps (keypairCreate owner) := by
  suspension_source [keypairCreate] using [allocation,branch,device,modify_device,set_key]

theorem key_rotate (pid kid : Nat) : Keeps (addNewKeypair pid kid) := by
  unfold addNewKeypair
  simp only [modifyPeer_source]
  suspension_source [] using [peer,set_peer,key,branch,key_put]

theorem key_derive (kid : KeypairId) (initiator : Bool) (chain : List UInt8) : Keeps (deriveKeys kid initiator chain) := by
  suspension_source [deriveKeys] using [clock,noise_kdf,noise_output,key,set_key]

theorem session (pid : PeerId) : Keeps (beginSession pid) := by
  suspension_source [beginSession,WG.andM] using [peer,key,set_key,branch,owner_word,key_create,
    key_derive,handshake_zero,key_rotate,owner_deref,index_replace_call,invariant,unsupported]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension
