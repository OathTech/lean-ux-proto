import Leanux.Proofs.WG.Roaming.Basic
import Leanux.Proofs.WG.Noise.ConsumeEdges
import Leanux.WG.RxData

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Decryption itself preserves the outer source and packet ownership,
and successful plaintext is precisely the AEAD result under the receiving
key read from the specified resident keypair. No source-address binding is
asserted: the actual call has empty associated data. -/
theorem decryptPacket_authenticated (pkt : RxPacket) (key : Keypair) :
    Ensures (decryptPacket pkt)
      (fun w => (w.k.wg.bind fun d => d.keypairs[pkt.keypair]?) = some key)
      (fun result _ => ∀ plain, result = some plain →
        plain.source = pkt.source ∧ plain.peer = pkt.peer ∧ plain.keypair = pkt.keypair ∧
        plain.nonce = u64le pkt.bytes 8 ∧
        aeadDecrypt key.receiving.key (counterNonce (u64le pkt.bytes 8))
          (pkt.bytes.drop 16) [] = some plain.bytes) := by
  rw [ensures_iff]
  have hh := hiddenClock64_kernel_spec (fun _ => True)
  have ha := unconstrained_prefix (hiddenAlloc .skbCowDataRx)
  mvcgen [decryptPacket, Leanux.WG.orM, branchExpired, birthdateTest,
    getKeypair, getDev, getK, setKeypair, modifyDev, modifyK,
    branch, branchCmp, invariant, hh, ha]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals grind only

end Leanux.Proofs.WG.Roaming
