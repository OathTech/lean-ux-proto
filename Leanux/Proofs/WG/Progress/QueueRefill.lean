import Leanux.Proofs.WG.Progress.BatchBacklog
/-! A constructed initialized execution prefix whose nested receive callback
refills the encrypt queue. It stops at the occupancy budget, not by divergence.
The operation's completion suffix is deliberately not claimed here. -/
namespace Leanux.Proofs.WG.Progress.QueueRefill
open Leanux Leanux.Runner Leanux.Proofs.WG.Progress
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000
def c (n : Nat) := word (n * 1000000000)
def j (n : Nat) := recAt .jiffiesEnd (word (100000+n))
def start (w : Worker) := recAt (.sectionStart w) (word 0 ++ word 0)
def stop (w : Worker) := recAt (.sectionStop w) (word 0)
def rows : Array (List HiddenRecord) := #[
 [recAt .resetLastSent (c 100), j 0],
 [recAt .birthdateExpired (c 101), start .sendWorker, recAt .birthdateExpired (c 101),
 recAt .initLastSent (c 101), recAt .initEphemeral (List.range 32 |>.map fun n => UInt8.ofNat (129+n)),
 recAt .tai64nNow [128,59,177,106,0,0,0,0,177,104,222,58,0,0,0,0],
 recAt .indexDraw [13,12,11,10,0,0,0,0], recAt .initLastSentAgain (c 101),
 start .netRx, stop .netRx, recAt .retransmitJitter [200,0,0,0,0,0,0,0], stop .sendWorker, j 1],
 [j 2],
 [start .netRx, stop .netRx, start .receiveWorker, recAt .deriveKeysBirthdate (c 102),
 recAt .walltimeLastHandshake (word 102 ++ word 0), recAt .birthdateExpired (c 102),
 stop .receiveWorker, start .encryptWorker, stop .encryptWorker, start .txWorker,
 start .netRx, stop .netRx, recAt .birthdateExpired (c 102), stop .txWorker, j 3],
 [start .netRx, stop .netRx, recAt .birthdateExpired (c 103), start .decryptWorker,
 recAt .birthdateExpired (c 103), recAt .reschedDecrypt (word 0), start .encryptWorker,
 start .netRx, recAt .birthdateExpired (c 103), recAt .birthdateExpired (c 103),
 stop .netRx, stop .encryptWorker]]
/-- The ordinary fixture and first three operations of w6_rst_syn, followed
by the response and a batch combining its encrypted [4, 0, 0, 0, 13, 12, 11, 10, 0, 0, 0, 0, 0, 0, 0, 0, 151, 59, 249, 8, 60, 214, 64, 116, 153, 153, 232, 164, 5, 184, 250, 173, 217, 172, 85, 92, 36, 218, 84, 212, 206, 225, 135, 74, 238, 230, 117, 48, 232, 201, 54, 200, 128, 253, 149, 13, 155, 64, 238, 215, 215, 247, 227, 148, 240, 184, 96, 158, 195, 65, 92, 238, 7, 210, 65, 105, 60, 236, 154, 126] with one transmit. -/
def concreteTrace : Trace :=
  { id := "campaign2-encrypt-refill",
    ops := #[
      .wgSet {
        privateKey := some (List.replicate 32 17), listenPort := some 51820,
        peers := some [.attrs {
          publicKey := some [15, 170, 104, 78, 210, 136, 103, 185, 127, 74, 106, 45, 238, 93, 248, 206, 151, 78, 118, 183, 1, 142, 63, 34, 161, 196, 207, 38, 120, 87, 15, 32],
          endpoint := some { len := 16, family := 2, addr := 0x7f000001, port := 51999 },
          keepalive := some 25,
          allowedIps := some [
            .attrs { family := some 2, addr := some 0x0a000000, addrLen := 4, cidr := some 8 },
            .attrs { family := some 10, addr := some 0x20010db8000000000000000000000000,
                     addrLen := 16, cidr := some 32 }] }] },
      .wgUp, .wgObserve,
      .wgInject 4 51820 [2, 0, 0, 0, 4, 3, 2, 1, 13, 12, 11, 10, 255, 46, 228, 86, 1, 236, 27, 103, 49, 12, 119, 144, 64, 69, 133, 174, 105, 115, 49, 238, 225, 193, 248, 207, 36, 25, 115, 28, 31, 255, 62, 107, 197, 10, 34, 61, 134, 184, 168, 107, 244, 26, 43, 211, 161, 171, 132, 248, 146, 253, 155, 172, 188, 69, 189, 164, 109, 192, 37, 230, 202, 198, 101, 165, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0 false 0,
      .wgBatch [.inject 4 51820 [4, 0, 0, 0, 13, 12, 11, 10, 0, 0, 0, 0, 0, 0, 0, 0, 151, 59, 249, 8, 60, 214, 64, 116, 153, 153, 232, 164, 5, 184, 250, 173, 217, 172, 85, 92, 36, 218, 84, 212, 206, 225, 135, 74, 238, 230, 117, 48, 232, 201, 54, 200, 128, 253, 149, 13, 155, 64, 238, 215, 215, 247, 227, 148, 240, 184, 96, 158, 195, 65, 92, 238, 7, 210, 65, 105, 60, 236, 154, 126],
        .xmit 4 0x0a000001 [1] {}] 100],
    dstCacheRecords := false, hidden := some rows }

def rejectedAtOccupancyBound : Bool :=
  match executeTrace concreteTrace with
  | .error (op, .invariant msg) => op == 4 && msg ==
      "wg_packet_encrypt_worker consumed more items than its queue held (1) in one run"
  | _ => false

/-- Executable reproduction; the full initialized prefix is not claimed as
a kernel-reduction theorem. Failure to reproduce is an explicit error. -/
def reproduce : IO Unit :=
  if rejectedAtOccupancyBound then
    IO.println "Reproduced operation 4 encrypt occupancy-budget invariant"
  else throw (IO.userError "encrypt refill finding did not reproduce")

#eval reproduce

end Leanux.Proofs.WG.Progress.QueueRefill
