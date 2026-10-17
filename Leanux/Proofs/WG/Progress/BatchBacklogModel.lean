import Leanux.Runner

set_option synthInstance.maxSize 1024
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.Runner

def recAt (site : HiddenSite) (bytes : List UInt8) : HiddenRecord :=
  { site := site.info.id, bytes }

def word (n : Nat) : List UInt8 :=
  (List.range 8).map fun i => UInt8.ofNat (n / 256 ^ i % 256)

def cookie64 : List UInt8 := [3, 0, 0, 0] ++ List.replicate 60 0
def upRecords : List HiddenRecord :=
  [recAt .udpPortDraw (word 0), recAt .jiffiesEnd (word 100)]
def batchRecords : List HiddenRecord :=
  [recAt (.sectionStart .netRx) (word 0 ++ word 0),
   recAt (.queued .receiveWorker) (word 1 ++ word 0),
   recAt (.sectionStop .netRx) (word 0), recAt .jiffiesEnd (word 101)]
def pendingTrace : Trace :=
  { id := "campaign2-pending-handshake", ops := #[.wgUp, .wgBatch [.inject 4 32768 cookie64] 100],
    armRecords := true, hidden := some #[upRecords, batchRecords] }

end Leanux.Proofs.WG.Progress
