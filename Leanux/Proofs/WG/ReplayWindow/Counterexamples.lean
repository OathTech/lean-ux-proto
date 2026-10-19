import Leanux.Runner

/-! A counterexample to the predecessor's arbitrary-World nonreceive
classification, carried to the split mirror without changing the witnessed behavior. -/
namespace Leanux.Proofs.WG.ReplayWindow.Counterexamples
open Leanux

/-- A ready keepalive and an uncrypted packet share a retained keypair lifetime.
The second packet makes the placeholder scheduler dispatch a decrypt activation. -/
def world : World :=
  let src : WG.SkbSource := { family := 4, saddr := 0, sport := 0, daddr := 0, iif := 0 }
  let peer : WG.Peer :=
    { remoteStatic := [], presharedKey := [], precomputedStaticStatic := [],
      internalId := 1, refcount := 4, endpoint := some { family := WG.AF_INET, addr := 0, port := 0 },
      keypairCurrent := some 1, rxQueue := { items := [1, 2] }, napiScheduled := true }
  let keypair : WG.Keypair := { internalId := 1, peer := some 1, refcount := 3 }
  let ready : WG.RxPacket := { peer := 1, keypair := 1, nonce := 0, bytes := [], source := src, state := .crypted }
  let device : WG.Device :=
    { ifindex := 3, ifname := "wg0", running := true,
      peers := Std.TreeMap.ofList [(1, peer)], peerList := [1],
      keypairs := Std.TreeMap.ofList [(1, keypair)], nextKeypairId := 2,
      rxSkbs := Std.TreeMap.ofList [(1, ready), (2, { ready with state := .uncrypted })],
      nextSkb := 3, decryptQueue := (WG.PtrRing.init WG.MAX_QUEUED_PACKETS).produce 2 }
  { tasks := Runner.initialTasks 1024, fs := Runner.initialFS true,
    wg := { Runner.initialWG true with dev := some device, keypairCounter := 1 },
    ambient := { env := Runner.harnessEnv, timing := Env.timing, hiddenPlaceholders := true } }

/-- Result, surviving lifetime, reference count, high-water mark, first bitmap word. -/
def result : Option (Int × Nat × Nat × Nat × Nat) := do
  let (ret, next) ← ((Leanux.syscall (.wgAdvance 0)).run world).toOption
  let device ← next.wg.dev
  let keypair ← device.keypairs.get? 1
  let word ← keypair.receivingCounter.backtrack[0]?
  pure (ret, keypair.internalId, keypair.refcount, keypair.receivingCounter.counter, word)

#guard ((world.wg.dev.bind (·.keypairs.get? 1)).map (fun k => (k.internalId, k.receivingCounter.counter))) == some (1, 0)
#guard result == some (0, 1, 1, 1, 2)

end Leanux.Proofs.WG.ReplayWindow.Counterexamples
