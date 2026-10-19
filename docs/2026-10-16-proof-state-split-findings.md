# State-split retrofit: observer findings and reproducers

These are checked differences between obsolete proof-side source copies and the
current mirror. They are unrestricted-state or callback examples, not initialized
security failures or Linux-defect claims. The mirror was not edited. The carried
observers follow its actual calls and retain exact erasure; their dependent
terminal results remain subject to the full proof gate.

Each displayed endpoint proof passed with standard axioms only. Failed earlier
probes and their recovery output are not evidence. Commands regenerate the
examples from source; no traces or logs are stored here. Build the imported
proof module first where applicable. The [retrofit report](2026-10-16-proof-state-split.md)
records the current status and unresolved runtime witnesses.

For snippets without their own wrapper:

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
# Feed a Lean snippet to:
cap scripts/in-bundle lake env lean -j1 --stdin
~~~

## Timer placement

The old expiry-only observer leaves no wheel entry. Actual armTimer installs slot 2, bucket expiry 2 and enqueue stamp 1 at delay 1. Native timer observers now follow wheel placement, clock/dispatch records, detach and clearing.

~~~sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env lean -j1 --stdin <<'LEAN'
import Leanux.Runner
open Leanux Leanux.WG
private def witnessPeer : Peer :=
  { remoteStatic := [], presharedKey := [], precomputedStaticStatic := [], internalId := 1 }
private def witnessWorld : WGWorld :=
  { dev := some { ifindex := 4, ifname := "wg0", peers := Std.TreeMap.ofList [(0, witnessPeer)] } }
private def witnessAmbient : Ambient := { env := Runner.harnessEnv, timing := Env.timing }
private def wheelAfter (a : WG.M Unit) : Option (Option (Nat × UInt64 × Nat)) := do
  let ((_, w), _) ← ((a.run witnessWorld).run witnessAmbient).toOption
  let d ← w.dev
  let p ← d.peers[0]?
  pure ((p.wheel .newHandshake).map fun e => (e.slot, e.bucketExpiry, e.enqueued))
theorem currentArmWheel : wheelAfter (armTimer 0 .newHandshake 1) = some (some (2, 2, 1)) := by
  decide +kernel
theorem obsoleteExpiryOnlyWheel : wheelAfter (do
    let p ← getPeer 0
    setPeer 0 (p.setTimer .newHandshake (some 1))) = some none := by
  decide +kernel
#print axioms currentArmWheel
#print axioms obsoleteExpiryOnlyWheel
LEAN
~~~


## Encrypt ring callback order

On an empty one-slot ring, a callback enqueues an empty batch. Actual encryption consumes and installs the ring before the callback, returning no item and retaining the queued batch. The obsolete callback-first copy returns that batch and leaves the ring empty. The cut, worker and history observers now follow the actual order.

~~~sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env lean -j1 --stdin <<'LEAN'
import Leanux.WG.Data
open Leanux Leanux.WG
private def start : WGWorld :=
  {dev := some {ifindex := 3, ifname := "wg0", encryptQueue := PtrRing.init 1}}
private def input : Ambient := {env := fun _ _ => true, timing := ⟨0,0⟩}
private def callback : WG.M Unit := modifyDev fun d => {d with encryptQueue := d.encryptQueue.produce []}
private def oldPoll : WG.M (Option (List SkbId)) := do
  let d ← getDev
  match d.encryptQueue.consume with
  | (none, _) => _ ← branch .encWorkerConsumed false; return none
  | (some item, ring) =>
    _ ← branch .encWorkerConsumed true
    modifyDev fun d => {d with encryptQueue := ring}
    return some item
private def oldFactor : WG.M (Option (List SkbId)) := do callback; oldPoll
private def observe (a : WG.M (Option (List SkbId))) :
    Except Stop (Option (List SkbId) × Option (Option (List SkbId)) × List Bool) :=
  ((a.run start).run input).map fun (out : (Option (List SkbId) × WGWorld) × Ambient) =>
    (out.1.1, out.1.2.dev.map (fun (d : Device) => d.encryptQueue.peek),
      out.2.steps.toList.map (fun (s : Step) => s.outcome))
theorem currentOrder :
    observe (encryptRingPoll callback) = .ok (none, some (some []), [false]) := by
  rfl
theorem obsoleteOrder :
    observe oldFactor = .ok (some [], some none, [true]) := by
  rfl
#print axioms currentOrder
#print axioms obsoleteOrder
LEAN
~~~


## Handshake queue bookkeeping

The actual send queue receives peer 0 without changing queuedThisCall. The obsolete observer also wrote queuedThisCall. Current maintenance observers preserve the source sequence.

~~~sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env lean -j1 --stdin <<'LEAN'
import Leanux.Runner
open Leanux Leanux.WG
private def queuePeer : Peer :=
  {remoteStatic := [], presharedKey := [], precomputedStaticStatic := [],
   internalId := 1, lastSentHandshake := -6000000000}
private def queueWorld : WGWorld :=
  {dev := some {ifindex := 4, ifname := "wg0",
    peers := Std.TreeMap.ofList [(0, queuePeer)]}}
private def queueAmbient : Ambient :=
  {env := Runner.harnessEnv, timing := Env.timing,
   hidden := some [{site := HiddenSite.birthdateExpired.info.id,
    bytes := List.replicate 8 0}]}
private def obsoleteQueue : WG.M Unit := do
  if ← branch .queuedNotRetry true then
    setPeer 0 {(← getPeer 0) with timerHandshakeAttempts := 0}
  let p ← getPeer 0
  if ← branchExpired .queuedNotExpired p.lastSentHandshake REKEY_TIMEOUT not then return
  if ← branch .queuedDead p.isDead then return
  peerGet 0
  if ← branch .queuedAlreadyQueued p.handshakePending then
    peerPut (some 0)
    return
  setPeer 0 {(← getPeer 0) with handshakePending := true}
  recordQueued .sendWorker 0
  modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [0]}
  modify fun w => {w with queuedThisCall := 0 :: w.queuedThisCall}
private def queueResult (a : WG.M Unit) : Option (List PeerId × List PeerId) := do
  let ((_, w), _) ← ((a.run queueWorld).run queueAmbient).toOption
  let d ← w.dev
  pure (d.sendWorkQueue, w.queuedThisCall)
theorem actualQueueResult :
    queueResult (sendQueuedHandshakeInitiation 0 false) = some ([0], []) := by
  decide +kernel
theorem obsoleteQueueResult :
    queueResult obsoleteQueue = some ([0], [0]) := by
  decide +kernel
#print axioms actualQueueResult
#print axioms obsoleteQueueResult
LEAN
~~~


## Peer hash decision

The old peerMakeDead copy omitted the getter and pubkeyRemoveHashed decision. The actual call emits the decision even when AllowedIPs is empty. Configured identity and AllowedIPs observers now retain it.

~~~sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env lean -j1 --stdin <<'LEAN'
import Leanux.Proofs.WG.Lifetimes.AllowedIpsAccess
import Leanux.Runner
open Leanux Leanux.WG Leanux.Proofs.WG.Lifetimes
private def nodePeer : Peer :=
  {remoteStatic := [], presharedKey := [], precomputedStaticStatic := [], internalId := 1}
private def nodeWorld : WGWorld :=
  {dev := some {ifindex := 4, ifname := "wg0", peers := Std.TreeMap.ofList [(0, nodePeer)],
                peerHashtable := [([], 0)]}}
private def nodeAmbient : Ambient := {env := Runner.harnessEnv, timing := Env.timing}
private def obsoleteMakeDead : WG.M Unit := do
  modifyDev (deadPeerList 0)
  removeByPeer 0
  modifyDev (deadPeerHashtable 0)
  setPeer 0 {(← getPeer 0) with isDead := true}
private def stepResult (a : WG.M Unit) : Option (List (Decision × Bool)) :=
  (((a.run nodeWorld).run nodeAmbient).toOption).map
    (fun out => out.2.steps.toList.map (fun step => (step.decision, step.outcome)))
theorem actualMakeDeadSteps : stepResult (peerMakeDead 0) =
    some [(.removeListEmpty, true), (.pubkeyRemoveHashed, true)] := by
  decide +kernel
theorem obsoleteMakeDeadSteps : stepResult obsoleteMakeDead =
    some [(.removeListEmpty, true)] := by
  decide +kernel
#print axioms actualMakeDeadSteps
#print axioms obsoleteMakeDeadSteps
LEAN
~~~


## Parser placement bound

The obsolete proof-side parser factor bounded NAPI placement entries by eight. The parser bounds them by consumed NET_RX section starts. One placement with no recorded section distinguishes the two; the factor now follows the actual count.

~~~sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 python3 - <<'PY'
import subprocess,sys
old=subprocess.check_output(['git','show','91a07ea:Leanux/Proofs/WG/Configuration/ParserShape.lean'],text=True)
fragment=old[old.index('private abbrev source_field'):old.index('private theorem traceSource_eq')]
lean='''import Leanux.Proofs.WG.Configuration.PeerTailRouting
open Lean Leanux Leanux.WG Leanux.Runner
namespace ParserPlacementProbe
private def parseOperation := pinned_const _private.Leanux.Runner.«0».Leanux.Runner.parseOperation
'''+fragment+'''
private def specimen : Json := Json.mkObj [
  ("version", toJson (1 : Nat)), ("id", toJson "placement_probe"),
  ("ops", Json.arr #[Json.mkObj [("op", toJson "pipe2"), ("flags", toJson (0 : Nat))]]),
  ("napi_irq_before_put", Json.arr #[Json.bool false])]
theorem actual_rejects : (Runner.parseTrace specimen).isOk = false := by
  decide +kernel
theorem obsolete_accepts : (traceSource specimen).isOk = true := by
  decide +kernel
#print axioms actual_rejects
#print axioms obsolete_accepts
end ParserPlacementProbe
'''
r=subprocess.run(['capped','--','scripts/in-bundle','lake','env','lean','-j1','--stdin'],input=lean,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
print(r.stdout);sys.exit(r.returncode)
PY
~~~


## IPv4 neighbor classification

The obsolete IPv4 send tail skipped neighbor classification. For this empty packet and one-route specimen, it leaves the neighbor list empty; the actual tail adds the neighbor. The current factor includes the FIB generation, socket namespace, both lookups and classification.

~~~sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env lean -j1 --stdin <<'LEAN'
import Leanux.Proofs.WG.Lifetimes.SocketSend4
open Leanux Leanux.WG Leanux.Proofs.WG.Lifetimes
namespace SocketFactorWitness
def w : WGWorld := {dev := some {ifindex := 3, ifname := "wg0", sock4 := some 51820}}
def a : Ambient := {env := fun _ _ => false, timing := {advanceWait := 0, traceBound := 0}}
def ep : Endpoint := {family := AF_INET, addr := LOOPBACK4, port := 51821}
def rt : Route := {dev := 1, src := LOOPBACK4}
def oldFinish (e : Endpoint) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (route : Option Route) : WG.M Int := do
  let some r := route | invariant "send4 without a route"
  (pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx
  return 0
def outcome (x : WG.M Int) : Option (Int × List (Bool × Nat × Nat)) :=
  match (x.run w).run a with
  | .error _ => none
  | .ok ((n, w'), _) => some (n, w'.routing.neighbours)
theorem old_result : outcome (oldFinish ep [] 0 false (some rt)) = some (0, []) := by decide +kernel
theorem current_result : outcome (send4FinishSource ep [] 0 false (some rt)) =
    some (0, [(false,1,3)]) := by decide +kernel
theorem differs : outcome (oldFinish ep [] 0 false (some rt)) ≠
    outcome (send4FinishSource ep [] 0 false (some rt)) := by
  rw [old_result, current_result]
  decide
#print axioms old_result
#print axioms current_result
#print axioms differs
end SocketFactorWitness
LEAN
~~~


## Zero-key requeue

A recorded queue event can describe requeueing while the earlier entry remains represented. The obsolete observer repaid the acquired reference. The source instead consumes the record, keeps the acquisition and appends the peer again. The timer observer now retains this distinction.

~~~sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env lean -j1 --stdin <<'LEAN'
import Leanux.WG.Timers
open Leanux Leanux.WG
namespace ZeroQueueObserverWitness
def peer : Peer := {remoteStatic := [], presharedKey := [], precomputedStaticStatic := [], internalId := 1}
def initial : WGWorld := {dev := some {ifindex := 3, ifname := "wg0", peers := ({} : Std.TreeMap Nat Peer).insert 0 peer, clearWorkQueue := [0]}}
def ambient : Ambient := {env := fun _ _ => true, timing := ⟨0,0⟩, armRecords := true, unitPeers := [(1, Worker.clearPeerWorker.index, 0)], hidden := some [{site := (HiddenSite.queued .clearPeerWorker).info.id, bytes := [1] ++ List.replicate 15 0}]}
def obsolete : WG.M Unit := do
  if ← branch .zeroKeyAlive !(← getPeer 0).isDead then
    peerGet 0
    if ← branch .zeroKeyAlreadyQueued ((← getDev).clearWorkQueue.contains 0) then
      peerPut (some 0)
    else
      recordQueued .clearPeerWorker 0
      modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue ++ [0]}
def observe (a : WG.M Unit) : Option (List PeerId × Option Nat × Nat) :=
  match (a.run initial).run ambient with
  | .error _ => none
  | .ok ((_, w), rest) => w.dev.map fun d =>
      (d.clearWorkQueue, (d.peers[0]?).map Peer.refcount, (rest.hidden.getD []).length)
theorem old_result : observe obsolete = some ([0], some 1, 1) := by decide +kernel
theorem current_result : observe (expiredZeroKeyMaterial 0) = some ([0,0], some 2, 0) := by decide +kernel
#print axioms old_result
#print axioms current_result
end ZeroQueueObserverWitness
LEAN
~~~


## Transmit error route

The old transmit factor omitted the ICMP route/classification and treated the credit record as unconditional permission to send. It stops on this specimen; the actual mirror consumes the record, increments txErrors and returns -ENOKEY. The factor now follows the source.

~~~sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 python3 - <<'PY'
import subprocess,sys
old=subprocess.check_output(['git','show','3fdf997:Leanux/Proofs/WG/Lifetimes/DeviceXmit.lean'],text=True)
parts=[]
for first,last in [('def xmitTrim (','def xmitTrimPrefix'),('def xmitSplice (','def xmitSplicePrefix'),('def wgXmitSource (','theorem wgXmitSource_eq')]:
 parts.append(old[old.index(first):old.index(last)].replace(': M ',': WG.M '))
source='import Leanux.WG.Device\nopen Leanux Leanux.WG\nnamespace XmitObserverWitness\n'+'\n'.join(parts)+"""
def initial : WGWorld := {dev := some {ifindex := 3, ifname := "wg0"}}
def ambient : Ambient := {\n  env := fun _ _ => false\n  timing := ⟨0,0⟩\n  hidden := some [{site := HiddenSite.icmpCredit.info.id, bytes := [1]}]}
def packet : Packet := {bytes := [0x45] ++ List.replicate 19 0}
def observe (a : WG.M Int) : Option (Int × Nat × Nat) :=
  match (a.run initial).run ambient with
  | .error _ => none
  | .ok ((n, w), rest) => w.dev.map fun d => (n, d.txErrors, (rest.hidden.getD []).length)
theorem obsolete_stops : observe (wgXmitSource 4 0 [packet] 0) = none := by decide +kernel
theorem current_returns : observe (WG.wgXmit 4 0 [packet] 0) = some (-ENOKEY, 1, 0) := by decide +kernel
#print axioms obsolete_stops
#print axioms current_returns
end XmitObserverWitness
"""
r=subprocess.run(['capped','--','scripts/in-bundle','lake','env','lean','-j1','--stdin'],input=source,text=True)
sys.exit(r.returncode)
PY
~~~


## Stack reply route

The obsolete reply factor stops on this unrestricted World. The actual invalid-source route returns before device access. Stack observers now include the output route, metric, neighbor classification and actual input-route verdicts.

```sh
python3 - <<'PY'
from pathlib import Path
import subprocess,sys
old=subprocess.check_output(['git','show','3b0a27a:Leanux/Proofs/WG/Lifetimes/StackAccess.lean'],text=True)
factor=old[old.index('def reply4Prefix '):old.index('theorem reply4Prefix_erases')]
factor=factor.replace('reply4Prefix','obsoleteReply').replace(': MixedM Unit',': Leanux.M Unit').replace('liftPrefix (skipCut ([.inetEhashSecret] ++ allocCuts))','skipCut ([.inetEhashSecret] ++ allocCuts)').replace('liftPrefix (get : M World)','(get : Leanux.M World)').replace('liftPrefix getDev','liftWG getDev').replace('w.routes','w.fixture.routes').replace('wgXmitPrefix','WG.wgXmit')
source='import Leanux.Runner\nimport Leanux.Env.Stack\nopen Leanux Leanux.WG Leanux.Env\nnamespace StackObserverWitness\n'+factor+'''
def initial : World := {
  ambient := {env := fun _ _ => false, timing := ⟨0,0⟩}
  tasks := Runner.initialTasks 32
  fs := {}}
def observe (a : Leanux.M Unit) : Bool :=
  match a.run initial with
  | .error _ => false
  | .ok _ => true
-- A nonzero zeronet source makes the actual route fail before device access.
def bytes : List UInt8 := List.replicate 15 0 ++ [1]
theorem obsolete_stops : observe (obsoleteReply 0 bytes) = false := by decide +kernel
theorem current_returns : observe (Stack.reply4 0 bytes) = true := by decide +kernel
#print axioms obsolete_stops
#print axioms current_returns
end StackObserverWitness
'''
r=subprocess.run(['capped','--','scripts/in-bundle','lake','env','lean','-j1','--stdin'],input=source,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
print(r.stdout);sys.exit(r.returncode)

PY
```


## Peer removal completion

A second omitted peer-hash decision occurred in the routing-completion observer. With resident peer 0 and empty AllowedIPs/hash lists, both versions mark the peer dead, but only the actual source records pubkeyRemoveHashed. The completion observer now includes the decision.

~~~lean
import Leanux.WG.Peer
open Leanux Leanux.WG
namespace RemovalDecisionWitness
def obsolete (pid : PeerId) : WG.M Unit := do
  modifyDev fun d => {d with peerList := d.peerList.filter (· != pid)}
  removeByPeer pid
  modifyDev fun d => {d with peerHashtable := d.peerHashtable.filter (·.2 != pid)}
  let p ← getPeer pid
  setPeer pid {p with isDead := true}
def peer : Peer := {
  remoteStatic := [], presharedKey := [], precomputedStaticStatic := [], internalId := 7 }
def initial : WGWorld := {
  dev := some {ifindex := 3, ifname := "wg0",
    peers := ({} : Std.TreeMap PeerId Peer).insert 0 peer} }
def ambient : Ambient := {env := fun _ _ => false, timing := ⟨0, 0⟩}
def observe (a : WG.M Unit) : Option (Nat × Bool) :=
  match (a.run initial).run ambient with
  | .error _ => none
  | .ok ((_, w), rest) => (w.dev.bind fun d => d.peers[0]?).map fun p =>
      ((rest.steps.toList.filter fun s => s.decision == .pubkeyRemoveHashed).length, p.isDead)
theorem obsolete_result : observe (obsolete 0) = some (0, true) := by decide +kernel
theorem actual_result : observe (peerMakeDead 0) = some (1, true) := by decide +kernel
#print axioms obsolete_result
#print axioms actual_result
end RemovalDecisionWitness
~~~



## Injection route

The obsolete injection observer skipped the injector route lookup and reached receive-section consumption. The current source rejects the absent route first. Current traffic observers include the actual route and loopback checks.

~~~sh
cap scripts/in-bundle python3 - <<'PY'
from pathlib import Path
import subprocess, sys
mirror = Path('Leanux/Env.lean').read_text()
old = mirror[mirror.index('def inject ('):mirror.index('/-! ## W7 stream B:')]
old = old.replace('def inject (', 'def obsoleteInject (', 1).replace(': M Int', ': Leanux.M Int')
a = old.index('  -- lane C:')
b = old.index('  runWorker .netRx', a)
old = old[:a] + old[b:]
src = '''import Leanux.Runner
namespace TrafficObserverDrift
open Leanux Leanux.WG Leanux.Env
''' + old + '''
def fixture : World :=
  { ambient := {env := Runner.harnessEnv, timing := Env.timing},
    tasks := Runner.initialTasks 1024, fs := Runner.initialFS true,
    wg := {dev := some {ifindex := 3, ifname := "wg0", running := true, incomingPort := 51820}} }
def observe (a : Leanux.M Int) : String :=
  match a.run fixture with
  | .ok (ret, _) => s!"returned {ret}"
  | .error e => e.message
theorem currentRouteRejection :
    observe (Env.inject 4 51820 []) =
      "mirror invariant violated: wg_inject: the injector's datagram has no route" := by
  decide +kernel
theorem obsoleteReachesReceive :
    observe (obsoleteInject 4 51820 []) =
      s!"hidden-input records disagree: no record supplied for {(HiddenSite.sectionStart .netRx).info.label}" := by
  decide +kernel
theorem distinctOutcomes :
    observe (Env.inject 4 51820 []) ≠ observe (obsoleteInject 4 51820 []) := by
  rw [currentRouteRejection, obsoleteReachesReceive]
  decide
#print axioms currentRouteRejection
#print axioms obsoleteReachesReceive
#print axioms distinctOutcomes
end TrafficObserverDrift
'''
r = subprocess.run(['lake', 'env', 'lean', '-j1', '--stdin'], input=src, text=True)
sys.exit(r.returncode)
PY
~~~



## Absent-device deletion

The old environment control copy ran route cleanup after an absent-device return. Actual deletion returns -ENODEV and preserves the World. The old IPv6 suffix instead clears addresses/default routing and increments the generation. The reconstruction below projects away obsolete IPv4 assignments that do not affect this observation.

~~~lean
import Leanux.Proofs.WG.Lifetimes.EnvControlsAudit
import Leanux.Runner
namespace Leanux.Proofs.DeleteDrift
open Leanux Leanux.WG
def obsoleteDeleteIPv6 : Leanux.M Int := do
  if (← getWG).dev.isSome then Env.requireIdleDevice
  let pending (sock : NlSock) : Bool :=
    sock.cbRunning || sock.queue.any fun chunk =>
      chunk.messages.any fun m => match m with | .done .. => true | _ => false
  let k ← getWG
  if pending k.nlSock7 || pending k.nlSock8 then
    unsupported "a delete with a stepped dump pending (the dump's cursor holds the device reference; the guest refuses wg_delete_with_dump_pending)"
  let ret ← (WG.wgDelete : Leanux.M Int)
  modifyRouting fun r => {r with addrs6 := [], defaultRoute6 := false, ipv6Gen := r.ipv6Gen + 1}
  return ret
def entry : World :=
  {fs := {}, tasks := Runner.initialTasks 32,
   ambient := {env := fun _ _ => false, timing := {advanceWait := 0, traceBound := 0}},
   wg := {routing := {addrs6 := [42], defaultRoute6 := true, ipv6Gen := 7}}}
def ipv6Result (x : Except Stop (Int × World)) : Except Stop (Int × List Nat × Bool × Nat) :=
  x.map fun (ret, w) => (ret, w.wg.routing.addrs6, w.wg.routing.defaultRoute6, w.wg.routing.ipv6Gen)
theorem current_absent_delete : Env.wgDelete.run entry = .ok (-ENODEV, entry) := by rfl'
theorem obsolete_absent_delete :
    ipv6Result (obsoleteDeleteIPv6.run entry) = .ok (-ENODEV, [], false, 8) := by rfl'
theorem current_absent_ipv6 :
    ipv6Result (Env.wgDelete.run entry) = .ok (-ENODEV, [42], true, 7) := by rfl'
#print axioms current_absent_delete
#print axioms obsolete_absent_delete
#print axioms current_absent_ipv6
end Leanux.Proofs.DeleteDrift
~~~



## Additional scope distinctions

The validated baseline has a 43-field observation: 31 filesystem, three task,
two seccomp and seven WG fields. Incoming unsplit work later added two FIB and
two timer fields. Four earlier checked FIB witnesses concern that enlarged
47-field observation, not the baseline contracts: MTU update changes fib4
generation 0→2; IPv4 address removal changes its generation and devAddrGenid
0→1; routeIntoWg0 changes generation 0→3; deleting the resulting unaccessed
default route reduces fib4.infos.size 2→1 without changing generation 3.
The original 43-field contracts retain their original masks. Those probe
conclusions remain recorded; standalone reproduction declarations for the four
FIB examples have not been added.

The raw-expiry timer selector also differs from TimerWheel.nextDue: expiries
64 and 65 share level-one bucket expiry 72, and enqueue stamps 1 and 2 make
wheel order select the latter while raw-expiry order selects the former. A
five-declaration kernel-checked probe established placements, coherent
timer/wheel pairs and both selector outcomes. Its standalone reproduction
declarations remain pending. Timer observers use actual wheel selection and
inline dispatch, not the obsolete raw-expiry scan.

Peer-release copies omitted queue and timer guards. Checked local probes
showed a refcount-one queued peer stopping after reference/index updates but
before erase; a pending timer stopping after erase; and staged packets allowing
release while contributing their length to txDropped. Correct event formulas
keep release only after the actual erase, including a subsequent timer Stop.
These are source-observer corrections, not initialized R2 counterexamples.


## Cleanup totality

The state-split carry exposed false unrestricted totality claims in the old RX
credit layer. Positive peer credit alone does not make peerPut total: a final
release checks both queues before erasing the peer, and checks timer state after
the erase. The mirror is unchanged.

[RxCleanupFindings.lean](../Leanux/Proofs/WG/Queues/RxCleanupFindings.lean) contains
two kernel-reduced local fixtures. The first has one peer reference and an RX
queue item; it refutes peerPut_returns and the stronger selected_payment.
The second has one peer reference, a nonempty TX queue, one RX store cell, and
a keypair with two references. Its selected carrier satisfies the complete
Inventory and Protected premises. The actual keypair payment succeeds with
its exact intermediate Ambient, but the following peer payment produces the
queue invariant Stop. The theorem cleanup_discharge_totality_refuted negates
the complete selected-cleanup contract, including packet/owner/caller equality,
and therefore the third conjunct of the historical R4
original_rx_cleanup_credit_discharge. It also refutes cleanup_discharge.

Changing the supplied carrier to unpublished additionally satisfies QueueOwners,
because the peer has no RX queue item. The actual key-put/peer-put/free suffix
still stops; discard_unpublished_totality_refuted negates that older contract.
No successful endpoint is manufactured for either Stop.

The normal-return effect and preservation statements are not refuted. Neither
are the first two R4 conjuncts or its actual-ENOSPC specialization: the latter
has an additional enqueue receipt and queue-ownership premises absent from these
fixtures. Initialized reachability, cryptographic input generation and Linux
behavior are outside these local counterexamples.

All eighteen theorems and fifteen fixture definitions pass explicit standard-only
axiom checks, fresh kernel replay and independent source review. Reproduce with
the usual optional cap wrapper from the retrofit report:

~~~sh
cap scripts/in-bundle lake build Leanux.Proofs.WG.Queues.RxCleanupFindings
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Queues.RxCleanupFindings
~~~

For the four refutations, an input to lake env lean --stdin is:

~~~lean
import Leanux.Proofs.WG.Queues.RxCleanupFindings
open Leanux.Proofs.WG.Queues.CleanupFindings
#print axioms positive_credit_totality_refuted
#print axioms selected_payment_totality_refuted
#print axioms cleanup_discharge_totality_refuted
#print axioms discard_unpublished_totality_refuted
~~~
