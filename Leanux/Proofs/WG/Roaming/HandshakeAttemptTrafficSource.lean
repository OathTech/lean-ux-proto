import Leanux.Proofs.WG.Roaming.HandshakeAttemptDeferredSource
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation

/-! Admission, transmission, inline data polls and guards retain their
existing RX observations. Handshake processing occurs in the supplied receive
observer through the actual scheduler callbacks. Exact source projection and
prefix validity hold on both normal and stopped outcomes. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Roaming.HandshakeAttemptTransport.Traffic
open Leanux Leanux.WG Queues Lifetimes Leanux.Proofs.Logged
variable {Attempt : Type} {valid : List Attempt → Prop}

def receive (msg : List UInt8) (src : SkbSource) : PrefixM (Event Attempt) Unit :=
  old (RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src)))
def transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) : PrefixM (Event Attempt) Int :=
  old (RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu)))
def multicast (family addr : Nat) : PrefixM (Event Attempt) Unit :=
  old (RxHistory.audit (xmitMulticastLoopAudit family addr))
def drained (what : String) (flags : List Bool) : PrefixM (Event Attempt) Unit :=
  old (RxHistory.mixed (requireDrainedPrefix what flags))
def inlinePoll : PrefixM (Event Attempt) Unit := old RxHistory.pollScheduledInline

theorem receive_preserves (valid : List Attempt → Prop) (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (receive msg src) :=
  old_preserves valid _
theorem transmit_preserves (valid : List Attempt → Prop) (family addr : Nat)
    (packets : List Packet) (mtu : Nat) :
    PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (transmit family addr packets mtu) :=
  old_preserves valid _
theorem multicast_preserves (valid : List Attempt → Prop) (family addr : Nat) :
    PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (multicast family addr) :=
  old_preserves valid _
theorem drained_preserves (valid : List Attempt → Prop) (what : String) (flags : List Bool) :
    PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (drained what flags) :=
  old_preserves valid _
theorem inlinePoll_preserves (valid : List Attempt → Prop) :
    PrefixPreserves (fun h _ => Safe valid h) (Safe valid) inlinePoll := old_preserves valid _

theorem receive_projects (msg : List UInt8) (src : SkbSource) :
    ProjectsPrefix rxEvent id (receive (Attempt := Attempt) msg src)
      (RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src))) :=
  old_projects _ (Appends.focus _ _ _)
theorem transmit_projects (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    ProjectsPrefix rxEvent id (transmit (Attempt := Attempt) family addr packets mtu)
      (RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu))) :=
  old_projects _ (Appends.focus _ _ _)
theorem multicast_projects (family addr : Nat) :
    ProjectsPrefix rxEvent id (multicast (Attempt := Attempt) family addr)
      (RxHistory.audit (xmitMulticastLoopAudit family addr)) :=
  old_projects _ (Appends.focus _ _ _)
theorem drained_projects (what : String) (flags : List Bool) :
    ProjectsPrefix rxEvent id (drained (Attempt := Attempt) what flags)
      (RxHistory.mixed (requireDrainedPrefix what flags)) :=
  old_projects _ (Appends.focus _ _ _)
theorem inlinePoll_projects :
    ProjectsPrefix rxEvent id (inlinePoll (Attempt := Attempt)) RxHistory.pollScheduledInline :=
  old_projects _ RxHistory.pollScheduledInline_appends

theorem receive_appends (msg : List UInt8) (src : SkbSource) :
    Appends (receive (Attempt := Attempt) msg src) := old_appends _
theorem transmit_appends (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Appends (transmit (Attempt := Attempt) family addr packets mtu) := old_appends _
theorem multicast_appends (family addr : Nat) :
    Appends (multicast (Attempt := Attempt) family addr) := old_appends _
theorem drained_appends (what : String) (flags : List Bool) :
    Appends (drained (Attempt := Attempt) what flags) := old_appends _
theorem inlinePoll_appends : Appends (inlinePoll (Attempt := Attempt)) := old_appends _

def inject (r : Receive Attempt valid) (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) : PrefixM (Event Attempt) Int :=
  TrafficSource.injectWith receive (Deferred.crypt r) drained family port msg tos ll dest
def afterBatch (r : Receive Attempt valid) : PrefixM (Event Attempt) Unit :=
  TrafficSource.afterBatchWith (Deferred.crypt r) (Deferred.send r) Deferred.sendOne
    (fun stack => schedule r stack) drained
def flood (r : Receive Attempt valid) (count port family : Nat) (messages : List (List UInt8)) :
    PrefixM (Event Attempt) Int :=
  TrafficSource.floodWith receive inlinePoll (afterBatch r) drained count port family messages
def batchItem (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    PrefixM (Event Attempt) (ForInStep (List Int)) :=
  batchItemWith receive inlinePoll multicast transmit d cqes item
def batch (r : Receive Attempt valid) (items : List Env.BatchItem) : PrefixM (Event Attempt) Int :=
  TrafficSource.batchWith batchItem (afterBatch r) items

variable (r : Receive Attempt valid)

theorem inject_projects (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) :
    ProjectsPrefix rxEvent id (inject r family port msg tos ll dest)
      (RxHistory.inject family port msg tos ll dest) := by
  rw [TrafficSource.inject_factor]
  exact TrafficSource.inject_projects rxEvent _ _ _ _ _ _
    receive_projects (Deferred.crypt_projects r) drained_projects family port msg tos ll dest
theorem afterBatch_projects :
    ProjectsPrefix rxEvent id (afterBatch r) RxHistory.afterBatch := by
  rw [TrafficSource.afterBatch_factor]
  exact TrafficSource.afterBatch_projects rxEvent _ _ _ _ _ _ _ _ _ _
    (Deferred.crypt_projects r) (Deferred.send_projects r) Deferred.sendOne_projects
    (schedule_projects r) drained_projects
theorem flood_projects (count port family : Nat) (messages : List (List UInt8)) :
    ProjectsPrefix rxEvent id (flood r count port family messages)
      (RxHistory.flood count port family messages) := by
  rw [TrafficSource.flood_factor]
  exact TrafficSource.flood_projects rxEvent _ _ _ _ _ _ _ _
    receive_projects inlinePoll_projects (afterBatch_projects r) drained_projects count port family messages
theorem batchItem_projects (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ProjectsPrefix rxEvent id (batchItem (Attempt := Attempt) d cqes item)
      (RxHistory.batchItem d cqes item) := by
  rw [rxBatchItem_factor]
  exact batchItemWith_projects rxEvent _ _ _ _ _ _ _ _ receive_projects inlinePoll_projects
    multicast_projects transmit_projects d cqes item
theorem batch_projects (items : List Env.BatchItem) :
    ProjectsPrefix rxEvent id (batch r items) (RxHistory.batch items) := by
  rw [TrafficSource.batch_factor]
  apply TrafficSource.batch_projects rxEvent _ _ _ _ _ (afterBatch_projects r) items
  intro d cqes item
  have step : (projectStep id : ForInStep (List Int) → ForInStep (List Int)) = id := by
    funext x
    cases x <;> rfl
  rw [step]
  exact batchItem_projects d cqes item

theorem inject_appends (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) : Appends (inject r family port msg tos ll dest) :=
  TrafficSource.inject_appends _ _ _ receive_appends (Deferred.crypt_appends r) drained_appends
    family port msg tos ll dest
theorem afterBatch_appends : Appends (afterBatch r) :=
  TrafficSource.afterBatch_appends _ _ _ _ _ (Deferred.crypt_appends r) (Deferred.send_appends r)
    Deferred.sendOne_appends (schedule_appends r) drained_appends
theorem flood_appends (count port family : Nat) (messages : List (List UInt8)) :
    Appends (flood r count port family messages) :=
  TrafficSource.flood_appends _ _ _ _ receive_appends inlinePoll_appends (afterBatch_appends r)
    drained_appends count port family messages
theorem batchItem_appends (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    Appends (batchItem (Attempt := Attempt) d cqes item) :=
  batchItemWith_appends _ _ _ _ receive_appends inlinePoll_appends multicast_appends
    transmit_appends d cqes item
theorem batch_appends (items : List Env.BatchItem) : Appends (batch r items) :=
  TrafficSource.batch_appends _ _ batchItem_appends (afterBatch_appends r) items

theorem inject_preserves (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (inject r family port msg tos ll dest) :=
  TrafficSource.inject_preserves (I := fun h _ => Safe valid h) (S := Safe valid)
    (fun _ _ pre => pre) (fun _ _ _ _ pre => pre) _ _ _
    (receive_preserves valid) (Deferred.crypt_preserves r) (drained_preserves valid)
    family port msg tos ll dest
theorem afterBatch_preserves :
    PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (afterBatch r) :=
  TrafficSource.afterBatch_preserves (I := fun h _ => Safe valid h) (S := Safe valid)
    (fun _ _ pre => pre) (fun _ _ _ _ pre => pre) _ _ _ _ _
    (Deferred.crypt_preserves r) (Deferred.send_preserves r)
    (Deferred.sendOne_preserves valid) (schedule_preserves r) (drained_preserves valid)
theorem flood_preserves (count port family : Nat) (messages : List (List UInt8)) :
    PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (flood r count port family messages) :=
  TrafficSource.flood_preserves (I := fun h _ => Safe valid h) (S := Safe valid)
    (fun _ _ pre => pre) (fun _ _ _ _ pre => pre) _ _ _ _
    (receive_preserves valid) (inlinePoll_preserves valid) (afterBatch_preserves r)
    (drained_preserves valid) count port family messages
theorem batchItem_preserves (valid : List Attempt → Prop) (d : Device)
    (cqes : List Int) (item : Env.BatchItem) :
    PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (batchItem d cqes item) :=
  batchItemWith_preserves (I := fun h _ => Safe valid h) (S := Safe valid)
    (fun _ _ pre => pre) (fun _ _ _ _ pre => pre) _ _ _ _
    (receive_preserves valid) (inlinePoll_preserves valid)
    (multicast_preserves valid) (transmit_preserves valid) d cqes item
theorem batch_preserves (items : List Env.BatchItem) :
    PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (batch r items) :=
  TrafficSource.batch_preserves (I := fun h _ => Safe valid h) (S := Safe valid)
    (fun _ _ pre => pre) (fun _ _ _ _ pre => pre) _ _
    (batchItem_preserves valid) (afterBatch_preserves r) items

theorem receive_erases (msg : List UInt8) (src : SkbSource) :
    ErasesPrefix (receive (Attempt := Attempt) msg src) (liftWG (wgReceive msg src)) :=
  projects_erases (receive_projects msg src)
    (RxHistory.mixed_erases (liftWGObserver_erases (wgReceivePrefix_erases msg src)))
theorem transmit_erases (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    ErasesPrefix (transmit (Attempt := Attempt) family addr packets mtu)
      (liftWG (wgXmit family addr packets mtu)) :=
  projects_erases (transmit_projects family addr packets mtu)
    (RxHistory.mixed_erases (liftWGObserver_erases (wgXmitPrefix_erases family addr packets mtu)))
theorem multicast_erases (family addr : Nat) :
    ErasesPrefix (multicast (Attempt := Attempt) family addr) (Env.xmitMulticastLoop family addr) :=
  projects_erases (multicast_projects family addr)
    (RxHistory.audit_erases (xmitMulticastLoopAudit_erases family addr))
theorem drained_erases (what : String) (flags : List Bool) :
    ErasesPrefix (drained (Attempt := Attempt) what flags) (Env.requireDrained what flags) :=
  projects_erases (drained_projects what flags)
    (RxHistory.mixed_erases (requireDrainedPrefix_erases what flags))
theorem inlinePoll_erases :
    ErasesPrefix (inlinePoll (Attempt := Attempt)) Env.pollScheduledInline :=
  projects_erases inlinePoll_projects RxHistory.pollScheduledInline_erases
theorem inject_erases (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) :
    ErasesPrefix (inject r family port msg tos ll dest) (Env.inject family port msg tos ll dest) :=
  projects_erases (inject_projects r family port msg tos ll dest)
    (RxHistory.inject_erases family port msg tos ll dest)
theorem afterBatch_erases : ErasesPrefix (afterBatch r) Env.afterBatch :=
  projects_erases (afterBatch_projects r) RxHistory.afterBatch_erases
theorem flood_erases (count port family : Nat) (messages : List (List UInt8)) :
    ErasesPrefix (flood r count port family messages) (Env.flood count port family messages) :=
  projects_erases (flood_projects r count port family messages)
    (RxHistory.flood_erases count port family messages)
theorem batchItem_erases (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ErasesPrefix (batchItem (Attempt := Attempt) d cqes item) (Environment.batchItemSource d cqes item) :=
  projects_erases (batchItem_projects d cqes item) (RxHistory.batchItem_erases d cqes item)
theorem batch_erases (items : List Env.BatchItem) : ErasesPrefix (batch r items) (Env.batch items) :=
  projects_erases (batch_projects r items) (RxHistory.batch_erases items)

end Leanux.Proofs.WG.Roaming.HandshakeAttemptTransport.Traffic
