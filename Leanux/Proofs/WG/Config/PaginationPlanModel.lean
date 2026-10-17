import Leanux.Proofs.WG.Config.SocketReadbackModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

/-- Positive-sized tail chunks. `extra + 1` is the resumed IPv4 capacity. -/
def ipv4TailPages (extra : Nat) : List NodeId → List (List NodeId)
  | [] => []
  | first :: rest => (first :: rest.take extra) :: ipv4TailPages extra (rest.drop extra)
termination_by ids => ids.length
decreasing_by simp_wf; omega

def ipv4FirstCapacity (d : Device) : Nat :=
  (NLMSG_GOODSIZE - devicePrefixSpace d - 140) / 28

def ipv4ResumeCapacity (d : Device) : Nat :=
  (NLMSG_GOODSIZE - devicePrefixSpace d - 44) / 28

/-- Canonical nonempty IPv4 pages. The later source theorem's header-room
domain makes both calculated capacities positive, so the first-plus-tail
presentation uses exactly those capacities, with no extra truncation. -/
def ipv4PaginationPages (d : Device) : List NodeId → List (List NodeId)
  | [] => []
  | first :: rest =>
    (first :: rest.take (ipv4FirstCapacity d - 1)) ::
      ipv4TailPages (ipv4ResumeCapacity d - 1) (rest.drop (ipv4FirstCapacity d - 1))

theorem ipv4TailPages_flatten (extra : Nat) (ids : List NodeId) :
    (ipv4TailPages extra ids).flatten = ids := by
  cases ids with
  | nil => simp [ipv4TailPages]
  | cons first rest =>
    rw [ipv4TailPages]
    simp only [List.flatten_cons,List.cons_append]
    rw [ipv4TailPages_flatten extra (rest.drop extra),List.take_append_drop]
termination_by ids.length
decreasing_by simp_wf; omega

theorem ipv4PaginationPages_flatten (d : Device) (ids : List NodeId) :
    (ipv4PaginationPages d ids).flatten = ids := by
  cases ids with
  | nil => rfl
  | cons first rest =>
    simp only [ipv4PaginationPages,List.flatten_cons,List.cons_append,
      ipv4TailPages_flatten,List.take_append_drop]

/-- The exact socket transformation for a nonfinal DATA callback. -/
def paginationMoreSocket (sock : NlSock) (call : DumpCall) : NlSock :=
  {sock with ctx := call.ctx,prevSeq := call.prevSeq,dumpDoneErrno := call.ret,queue := [call.skb]}


end Leanux.Proofs.WG.Config
