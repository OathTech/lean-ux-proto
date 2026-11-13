# Independent review B: binary remediation plan

Reviewed revision: `2c020e3192aafc60788d5f9b5da2df6088416737`.
Archive inspected: `8b498e7ec207a042540148dda5881787731b5ac0`
(`archive/whole-driver-pilot-2026-11-12`). Review conclusions and proposed
remedies are [AGENT 2026-11-13].

The sequencing is sensible: repair admission, recover instruments separately,
then prove a small useful statement and its joins. The plan distinguishes
conditional service contracts from verified bodies, independently predicted
source state from reconstruction, and ordinary execution from serialized
execution. Its investigation budget and permission to retain partial results
give it a practical stopping rule. I found two material omissions in the
acceptance procedure. They can be repaired without another validation framework.
Neither finding asserts that the existing Lean theorems are false.

## B1 — Medium: require complete capture intervals before accepting joins

**Plan references:** `docs/2026-11-13-binary-remediation-plan.md:150–165`,
`:260–280`, and `:292–300`.

Stage 2 requires separate expected/captured/admitted counts and detection of
missing clauses. It does not say where the expected invocation count comes
from, require continuous observation of the selected interval, or make an
inexact count disqualify that interval. Its explicit exit only requires the
instruments to detect the two known predicate failures. Those requirements
can leave a missing *invocation* invisible even after omitted clauses and
missing snapshot spans are rejected.

This is an existing property of the proposed recovery tools, not a hypothetical
adversarial parser attack:

* At archive `binary/contracts/capture.py:34–46`, service breakpoints are
  removed after a quota and later sampled. Counts are explicitly only counts
  of seen visits after disarming. Lines 238–240 set `exact=False` when this
  happens, and lines 505–509 emit that information in final `site` rows.
* At archive `binary/contracts/wd_trace.py:65–92`, the event conversion keeps
  marks, calls and entries, dropping those final site rows. The per-event
  `exact` field survives Python conversion but is not represented or read by
  archive `binary/PilotTraceRun.lean:42–65,89–109`.
* Archive `binary/contracts/wd_check.py:404–406` uses `--first 100000` for the
  short pilot. That reduces the chance of truncation; it neither establishes
  completeness nor supplies a check when a longer workload reaches the cap.

A targeted executable check confirmed that an input `site` row carrying
`exact=False` yields no output event. Thus a service can execute in an
unobserved gap without generating a failed, absent or unevaluated clause at
all. A whole entry/return pair omitted after entry sampling can likewise be
absent from a retained-event denominator. Endpoint equality alone cannot
identify a temporary ownership or lifetime change in that gap. This threatens
the real-sequence and one-identity-map claims in stages 5 and 6.

**Requested change:** make stage 2 establish a complete selected interval for
composition: all relevant entry/service/lifetime sites remain observed, no
quota or sampling gap intersects it, and the coverage metadata is checked
before predicate evaluation. State how expected invocations are counted and
which missing counts make admission unavailable. Diagnostic sampled runs can
remain useful at their stated scope. Add one small control that removes a
whole invocation or exhausts a site quota; it must fail completeness rather
than merely reduce the reported denominator. This is a narrow extension of
the proposed missing-clause controls.

## B2 — Medium: make proof acceptance include each recovered headline

**Plan references:** `docs/2026-11-13-binary-remediation-plan.md:199–204`,
`:275–279`, and `:324–329`.

The plan directs new proof claim points to run the existing binary gate and
the acceptance procedure in `binary/README.md`, but those commands do not
automatically discover newly recovered claims:

* `scripts/binary-proof-gate:140–153` checks exactly `HEADLINES` and `IMPORTS`
  from `binary/surface.py`. Their current lists at `binary/surface.py:10–86`
  contain the October claims, not clean-image C2, C1 or future compositions.
* The printed specification is likewise explicitly enumerated in
  `binary/surface.py:89–179`.
* `binary/README.md:99–109` exports nine named October roots. Its lines
  118–125 correctly say acceptance is specific to the source commit and
  export closure. Repeating those commands after a port does not add the
  port's root to that closure.
* The gate's escape scan at `scripts/binary-proof-gate:158–164` examines
  top-level `binary/*.lean` only. The archive's complete C2 headline includes
  `binary/bridge/RtC2Bridge.lean`; the archived `RtC2Headline.lean:6–8`
  explicitly distinguishes the three local clauses from the complete
  headline. This is another reason that an old command's green result
  cannot stand in for an explicitly selected new closure.

An implementation following the stated commands can build the new modules
separately while obtaining a green gate and external acceptance for the old
roots. That would leave the reported new proof claim outside the required
axiom/replay evidence. The stage-0 inventory is helpful documentation but
does not itself update these executable lists.

**Requested change:** require each proof-bearing recovery unit to add its
exact terminal declarations, meaning-defining predicates and imported roots
to the existing trust surface and to name the export/replay closure containing
them. Include any recovered bridge in that closure and in the applicable
source checks. Review the updated statement diff and report acceptance for
that revision and closure. No new gate or broad audit system is needed.

## Validation performed and limits

I read the proposal, linked assessment, standing rules, current binary build
and proof-acceptance setup, the current lookup and mutator capture code, and
the archived C2 statement/capture/checker and pilot capture/event/evaluation
path. I did not consult another reviewer's conclusions. The assessment's
reported build and capture counts were not rerun and are not fresh evidence
from this review.

One bounded Python check ran under `capped -m 1G` after inspecting account
memory. It loaded the archived `wd_trace.py` directly from Git, wrote one
synthetic final coverage row in a private temporary directory, and confirmed
that conversion discarded it. It checks metadata loss, not an end-to-end
false acceptance by the Lean evaluator. The temporary directory was removed.
No kernel boot, Lean build, heavy experiment, external acceptance, source
remediation, main update or external publication was performed.

Reproduce the focused check from a task worktree:

```sh
capped -m 1G -- python3 -B -c '
import json, pathlib, subprocess, tempfile
source = subprocess.check_output(["git", "show",
    "8b498e7ec207a042540148dda5881787731b5ac0:binary/contracts/wd_trace.py"], text=True)
module = {"__name__": "review_wd_trace"}
exec(compile(source, "archive/wd_trace.py", "exec"), module)
root = pathlib.Path(".tmp")
root.mkdir(exist_ok=True)
with tempfile.TemporaryDirectory(prefix="binary-review-b-", dir=root) as temporary:
    path = pathlib.Path(temporary)
    row = {"type": "site", "site": "0x1000", "kind": "call",
           "function": "wg_example", "callee": "kmem_cache_alloc",
           "seen": 8, "kept": 8, "exact": False, "contracts": ["allocator"]}
    (path / "records.jsonl").write_text(json.dumps(row) + "\n")
    assert module["events"](path) == []
    print("Confirmed: final inexact-site coverage metadata is discarded")
'
```
