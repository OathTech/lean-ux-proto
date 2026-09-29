# **Lean-ux v0.1**

## **A structurally faithful, differentially tested Lean twin of a Linux security boundary**

**Status:** prototype design note  
 **Audience:** engineering/research agents working on the first Lean-ux prototype  
 **Primary objective:** bootstrap an executable Lean model that is useful as scaffolding for an eventual simulation proof relating real Linux source to Lean-ux.

---

## **1\. Project thesis**

Lean-ux is an executable model of a carefully selected slice of Linux, written in Lean.

It is **not** intended to be merely:

* an abstract operating-system model;  
* a clean specification of how Linux ought to behave;  
* a reimplementation of Linux in a functional style;  
* a syscall emulator;  
* a collection of security lemmas disconnected from real Linux source; or  
* a behavioral clone whose internal organization bears little resemblance to Linux.

The long-term goal is stronger:

**Build a structurally faithful semantic twin of Linux that initially earns confidence through differential testing, but is deliberately constructed so that it can later become the right-hand side of a mechanized simulation proof from actual Linux.**

The intended progression is:

                        differential testing  
                               │  
                               ▼  
Linux executable  ═════════  Lean-ux  
       │                         │  
       │                         │  
       │ source                  │ explicit structural map  
       ▼                         ▼  
 Linux C source  ──────── candidate correspondence relation  
       │                         │  
       └──────────────┬──────────┘  
                      ▼  
              local simulation proofs  
                      │  
                      ▼  
             subsystem simulation  
                      │  
                      ▼  
              modeled-slice simulation  
                      │  
                      ▼  
       transport Lean-ux security results  
                 back to Linux

The prototype should therefore be judged on **three axes simultaneously**:

1. **Behavioral fidelity:** does Lean-ux behave like the pinned Linux kernel?  
2. **Structural fidelity:** does the Lean implementation correspond recognizably to Linux’s state and control-flow decomposition?  
3. **Proof readiness:** are the two artifacts arranged so that an explicit state relation and local simulation lemmas can plausibly be constructed later?

A design that scores very highly on only one or two of these axes is not sufficient.

---

# **2\. The eventual theorem**

The motivating endpoint is a relation

R : LinuxState → LeanuxState → Prop

such that, schematically,

theorem linux\_refines\_leanux  
    (hrel : R linux₀ lean₀)  
    (hstep : Linux.step linux₀ event linux₁) :  
    ∃ lean₁,  
      Leanux.steps lean₀ event lean₁ ∧  
      R linux₁ lean₁

The exact relation will probably require:

* stuttering;  
* nondeterminism;  
* abstraction of implementation-only Linux state;  
* existentially related Lean states;  
* multiple Linux transitions corresponding to one Lean transition, or vice versa;  
* environment events;  
* concurrency reasoning.

Do **not** prematurely commit to a simple one-step lockstep simulation.

The important point for v0.1 is that every design decision should make some future relation `R` easier to state and prove.

Differential testing is not the final justification for Lean-ux. It is the mechanism by which we **bootstrap a plausible candidate for the abstraction and correspondence relation before undertaking the expensive proof work**.

---

# **3\. Initial target: the sealed Firecracker host boundary**

Do not begin by modeling Linux generally.

The initial motivating security boundary is a heavily constrained Firecracker process running on a pinned Linux kernel.

Firecracker already uses several host-side defense-in-depth mechanisms: seccomp, namespaces, cgroups, privilege dropping, and a jailer. Its default seccomp filters are installed per thread before guest code executes, and its design explicitly treats the KVM/virtualization layer as the primary isolation layer with process sandboxing providing additional defense in depth. ([GitHub](https://github.com/firecracker-microvm/firecracker/blob/main/docs/design.md?utm_source=chatgpt.com))

As of September 2026, Firecracker v1.17.0 is the current release. **The prototype must nevertheless pin exact commits rather than tracking “latest.”** ([GitHub](https://github.com/firecracker-microvm/firecracker/releases?utm_source=chatgpt.com))

The first interesting theorem boundary is:

Assume configuration is complete, required resources have already been opened, the jail has been established, privileges have been dropped, and restrictive seccomp policies have been installed. Now assume arbitrary attacker control over the Firecracker userspace process. What effects can that process cause through Linux?

This is deliberately stronger than proving the correctness of Firecracker’s VirtIO parsing.

For v0.1, treat compromise of Firecracker userspace as already having happened.

Conceptually:

      setup phase  
           │  
           │ create VM  
           │ establish namespaces  
           │ open resources  
           │ configure KVM  
           │ install seccomp  
           ▼  
══════════════════════════════════  
       THEOREM BOUNDARY  
══════════════════════════════════  
           │  
           │ Firecracker userspace may  
           │ now be completely malicious  
           ▼  
       Linux host interface  
           │  
           ▼  
  permitted / forbidden effects

This boundary is attractive because the jailer already aims to ensure that, once Firecracker is running unprivileged, its access is restricted to resources deliberately made available to it. ([GitHub](https://github.com/firecracker-microvm/firecracker/blob/main/docs/jailer.md?utm_source=chatgpt.com))

---

# **4\. Explicit v0.1 non-goals**

The first prototype should **not** attempt to model:

* the whole Linux kernel;  
* guest execution;  
* KVM correctness;  
* the CPU ISA;  
* VirtIO device implementations;  
* Firecracker’s Rust implementation;  
* the Firecracker API/configuration phase;  
* the jailer setup procedure;  
* arbitrary Linux applications;  
* arbitrary filesystems;  
* scheduler implementation details;  
* general networking;  
* all concurrency;  
* performance;  
* timing accuracy.

These are intentionally deferred.

In particular, **KVM is initially an abstract capability**.

This means v0.1 will not prove complete VM isolation. It will aim at the much narrower but still useful statement:

If a Firecracker process is compromised after sealing, and if the KVM capability itself satisfies an assumed isolation contract, Linux’s remaining process-facing mechanisms do not allow that process to acquire effects outside its assigned authority.

Later work can progressively replace KVM assumptions with actual KVM semantics and proofs.

---

# **5\. Freeze the universe**

Reproducibility is essential.

The prototype must pin:

Linux source commit  
Linux configuration  
compiler and compiler version  
target architecture  
Firecracker source commit  
Firecracker build configuration  
seccomp policy  
initial jail configuration  
test-machine configuration  
Lean version  
Lean-ux source revision

Do not attempt to support a moving Linux target.

Prefer **AArch64** for the first serious virtualization-related work unless an empirical obstacle appears. The eventual KVM problem remains enormous, but AArch64 offers a cleaner architecture than x86 for later refinement work.

The immediate v0.1 non-KVM prototype may run wherever engineering convenience dictates, provided the modeled kernel target itself remains pinned.

---

# **6\. Lean-ux is structurally faithful**

This requirement is fundamental.

A minimal behavioral model might represent Linux as:

def step : State → Syscall → Result State

and invent whatever internal decomposition is easiest.

Lean-ux should instead mirror Linux’s semantic organization wherever practical.

For example:

Linux                               Lean-ux

struct task\_struct            ↔     Task  
struct mm\_struct              ↔     MM  
struct files\_struct           ↔     Files  
struct file                   ↔     File  
struct vm\_area\_struct         ↔     VMA

do\_mmap                       ↔     doMmap  
mmap\_region                   ↔     mmapRegion  
vma\_merge                     ↔     vmaMerge

do\_epoll\_ctl                  ↔     doEpollCtl

kernel/...                    ↔     Leanux/Kernel/...  
mm/...                        ↔     Leanux/MM/...  
fs/...                        ↔     Leanux/FS/...  
virt/kvm/...                  ↔     Leanux/KVM/...

This is **not** a requirement for syntactic translation.

Linux implementation artifacts that have no semantic relevance to the future proof may be abstracted:

* `goto`;  
* intrusive list representation;  
* allocator layout;  
* lock implementation;  
* cache layout;  
* debugging infrastructure;  
* compiler pragmatics;  
* many forms of bookkeeping.

But abstraction must be **explicit**.

The default rule is:

Every material Linux state component and transition in the modeled slice gets either:

1. an identifiable Lean counterpart, or  
2. an explicitly documented abstraction boundary.

Never silently omit state because differential tests happen to pass without it.

---

# **7\. Correspondence metadata is a first-class artifact**

Lean-ux should maintain a machine-readable correspondence database from the beginning.

Conceptually:

structure Correspondence where  
  linuxSymbol      : LinuxSymbol  
  leanSymbol       : Lean.Name  
  kind             : CorrespondenceKind  
  sourceLocation   : LinuxSourceRange  
  fidelity         : FidelityStatus  
  abstractions     : List Abstraction  
  linuxReads       : List LinuxField  
  linuxWrites      : List LinuxField  
  knownCallers     : List LinuxSymbol  
  knownCallees     : List LinuxSymbol  
  testCoverage     : CoverageSummary

Example entries:

mm/mmap.c:mmap\_region  
  ↔ Leanux.MM.Mmap.mmapRegion  
  structural correspondence: close  
  Linux fields read: ...  
  Linux fields written: ...  
  deliberately abstracted: lock acquisition, allocator details  
  differential traces: 182,143  
  Linux KCOV paths represented: ...  
  known mismatches: none

and:

struct mm\_struct  
  ↔ Leanux.MM.Types.MM  
  represented fields: ...  
  abstracted fields: ...  
  relation sketch: relateMM

This database will later bootstrap:

def relateMM :  
    Linux.MMStruct →  
    Leanux.MM →  
    Prop

and eventually local lemmas such as:

theorem sim\_mmapRegion ...

A patch that improves differential agreement while making structural correspondence harder to explain should be treated with suspicion.

---

# **8\. The key prototype methodology: differential grinding**

The initial semantic model is largely agent-built.

The main engineering loop is:

generate test  
      │  
      ▼  
run against pinned Linux  
      │  
      ├─────────────────┐  
      ▼                 ▼  
Linux observation   Linux coverage/path  
      │  
      │  
run against Lean-ux  
      │  
      ▼  
Lean observation  
      │  
      ▼  
normalize both observations  
      │  
      ▼  
compare  
      │  
  ┌───┴────┐  
same     mismatch  
 │           │  
 │           ▼  
 │       minimize  
 │           │  
 │           ▼  
 │     builder agent  
 │           │  
 │           ▼  
 │      critic agent  
 │           │  
 └───────────┴──→ regression corpus

The aim is to turn semantic construction into a task where an agent can repeatedly **grind against an executable reward signal**.

This is expected to be one of Lean-ux’s main advantages over traditional hand-written formal models.

---

# **9\. Syzkaller should be exploited rather than reinvented**

Syzkaller is highly relevant infrastructure.

Its syscall descriptions are declarative, and syzkaller represents tests as typed syscall programs. It already contains machinery for generating, mutating, serializing, validating, executing, and minimizing such programs. ([GitHub](https://github.com/google/syzkaller/blob/master/docs/syscall_descriptions.md?utm_source=chatgpt.com))

That is almost exactly the workload language Lean-ux needs.

A useful initial architecture is:

            restricted syz program  
                     │  
          ┌──────────┴──────────┐  
          ▼                     ▼  
       Linux                 Lean-ux  
          │                     │  
          ▼                     ▼  
   raw observation        raw observation  
          │                     │  
          └──────────┬──────────┘  
                     ▼  
                normalization  
                     │  
                     ▼  
                     diff

Do not necessarily embed syzkaller wholesale into the trusted architecture.

Use whatever pieces make the grind loop efficient:

* syzlang descriptions;  
* typed program generation;  
* dependency-aware mutation;  
* minimization;  
* corpus management;  
* existing Linux interface descriptions.

The Firecracker seccomp surface can help identify the relevant interface subset.

Firecracker’s seccomp tooling expresses filters per thread category, and target-specific policies are compiled into BPF at build time. ([GitHub](https://github.com/firecracker-microvm/firecracker/blob/main/docs/seccompiler.md?utm_source=chatgpt.com))

The long-term pipeline could therefore resemble:

Firecracker seccomp policy  
          │  
          ▼  
allowed syscall/ioctl variants  
          │  
          ▼  
relevant syz descriptions  
          │  
          ├────→ generator  
          │  
          └────→ expected Lean-ux model surface

Do not assume this extraction is perfectly automatic. Firecracker’s reachable kernel surface also depends on already-open file descriptors and their object types.

---

# **10\. Inputs are traces, not isolated calls**

Linux behavior is stateful.

Therefore the fundamental differential-test unit should be a **program/trace**, not a single syscall.

Example:

eventfd(...)  
dup(...)  
mmap(...)  
epoll\_ctl(...)  
write(...)  
close(...)

The prefix constructs kernel state; the suffix interrogates it.

This is advantageous because we often do not need privileged introspection into arbitrary Linux internal state.

Instead:

operations 1..n construct interesting state  
operation n+1 distinguishes candidate semantics

A mismatch should be minimized to the smallest trace that still distinguishes Linux and Lean-ux.

The minimized trace becomes:

* a debugging artifact;  
* a permanent regression test;  
* evidence about missing semantic state;  
* input to the builder agent;  
* input to the critic agent.

---

# **11\. Define an explicit observation language**

Never compare arbitrary Linux memory against Lean state.

Define exactly what the model claims to predict.

A preliminary observation type might resemble:

structure Observation where  
  result       : SysResult  
  errno        : Option Errno  
  outputMemory : List MemoryDelta  
  fdEffects    : List FDEffect  
  mappings     : List MappingEffect  
  signals      : List SignalEffect  
  external     : List ExternalEffect  
  termination  : Option TerminationReason

This will evolve.

The critical requirement is that the observation language be sufficiently rich to expose distinctions relevant to the eventual confinement theorem.

It must not quietly quotient away security-relevant differences merely because they make testing difficult.

---

# **12\. Normalize incidental nondeterminism**

Literal output equality is generally wrong.

Examples of incidental Linux values include:

* raw virtual addresses under ASLR;  
* file-descriptor numbers;  
* PIDs/TIDs;  
* timestamps;  
* scheduling choices;  
* random values;  
* allocator-dependent identifiers.

Represent these relationally.

For example:

Linux fd 7       ↔ abstract capability F0  
Linux fd 11      ↔ abstract capability F1

Linux 0x7f...    ↔ mapping M0 \+ offset 0  
Linux tid 18342  ↔ thread T0

The comparison target becomes roughly:

# **\[**

#  

# **normalize(trace\_{Linux})**

normalize(trace\_{Leanux})  
 \]

or, eventually, membership/refinement rather than equality:

\[  
 normalize(trace\_{Linux})  
 \\in Behaviors\_{Leanux}  
 \]

if Lean-ux intentionally over-approximates nondeterminism.

---

# **13\. The normalization relation is security-critical**

The builder agent must **not** be allowed to make tests pass by weakening observational equivalence.

Treat the following artifacts as high-trust/high-review components:

* observation definition;  
* normalization rules;  
* ignored fields;  
* nondeterminism boundaries;  
* external-environment model;  
* test oracle;  
* trusted abstractions.

Changing these is qualitatively different from fixing `mmapRegion`.

A useful governance rule is:

**Builder agents may freely patch modeled semantics. Changes to the oracle, normalization layer, or abstraction boundary require critic approval and explicit justification.**

Every normalization rule should answer:

1. Why is the concrete Linux value irrelevant?  
2. What relation replaces literal equality?  
3. Could erasing this distinction conceal a confinement failure?  
4. Will a future simulation relation have to recover this information?

---

# **14\. Use Linux coverage as a second reward signal**

Behavioral agreement alone encourages accidental specialization to the existing corpus.

Linux’s KCOV infrastructure is specifically designed for coverage-guided kernel fuzzing. It can collect task-local coverage precise enough to associate coverage with an individual syscall, and its design intentionally avoids some inherently nondeterministic scheduler/locking coverage to obtain a signal more closely tied to syscall inputs. ([Kernel.org](https://kernel.org/doc/html/next/dev-tools/kcov.html?utm_source=chatgpt.com))

Use KCOV where practical.

The optimization signals then become:

1\. differential agreement  
2\. Linux kernel coverage  
3\. Lean-ux semantic branch coverage  
4\. structural-path correspondence

A prototype dashboard could track:

interface        tests       agreement       Linux coverage  
\-----------------------------------------------------------  
close            61k         100.000%        ...  
dup              92k          99.998%        ...  
mmap            188k          99.94%         ...  
munmap           74k         100.000%        ...  
epoll\_ctl        89k          99.81%         ...

Coverage percentage itself is not proof of completeness.

Its purpose is to tell the generator and agents where unexplored behavior remains.

KCOV also exposes comparison operands, potentially providing additional guidance for generation around branch constants. ([Kernel.org](https://kernel.org/doc/html/next/dev-tools/kcov.html?utm_source=chatgpt.com))

---

# **15\. Structural execution correspondence**

Where feasible, go beyond output comparison.

If Linux execution visits:

sys\_mmap  
  → ksys\_mmap\_pgoff  
  → vm\_mmap\_pgoff  
  → do\_mmap  
  → mmap\_region  
  → vma\_merge

and the structurally mapped Lean execution visits:

mmap  
  → mmapPgoff  
  → vmMmapPgoff  
  → doMmap  
  → mmapRegion  
  → vmaMerge

then the test harness has learned something much stronger than merely:

both returned 0

Exact path equality is not required and often will not be desirable.

But source coverage plus the correspondence database can expose:

* a Linux semantic branch with no Lean counterpart;  
* Lean logic that predicts the right output through the wrong mechanism;  
* unexpected source dependencies;  
* missing state;  
* excessive abstraction.

This structural feedback should be fed to the critic.

---

# **16\. Builder and critic agents**

The agent architecture intentionally separates local progress from anti-specialization.

## **Builder objective**

The builder is allowed to be aggressively local.

Given a minimized discrepancy, it should:

1\. reproduce discrepancy  
2\. inspect Linux execution  
3\. inspect relevant Linux source  
4\. inspect correspondence metadata  
5\. hypothesize missing semantic rule/state  
6\. modify Lean-ux  
7\. compile  
8\. rerun minimized case  
9\. rerun regressions  
10\. report structural consequences

The builder’s immediate optimization objective is:

maximize behavioral agreement while preserving declared structural correspondence.

## **Critic objective**

The critic is the anti-specialization watchdog.

Its job is not primarily to write prose reviews.

Where possible, criticism should become **new executable tests**.

The critic asks:

* Is this a genuine Linux rule or an encoding of one counterexample?  
* Is the change justified by Linux source?  
* What neighboring inputs distinguish the proposed rule from obvious alternatives?  
* Did the builder introduce unexplained constants?  
* Is newly introduced Lean state actually reflected in Linux?  
* Did the patch accidentally collapse distinct Linux states?  
* Did the patch change an abstraction boundary?  
* Does the Lean control-flow decomposition still align with Linux?  
* Could the model be simpler without losing observed behavior?  
* Did a normalization change merely hide the mismatch?

If the builder adds:

if len \= 4096 then  
  .error EINVAL

the critic should generate probes around:

4095  
4096  
4097  
page\_size  
2 \* page\_size  
different mapping state  
different flags  
different preceding operations

rather than merely saying “this looks overfit.”

---

# **17\. Maintain different test populations**

Do not treat all tests as one undifferentiated corpus.

At minimum distinguish:

### **Regression corpus**

Every previously discovered semantically meaningful discrepancy.

Must remain green.

### **Coverage-seeking corpus**

Generated primarily to exercise previously unexplored Linux source paths or semantic branches.

### **Critic/generalization corpus**

Generated specifically to distinguish a proposed semantic rule from nearby hypotheses.

### **Structural-correspondence probes**

Chosen to exercise mapped Linux/Lean source paths and identify path divergence.

### **Security-directed probes**

Inputs designed to stress capability acquisition, aliasing, FD behavior, memory mappings, privilege boundaries, and other behavior directly relevant to the eventual confinement property.

---

# **18\. Avoid cloning subsystems we do not need**

The structural-fidelity requirement does **not** imply reimplementing every Linux subsystem touched indirectly.

Once a resource is deliberately granted to the sealed process, many underlying implementations can become abstract capabilities.

For example, instead of modeling ext4:

structure FileCapability where  
  object      : ObjectId  
  permissions : Permissions

A write can generate:

ExternalEffect.write object range bytes

The security theorem may care that:

fd B grants effects on disk object B

but not how ext4 converts those effects into block requests.

Similarly, TAP/network access can initially become an environmental capability:

ExternalEffect.send networkCapability packet

The key proof question is whether an attacker can **manufacture authority over another object**, not whether Lean-ux implements every layer underneath an authorized object.

The model should still preserve the Linux structures that determine which capability a particular FD names.

---

# **19\. Concurrency policy for v0.1**

Do not begin by predicting the Linux scheduler.

Represent concurrency semantically as nondeterministic interleaving.

For example:

step :  
  State →  
  ThreadId →  
  Action →  
  Set State

or an equivalent transition relation.

The eventual invariant proof should aim for:

\[  
 I(s) \\land s \\rightarrow s’  
 \\Rightarrow I(s’)  
 \]

for every permitted transition.

Differential testing can initially focus on controlled/sequential transitions and deliberately constructed concurrency experiments.

Exact schedule matching is not a requirement.

Synchronization primitives may need progressively richer semantics as the modeled surface grows.

---

# **20\. Environment-driven behavior**

Timing, randomness, asynchronous input, and external I/O should generally be explicit environment inputs rather than secretly sampled inside Lean-ux.

Conceptually:

inductive EnvironmentEvent  
  | clockValue ...  
  | randomBytes ...  
  | networkPacket ...  
  | signalArrival ...  
  | ioCompletion ...

A differential experiment should, where possible, inject equivalent environment events into Linux and Lean-ux.

This prevents accidental attempts to predict fundamentally environmental state.

---

# **21\. Suggested v0.1 semantic state**

Do not freeze this prematurely, but an initial shape might resemble:

structure KernelState where  
  tasks          : TaskId → Option Task  
  addressSpaces  : MMId → Option MM  
  filesTables    : FilesId → Option Files  
  files          : FileId → Option File  
  kernelObjects  : ObjectId → Option KernelObject

  mappings       : MappingState  
  epoll          : EpollState  
  eventfd        : EventfdState  
  futex          : FutexState  
  signals        : SignalState

  seccomp        : ThreadId → SeccompPolicy

  capabilities   : CapabilityState  
  kvm            : AbstractKVMState

  environment    : EnvironmentState

Do not centralize everything into a giant record merely because Lean permits it.

Preserve Linux ownership/decomposition relationships where those relationships will matter to the future simulation relation.

---

# **22\. First modeled surface**

Do **not** start with the whole Firecracker seccomp policy.

First prove the methodology on a deliberately tiny coherent surface.

A plausible first set is around:

close  
dup / dup3  
read/write on controlled objects  
mmap  
munmap  
eventfd  
epoll  
basic signal delivery/state

Exact selection should be determined by:

1. ease of constructing deterministic experiments;  
2. relevance to the sealed Firecracker process;  
3. enough hidden state to make the problem nontrivial;  
4. enough Linux structural complexity to test structural mirroring;  
5. availability of existing syz descriptions;  
6. good KCOV observability.

The first research milestone is **not Firecracker confinement**.

It is:

Can an agent autonomously build and maintain a structurally faithful Lean semantic twin of a nontrivial Linux slice by differential grinding?

If this fails, discover why before expanding the modeled surface.

---

# **23\. Prototype milestone 0: prove the loop**

Implement perhaps 5–10 operations.

Success means:

generated trace  
    ↓  
real Linux execution  
    ↓  
normalized observation  
    ↓  
Lean execution  
    ↓  
normalized observation  
    ↓  
automatic comparison  
    ↓  
automatic minimization of mismatch  
    ↓  
builder patch  
    ↓  
critic-generated adversarial neighbors  
    ↓  
regression

This loop should be nearly push-button.

The primary deliverable is **not the semantics**.

It is the semantic-construction machine.

---

# **24\. Prototype milestone 1: structural fidelity**

Once the grind loop works, add explicit source correspondence.

For each modeled operation:

* record the Linux entry point;  
* record the important call graph;  
* identify material structures and fields;  
* align Lean definitions;  
* collect KCOV/source path evidence;  
* record deliberate abstractions.

Require the critic to reject behaviorally successful patches that destroy correspondence without justification.

At this stage it should be possible for a human to place the Linux implementation and Lean implementation side-by-side and understand why they correspond.

---

# **25\. Prototype milestone 2: Firecracker-derived surface**

Extract the host operations actually available to a chosen sealed Firecracker configuration.

Use:

* Firecracker seccomp policies;  
* its build configuration;  
* runtime tracing;  
* open FD inventory;  
* capability/object types.

Firecracker’s seccomp configuration is already per-thread and designed to restrict the host syscall surface to what each thread requires. ([GitHub](https://github.com/firecracker-microvm/firecracker/blob/main/docs/seccomp.md?utm_source=chatgpt.com))

Construct an explicit modeled-surface manifest such as:

interface  
allowed thread(s)  
argument restrictions  
required fd/object type  
Linux entry point  
Lean counterpart  
modeling status  
coverage status  
known abstractions

At this point Lean-ux should begin resembling a semantic twin of the **actual attack surface**, rather than a generic syscall model.

---

# **26\. Prototype milestone 3: first confinement theorem**

Once enough capability-bearing state exists, formulate a theorem over Lean-ux itself.

For example:

theorem compromised\_vmm\_confinement  
    (hinit : SealedFirecrackerState s)  
    (hattacker : ArbitraryUserCode attacker) :  
    ∀ effect ∈ behaviors s attacker,  
      AllowedByInitialCapabilities s effect

Possible permitted capability classes:

guest RAM  
the VM's KVM object  
the VM's vCPU objects  
the VM's root/block images  
its TAP/network capability  
metrics/log output  
its own process state

The exact theorem is a design problem.

The critical feature is that authority should be traceable to **initially granted capabilities**.

The attacker should not be able to manufacture authority over unrelated host resources.

---

# **27\. KVM remains abstract in v0.1**

Represent KVM operations structurally enough that they can later be refined, but assume their internal isolation initially.

For example:

structure KVMCapability where  
  vm : VMId

with operations resembling the relevant KVM API.

Initial assumptions might say:

a capability for VM A cannot mutate VM B  
KVM\_RUN cannot directly create arbitrary host capabilities  
memslot operations affect only permitted VM resources

These are temporary proof assumptions.

Track them prominently.

The long-term program is to replace them incrementally:

axiom KVM isolation  
        ↓  
prove VM object ownership  
        ↓  
prove memslot isolation  
        ↓  
model stage-2 mappings  
        ↓  
model guest memory access  
        ↓  
model exits  
        ↓  
model interrupt machinery  
        ↓  
...

The trusted KVM region should shrink rather than being forgotten.

---

# **28\. The future source-side problem**

Differential testing only provides evidence about an executable Linux binary.

A formal simulation proof eventually needs a formal meaning for the Linux side.

Schematically:

Linux C source  
      │  
      ▼  
source semantics  
      │  
      ▼  
Linux transition  
      │  
      │ simulation  
      ▼  
Lean-ux transition

Do **not** solve this first.

The proposed methodology deliberately reverses the usual order.

Traditional approach:

formalize implementation  
      ↓  
design abstraction  
      ↓  
prove refinement

Lean-ux approach:

construct abstraction experimentally  
      ↓  
force structural alignment  
      ↓  
stabilize candidate relation  
      ↓  
formalize only the source semantics needed  
      ↓  
prove correspondence

This is one of the central research bets of the project.

The prototype should therefore continuously record enough source information that later source-level formalization is local rather than archaeological.

---

# **29\. Local simulation lemmas are the desired decomposition**

The eventual verification should ideally not begin with one enormous whole-kernel theorem.

We want local obligations resembling:

theorem sim\_vmaMerge  
    (hrel : relateMM cmm lmm)  
    (hlinux : Linux.vmaMerge cmm args ⇓ cmm') :  
    ∃ lmm',  
      Leanux.vmaMerge lmm args ⇓ lmm' ∧  
      relateMM cmm' lmm'

and similarly:

sim\_doMmap  
sim\_mmapRegion  
sim\_epollCtl  
sim\_fdInstall  
...

Structural fidelity in v0.1 is valuable primarily because it makes this decomposition imaginable.

The correspondence database should make it possible to ask:

What Linux function/state relation is the next local proof obligation for this Lean definition?

---

# **30\. The agent should think of differential testing as relation synthesis**

Do not conceptualize the test loop simply as “finding bugs in our emulator.”

A recurring mismatch often tells us something about `R`.

Suppose Lean-ux models a VMA as:

structure VMA where  
  start : Addr  
  stop  : Addr  
  prot  : Prot

but repeated Linux discrepancies require a flag currently omitted.

Adding that field may represent more than fixing execution.

We have learned experimentally that any useful future relation:

relateVMA linuxVMA leanVMA

must preserve some information represented by that flag.

Thus repeated differential refinement performs a crude kind of **empirical relation synthesis**.

The critic should explicitly reason in these terms.

Ask not only:

Why did this test fail?

but:

What information about Linux state did our proposed abstraction incorrectly identify as irrelevant?

---

# **31\. Anti-specialization rules**

The following should be considered hard project norms.

### **Rule 1: source grounding**

Every surprising semantic rule should be traceable to Linux source, not merely to observations.

### **Rule 2: neighboring tests**

Every nontrivial fix should trigger critic-generated nearby cases.

### **Rule 3: no unexplained constants**

Magic values copied from a minimized trace are presumptively bugs.

### **Rule 4: normalization changes are exceptional**

Never weaken the comparison relation merely to restore green tests.

### **Rule 5: preserve Linux distinctions until justified**

Prefer temporarily carrying apparently irrelevant state over prematurely quotienting it away.

### **Rule 6: abstractions must have names**

Every intentionally omitted Linux mechanism should appear in the correspondence metadata.

### **Rule 7: behavioral agreement does not excuse structural mismatch**

Passing tests by implementing a completely different algorithm is not automatically acceptable.

### **Rule 8: structural correspondence is not permission to cargo-cult implementation details**

Do not reproduce irrelevant low-level C mechanics purely for visual similarity.

### **Rule 9: minimize trusted assumptions**

Record every opaque component and axiom.

### **Rule 10: every discovered discrepancy is valuable**

Do not hide hard cases. Preserve them even if temporarily marked unsupported.

---

# **32\. Suggested repository structure**

A possible initial layout:

lean-ux/  
├── README.md  
├── DESIGN.md  
├── lakefile.toml  
│  
├── Leanux/  
│   ├── Basic/  
│   │   ├── Addr.lean  
│   │   ├── Errno.lean  
│   │   └── Capability.lean  
│   │  
│   ├── Kernel/  
│   │   ├── Task.lean  
│   │   ├── Signal.lean  
│   │   └── Seccomp.lean  
│   │  
│   ├── MM/  
│   │   ├── Types.lean  
│   │   ├── Mmap.lean  
│   │   └── Munmap.lean  
│   │  
│   ├── FS/  
│   │   ├── File.lean  
│   │   ├── FDTable.lean  
│   │   └── ReadWrite.lean  
│   │  
│   ├── Epoll/  
│   ├── Eventfd/  
│   ├── KVM/  
│   │   └── Abstract.lean  
│   │  
│   ├── Observation.lean  
│   ├── Transition.lean  
│   └── Properties/  
│       └── Confinement.lean  
│  
├── correspondence/  
│   ├── symbols.json  
│   ├── abstractions.json  
│   └── source-map.json  
│  
├── harness/  
│   ├── generator/  
│   ├── linux-runner/  
│   ├── lean-runner/  
│   ├── normalize/  
│   ├── diff/  
│   └── minimize/  
│  
├── corpus/  
│   ├── regression/  
│   ├── coverage/  
│   ├── critic/  
│   └── security/  
│  
├── linux/  
│   ├── PINNED\_COMMIT  
│   ├── config  
│   └── patches/  
│  
└── reports/  
    ├── coverage/  
    ├── mismatches/  
    └── correspondence/

The precise structure can change.

Maintain conceptual separation between:

semantic implementation  
test oracle  
normalization  
source correspondence  
trusted assumptions  
proofs  
---

# **33\. Every modeled component should carry a dossier**

For each significant Lean definition, record something like:

Lean symbol:  
  Leanux.MM.Mmap.mmapRegion

Linux correspondents:  
  mm/mmap.c:mmap\_region  
  supporting functions: ...

Linux commit:  
  \<hash\>

Structural fidelity:  
  close / moderate / abstract

Known abstraction:  
  locking represented atomically  
  allocator identity erased

Observed Linux fields:  
  reads: ...  
  writes: ...

Differential status:  
  N generated traces  
  M mismatches outstanding

Coverage:  
  source regions observed

Security relevance:  
  modifies memory authority

Future proof:  
  expected relation: relateMM  
  expected theorem: sim\_mmapRegion

This is not bureaucracy.

It is the accumulated scaffolding for the future simulation proof.

---

# **34\. What counts as v0.1 success?**

Lean-ux v0.1 succeeds if it establishes that the **method works**, not if it models all of Firecracker’s host surface.

A successful v0.1 should demonstrate all of the following:

1. A pinned Linux executable acts as an automatic behavioral oracle.  
2. Typed multi-operation traces can be generated automatically.  
3. The same conceptual traces execute against Lean-ux.  
4. Observations can be normalized robustly.  
5. Differential mismatches are automatically detected and minimized.  
6. An agent can repair a nontrivial semantic mismatch.  
7. A critic can generate adversarial generalization tests that catch an over-specialized repair.  
8. Linux KCOV/source traces provide useful exploration feedback.  
9. Lean definitions maintain recognizable structural correspondence with Linux.  
10. Correspondence metadata is generated and maintained.  
11. At least one nontrivial Linux structure has an explicit candidate `relateX` relation.  
12. At least one small local simulation-style lemma is written, even if it relates two Lean encodings or an idealized Linux-side representation rather than actual C semantics.  
13. The model is strong enough to state a meaningful capability-preservation invariant.

If those things work, scaling the semantic surface is justified.

---

# **35\. Failure modes worth detecting early**

The prototype should actively try to falsify the project thesis.

Particularly important failure modes include:

### **Hidden-state explosion**

Every new differential test requires adding obscure Linux state until Lean-ux becomes essentially another Linux implementation.

If this happens quickly, the intended abstraction boundary is wrong.

### **Structural/behavioral conflict**

The easiest behaviorally correct model consistently wants radically different decomposition from Linux.

We need to know whether structural fidelity imposes unreasonable complexity.

### **Nondeterminism dominates**

Normalized outputs remain too unstable for a useful differential oracle.

If so, redefine the experiment boundary before scaling.

### **Coverage plateaus**

Generated traces achieve high agreement but repeatedly exercise only shallow Linux paths.

Then agreement is misleading.

### **Critic impotence**

The critic produces plausible prose but does not actually find specialized patches.

The critic must be evaluated empirically by deliberately injecting overfit repairs.

### **Oracle erosion**

The easiest path to increasing the pass rate becomes weakening normalization.

Treat this as a severe warning.

### **Source archaeology dominates**

Agents spend most of their time understanding unrelated Linux machinery rather than making checked progress.

This indicates the initial modeled slice is too broad.

### **Lean execution is too slow**

Differential fuzzing requires large numbers of executions. Keep executable semantics computational enough to support this workload.

---

# **36\. First concrete experiment**

The first experiment should be intentionally small.

Choose one stateful subsystem such as memory mappings or FD management.

For example:

mmap  
munmap  
mprotect  
close  
dup

Then implement:

1\. restricted typed trace generator  
2\. Linux runner  
3\. Lean runner  
4\. observation format  
5\. normalization  
6\. differential comparator  
7\. minimizer  
8\. KCOV capture  
9\. correspondence metadata  
10\. builder prompt/context  
11\. critic prompt/context

Seed Lean-ux with an intentionally incomplete semantics.

Then ask whether the full system can repeatedly transform:

Linux ≠ Lean-ux

into:

Linux ≈ Lean-ux

without human semantic patching.

Deliberately insert bad/specialized repairs and verify that the critic catches them.

This tests the methodology more directly than attempting to maximize syscall count.

---

# **37\. Agent working instructions**

When working on Lean-ux, optimize for the following order:

1\. understand the exact Linux behavior  
2\. understand the Linux source mechanism producing it  
3\. identify the corresponding Lean structure/path  
4\. make the smallest principled semantic correction  
5\. preserve or improve structural correspondence  
6\. generate tests that could falsify the correction  
7\. run regressions  
8\. update correspondence metadata  
9\. state any new abstraction or trusted assumption explicitly

Never optimize primarily for number of green tests.

When uncertain, prefer:

explicit state  
explicit nondeterminism  
explicit abstraction  
explicit correspondence

over clever compression.

Do not assume an observed behavior is intentional Linux API semantics. The project mirrors the pinned kernel initially; distinguishing specification from implementation behavior is a later concern.

Do not infer general rules from one execution.

Do not invent Linux behavior when an experiment can determine it.

Do not treat Linux source as infallible documentation of runtime behavior when compilation/configuration details can be tested.

Do not treat differential agreement as proof.

Do not treat structural similarity as proof.

The goal is to make both forms of evidence converge on an artifact from which proof is tractable.

---

# **38\. Core research hypothesis**

The project is testing a broader methodology:

**A large implementation can be bootstrapped into formal verification by using agents to construct a structurally faithful executable twin, using the implementation itself as a differential oracle, and only later converting the resulting empirically stabilized correspondence into a mechanized simulation proof.**

Lean-ux is a particularly demanding test case because Linux is:

* large;  
* stateful;  
* concurrency-heavy;  
* implementation-driven;  
* full of historical detail;  
* security-critical;  
* difficult to formalize monolithically.

The hypothesis is that agents can nevertheless make progress because the work is decomposed into repeated locally checkable steps.

Early phase:

reward \= differential agreement

Middle phase:

reward \=  
  differential agreement  
  \+ source/path correspondence  
  \+ adversarial critic survival

Later phase:

reward \= Lean accepts the simulation proof

Thus the project gradually transitions from **empirical semantic synthesis** to **formal refinement**, without requiring a clean manual model to exist beforehand.

---

# **39\. The conceptual end state**

The ideal mature artifact looks approximately like:

                  empirical evidence  
                         │  
                         ▼  
       Linux executable ≈ Lean-ux  
                              │  
                              │ proved properties  
                              ▼  
                        confinement etc.  
                              ▲  
                              │ simulation  
                              │  
       Linux source semantics

with the central theorem eventually allowing:

\[  
 Leanux \\models P  
 \]

plus

\[  
 Linux \\preceq Leanux  
 \]

to imply the relevant form of:

\[  
 Linux \\models P.  
 \]

At that point Lean-ux is not simply a model of Linux.

It is the **proof-facing representation of Linux**.

That is the design target against which all prototype choices should be evaluated.

---

# **40\. Immediate next task**

Do not start by implementing dozens of syscalls.

Build the smallest end-to-end experiment that tests the central bet.

The next concrete objective is:

**Produce a structurally aligned Lean model of one small but stateful Linux subsystem, run generated syscall traces against both the pinned Linux kernel and Lean-ux, automatically minimize discrepancies, and demonstrate an autonomous builder/critic loop that converges toward both behavioral and structural fidelity.**

Everything else in v0.1 follows from whether that experiment works.

