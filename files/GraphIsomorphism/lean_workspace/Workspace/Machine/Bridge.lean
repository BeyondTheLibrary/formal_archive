import Workspace.Machine.BridgeUp
import Workspace.Machine.PolyFun

/-!
# The bridge: the workspace convention gives the top-level classes

`Workspace/Machine/BridgeUp.lean` and `Workspace/Machine/BridgeDown.lean` build the two halves
`up` and `down`.  This file puts them together: for a routine `P` of the workspace convention,

`seq up (seq P down)`

is a program of the *top-level* convention computing the same function, with `O(n)` steps added
at each end.  The consequences are the missing implications of `Workspace/Machine/PolyFun.lean`:
`PolyFun f → PolyTime f` and `QuasiPolyFun f → QuasiPolyTime f`, and the relational forms that
produce the shape of `RAM.Targets.Theorem_1_1_1_statement`.

## Why the output size has to be bounded

`down` reads the length of the output out of a register and copies that many cells, so it costs
`O(n')` steps with `n'` the length of the output encoding.  That is *not* bounded by the running
time of `P`: one instruction `add x x x` doubles a register, so a `T`-step routine may output a
list of length `2 ^ T` (this is "Doubts" item 3 of `Workspace/Machine/DESIGN.md`).  So every
statement below takes a bound `Enc.size (f a) ≤ S (Enc.size a)` with `S` polynomially bounded —
exactly the bound that `RAM.SizeBound` packages, which is why `RAM.PolyFun` carries it.

## Main results

* `RAM.Bridge.runsTo_bridge`: the Hoare triple for `seq up (seq P down)`;
* `RAM.polyTime_of_polyTimeCleanAt`, `RAM.quasiPolyTime_of_quasiPolyTimeCleanAt`;
* `RAM.PolyFun.polyTime`, `RAM.QuasiPolyFun.quasiPolyTime`;
* `RAM.polyTimeRel_of_polyTimeCleanRelAt`, `RAM.quasiPolyTimeRel_of_quasiPolyTimeCleanRelAt`;
* `RAM.quasiPolyTimeRel_uniform`: one program and one bound for a whole family of relations,
  which is the shape `RAM.Targets.Theorem_1_1_1_statement` asks for.
-/

namespace RAM

variable {α β : Type*}

namespace Bridge

/-- **The bridge.**  A routine of the workspace convention, framed by `up` and `down`, is a
program of the top-level convention. -/
theorem runsTo_bridge {l l' : List ℕ} {P : Program} {T : ℕ}
    (hP : RunsTo P (fun m => m = initMemAt 16 l) (fun m' => m' = initMemAt 16 l') T) :
    RunsTo (seq up (seq P down)) (fun m => m = initMem l) (fun m' => OutputAt m' l')
      ((18 * l.length + 78) + (T + (7 * l'.length + 34))) :=
  (runsTo_up l).seq (hP.seq (runsTo_down_outputAt l'))

end Bridge

/-! ## The time bound of the bridge -/

/-- The cost of the framed routine: the two linear passes plus the routine's own time. -/
def bridgeTime (T S : ℕ → ℕ) : ℕ → ℕ := fun n => (18 * n + 78) + (T n + (7 * S n + 34))

theorem polyBound_bridgeTime {T S : ℕ → ℕ} (hT : PolyBound T) (hS : PolyBound S) :
    PolyBound (bridgeTime T S) :=
  (((polyBound_const 18).mul polyBound_id).add (polyBound_const 78)).add
    (hT.add (((polyBound_const 7).mul hS).add (polyBound_const 34)))

theorem quasiPolyBound_bridgeTime {T S : ℕ → ℕ} (hT : QuasiPolyBound T) (hS : PolyBound S) :
    QuasiPolyBound (bridgeTime T S) :=
  ((((polyBound_const 18).mul polyBound_id).add (polyBound_const 78)).quasiPoly).add
    (hT.add ((((polyBound_const 7).mul hS).add (polyBound_const 34)).quasiPoly))

/-- The length of an encoding is below its size; this is what turns the `O(n)` cost of `up` and
`down` into a cost in the input size. -/
theorem length_encode_lt [Enc α] (a : α) : (Enc.encode a).length < Enc.size a :=
  length_lt_listSize _

/-! ## Functions -/

/-- **A clean routine of the workspace convention computes in the top-level convention.**  The
bound `S` on the size of the output is needed because `down` copies the whole output; see the
module docstring. -/
theorem computesInTime_of_cleanComputeAt [Enc α] [Enc β] {P : Program} {f : α → β}
    {T S : ℕ → ℕ} (hP : CleanComputeAt 16 P f T) (hSmono : ∀ n n', n ≤ n' → S n ≤ S n')
    (hS : ∀ a, Enc.size (f a) ≤ S (Enc.size a)) :
    ComputesInTime (seq Bridge.up (seq P Bridge.down)) f (bridgeTime T S) := by
  refine RunsTo.computesInTime (fun a => ?_)
  refine (Bridge.runsTo_bridge (hP a)).mono ?_
  have h1 : (Enc.encode a).length < Enc.size a := length_encode_lt a
  have h2 : (Enc.encode (f a)).length < Enc.size (f a) := length_encode_lt (f a)
  have h3 : Enc.size (f a) ≤ S (Enc.size a) := hS a
  simp only [bridgeTime]
  omega

/-- **Polynomial time at the workspace convention gives polynomial time.** -/
theorem polyTime_of_polyTimeCleanAt [Enc α] [Enc β] {f : α → β} (h : PolyTimeCleanAt 16 f)
    {S : ℕ → ℕ} (hSb : PolyBound S) (hS : ∀ a, Enc.size (f a) ≤ S (Enc.size a)) :
    PolyTime f := by
  obtain ⟨P, T, hT, hP⟩ := h
  obtain ⟨c, d, hc⟩ := hSb
  refine ⟨seq Bridge.up (seq P Bridge.down),
    bridgeTime T (fun n => c * (n + 1) ^ d),
    polyBound_bridgeTime hT (polyBound_witness c d), ?_⟩
  exact computesInTime_of_cleanComputeAt hP (fun _ _ h => polyBound_witness_mono c d h)
    (fun a => le_trans (hS a) (hc _))

/-- **Quasipolynomial time at the workspace convention gives quasipolynomial time.** -/
theorem quasiPolyTime_of_quasiPolyTimeCleanAt [Enc α] [Enc β] {f : α → β}
    (h : QuasiPolyTimeCleanAt 16 f) {S : ℕ → ℕ} (hSb : PolyBound S)
    (hS : ∀ a, Enc.size (f a) ≤ S (Enc.size a)) : QuasiPolyTime f := by
  obtain ⟨P, T, hT, hP⟩ := h
  obtain ⟨c, d, hc⟩ := hSb
  refine ⟨seq Bridge.up (seq P Bridge.down),
    bridgeTime T (fun n => c * (n + 1) ^ d),
    quasiPolyBound_bridgeTime hT (polyBound_witness c d), ?_⟩
  exact computesInTime_of_cleanComputeAt hP (fun _ _ h => polyBound_witness_mono c d h)
    (fun a => le_trans (hS a) (hc _))

/-- **`PolyFun` gives `PolyTime`.**  This is the implication `Workspace/Machine/PolyFun.lean`
was missing: a function assembled from the structural rules of that file is computable in
polynomial time at the top-level convention. -/
theorem PolyFun.polyTime [Enc α] [Enc β] {f : α → β} (h : PolyFun f) : PolyTime f := by
  obtain ⟨S, hSb, -, hS⟩ := h.size.exists_polyBound
  exact polyTime_of_polyTimeCleanAt h.time hSb hS

/-- **`QuasiPolyFun` gives `QuasiPolyTime`.** -/
theorem QuasiPolyFun.quasiPolyTime [Enc α] [Enc β] {f : α → β} (h : QuasiPolyFun f) :
    QuasiPolyTime f := by
  obtain ⟨S, hSb, -, hS⟩ := h.size.exists_polyBound
  exact quasiPolyTime_of_quasiPolyTimeCleanAt h.time hSb hS

/-! ## Search problems -/

/-- **The relational form of the bridge.** -/
theorem solvesInTime_of_cleanSolveAt [Enc α] [Enc β] {P : Program} {R : α → β → Prop}
    {T S : ℕ → ℕ} (hP : CleanSolveAt 16 P R T) (hSmono : ∀ n n', n ≤ n' → S n ≤ S n')
    (hS : ∀ a b, R a b → Enc.size b ≤ S (Enc.size a)) :
    SolvesInTime (seq Bridge.up (seq P Bridge.down)) R (bridgeTime T S) := by
  intro a
  obtain ⟨b, hb, hrun⟩ := hP a
  refine ⟨b, hb, ?_⟩
  have hbound : (18 * (Enc.encode a).length + 78) +
      (T (Enc.size a) + (7 * (Enc.encode b).length + 34)) ≤ bridgeTime T S (Enc.size a) := by
    have h1 : (Enc.encode a).length < Enc.size a := length_encode_lt a
    have h2 : (Enc.encode b).length < Enc.size b := length_encode_lt b
    have h3 : Enc.size b ≤ S (Enc.size a) := hS a b hb
    simp only [bridgeTime]
    omega
  obtain ⟨k, hk, hhalt, hout⟩ :=
    ((Bridge.runsTo_bridge hrun).mono hbound).spec (initMem (Enc.encode a)) rfl
  exact ⟨k, hk, hhalt, hout⟩

/-- **Polynomial time at the workspace convention gives polynomial time**, search version. -/
theorem polyTimeRel_of_polyTimeCleanRelAt [Enc α] [Enc β] {R : α → β → Prop}
    (h : PolyTimeCleanRelAt 16 R) {S : ℕ → ℕ} (hSb : PolyBound S)
    (hS : ∀ a b, R a b → Enc.size b ≤ S (Enc.size a)) : PolyTimeRel R := by
  obtain ⟨P, T, hT, hP⟩ := h
  obtain ⟨c, d, hc⟩ := hSb
  refine ⟨seq Bridge.up (seq P Bridge.down),
    bridgeTime T (fun n => c * (n + 1) ^ d),
    polyBound_bridgeTime hT (polyBound_witness c d), ?_⟩
  exact solvesInTime_of_cleanSolveAt hP (fun _ _ h => polyBound_witness_mono c d h)
    (fun a b hab => le_trans (hS a b hab) (hc _))

/-- **Quasipolynomial time at the workspace convention gives quasipolynomial time**, search
version.  This is the form `RAM.Targets.Theorem_1_1_1_statement` is phrased in. -/
theorem quasiPolyTimeRel_of_quasiPolyTimeCleanRelAt [Enc α] [Enc β] {R : α → β → Prop}
    (h : QuasiPolyTimeCleanRelAt 16 R) {S : ℕ → ℕ} (hSb : PolyBound S)
    (hS : ∀ a b, R a b → Enc.size b ≤ S (Enc.size a)) : QuasiPolyTimeRel R := by
  obtain ⟨P, T, hT, hP⟩ := h
  obtain ⟨c, d, hc⟩ := hSb
  refine ⟨seq Bridge.up (seq P Bridge.down),
    bridgeTime T (fun n => c * (n + 1) ^ d),
    quasiPolyBound_bridgeTime hT (polyBound_witness c d), ?_⟩
  exact solvesInTime_of_cleanSolveAt hP (fun _ _ h => polyBound_witness_mono c d h)
    (fun a b hab => le_trans (hS a b hab) (hc _))

/-! ## Only the answer that is returned has to be small

`RAM.solvesInTime_of_cleanSolveAt` asks `hS : ∀ a b, R a b → Enc.size b ≤ S (Enc.size a)`: *every*
admissible answer is small.  For the relations the paper produces this is false.  In
`RAM.Targets.SIRel` an admissible answer carries a list of generators of `Aut_G(x)`, and any
list that generates that group is admissible, so the list can be as long as one likes.

What is true, and what the routine delivers, is that the *returned* answer is small.  So the
right hypothesis is that the routine solves the strengthened relation
`fun a b => R a b ∧ Enc.size b ≤ S (Enc.size a)`, and the conclusion is still about `R`.  The
step from the one to the other is `RAM.SolvesInTime.imp`. -/

/-- A routine solving a relation also solves any weaker relation. -/
theorem CleanSolveAt.imp {K : ℕ} [Enc α] [Enc β] {P : Program} {R R' : α → β → Prop} {T : ℕ → ℕ}
    (h : CleanSolveAt K P R T) (hRR : ∀ a b, R a b → R' a b) : CleanSolveAt K P R' T := by
  intro a
  obtain ⟨b, hb, hrun⟩ := h a
  exact ⟨b, hRR a b hb, hrun⟩

/-- **The relational bridge, usable form.**  The routine solves the relation *together with* the
size bound, so only the answer it returns has to be small. -/
theorem solvesInTime_of_cleanSolveAt_small [Enc α] [Enc β] {P : Program} {R : α → β → Prop}
    {T S : ℕ → ℕ}
    (hP : CleanSolveAt 16 P (fun a b => R a b ∧ Enc.size b ≤ S (Enc.size a)) T)
    (hSmono : ∀ n n', n ≤ n' → S n ≤ S n') :
    SolvesInTime (seq Bridge.up (seq P Bridge.down)) R (bridgeTime T S) :=
  (solvesInTime_of_cleanSolveAt hP hSmono (fun _ _ hab => hab.2)).imp (fun _ _ hab => hab.1)

/-- **Polynomial time at the workspace convention gives polynomial time**, search version with
the size bound carried inside the relation. -/
theorem polyTimeRel_of_polyTimeCleanRelAt_small [Enc α] [Enc β] {R : α → β → Prop} {S : ℕ → ℕ}
    (hSb : PolyBound S) (hSmono : ∀ n n', n ≤ n' → S n ≤ S n')
    (h : PolyTimeCleanRelAt 16 (fun a b => R a b ∧ Enc.size b ≤ S (Enc.size a))) :
    PolyTimeRel R := by
  obtain ⟨P, T, hT, hP⟩ := h
  exact ⟨seq Bridge.up (seq P Bridge.down), bridgeTime T S, polyBound_bridgeTime hT hSb,
    solvesInTime_of_cleanSolveAt_small hP hSmono⟩

/-- **Quasipolynomial time at the workspace convention gives quasipolynomial time**, search
version with the size bound carried inside the relation. -/
theorem quasiPolyTimeRel_of_quasiPolyTimeCleanRelAt_small [Enc α] [Enc β] {R : α → β → Prop}
    {S : ℕ → ℕ} (hSb : PolyBound S) (hSmono : ∀ n n', n ≤ n' → S n ≤ S n')
    (h : QuasiPolyTimeCleanRelAt 16 (fun a b => R a b ∧ Enc.size b ≤ S (Enc.size a))) :
    QuasiPolyTimeRel R := by
  obtain ⟨P, T, hT, hP⟩ := h
  exact ⟨seq Bridge.up (seq P Bridge.down), bridgeTime T S, quasiPolyBound_bridgeTime hT hSb,
    solvesInTime_of_cleanSolveAt_small hP hSmono⟩

/-! ## One program for a whole family

`RAM.Targets.Theorem_1_1_1_statement` asks for a *single* program and a *single* bound working
for every domain size and every alphabet size.  The bridge preserves that: it frames one
workspace routine, so one workspace routine for the whole family gives one program for the whole
family. -/

/-- **The shape of the final theorem.**  One clean routine of the workspace convention, one
quasipolynomial bound and one polynomial size bound, uniform over the family, give one program
of the top-level convention solving every member of the family within one quasipolynomial
bound. -/
theorem quasiPolyTimeRel_uniform {ι : Type*} {A B : ι → Type*} [∀ i, Enc (A i)]
    [∀ i, Enc (B i)] {R : ∀ i, A i → B i → Prop} {P : Program} {T S : ℕ → ℕ}
    (hT : QuasiPolyBound T) (hSb : PolyBound S)
    (hP : ∀ i, CleanSolveAt 16 P (R i) T)
    (hS : ∀ i (a : A i) (b : B i), R i a b → Enc.size b ≤ S (Enc.size a)) :
    ∃ (Q : Program) (T' : ℕ → ℕ), QuasiPolyBound T' ∧ ∀ i, SolvesInTime Q (R i) T' := by
  obtain ⟨c, d, hc⟩ := hSb
  refine ⟨seq Bridge.up (seq P Bridge.down), bridgeTime T (fun n => c * (n + 1) ^ d),
    quasiPolyBound_bridgeTime hT (polyBound_witness c d), fun i => ?_⟩
  exact solvesInTime_of_cleanSolveAt (hP i) (fun _ _ h => polyBound_witness_mono c d h)
    (fun a b hab => le_trans (hS i a b hab) (hc _))

/-- **The shape of the final theorem, usable form.**  One clean routine of the workspace
convention which, uniformly in the index, returns an answer that is both admissible and small.
Only the returned answer is bounded, which is what a routine can promise: see the section "Only
the answer that is returned has to be small". -/
theorem quasiPolyTimeRel_uniform_small {ι : Type*} {A B : ι → Type*} [∀ i, Enc (A i)]
    [∀ i, Enc (B i)] {R : ∀ i, A i → B i → Prop} {P : Program} {T S : ℕ → ℕ}
    (hT : QuasiPolyBound T) (hSb : PolyBound S) (hSmono : ∀ n n', n ≤ n' → S n ≤ S n')
    (hP : ∀ i, CleanSolveAt 16 P
      (fun (a : A i) (b : B i) => R i a b ∧ Enc.size b ≤ S (Enc.size a)) T) :
    ∃ (Q : Program) (T' : ℕ → ℕ), QuasiPolyBound T' ∧ ∀ i, SolvesInTime Q (R i) T' :=
  ⟨seq Bridge.up (seq P Bridge.down), bridgeTime T S, quasiPolyBound_bridgeTime hT hSb,
    fun i => solvesInTime_of_cleanSolveAt_small (hP i) hSmono⟩

end RAM
