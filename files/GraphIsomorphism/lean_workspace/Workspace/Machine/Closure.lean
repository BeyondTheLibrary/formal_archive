import Workspace.Machine.Const
import Workspace.Machine.Locality
import Workspace.Machine.Recursion
import Workspace.Machine.Reloc
import Workspace.Machine.Small
import Workspace.Machine.Iterate

/-!
# Closure summary: what may be used without writing machine code

This is the file a later section reads.  It collects, under uniform names, every way currently
available of proving that a function is computed in polynomial or quasipolynomial time on the
RAM of `Workspace/Machine/RAM.lean`, together with the frame rule that a new combinator would be
built from.  Nothing is proved here: each statement is a restatement of a theorem of
`Compose.lean`, `Recursion.lean`, `Const.lean` or `Locality.lean`.

The classes are `RAM.PolyTimeClean f` and `RAM.QuasiPolyTimeClean f` (`Compose.lean`): `f` is
computed by a program that, started in `initMem (Enc.encode a)`, halts within `T (Enc.size a)`
steps in *exactly* `initMem (Enc.encode (f a))`.  Cleanliness is what makes the classes closed
under composition; `RAM.PolyTimeClean.polyTime` and `RAM.QuasiPolyTimeClean.quasiPolyTime` turn
membership into the plain classes `PolyTime`, `QuasiPolyTime` of `TimeClasses.lean`, in which
`RAM.Theorem_1_1_1_statement` is phrased.

## Available

| Fact | Name | Hypotheses |
|---|---|---|
| identity | `RAM.Closure.polyTime_id` | — |
| constant | `RAM.Closure.polyTime_const` | — |
| function of one bit | `RAM.Closure.polyTime_ofBool` | — |
| conditional, constant branches | `RAM.Closure.polyTime_ifConst` | `p` clean and polynomial |
| bit length, binary logarithm | `RAM.Closure.polyTime_size`, `RAM.Closure.polyTime_log2` | — |
| `+`, truncated `-`, `min`, `max`, `≤` on `ℕ × ℕ` | `RAM.Closure.polyTime_add`, `..._sub`, `..._min`, `..._max`, `..._le` | — |
| packaging a scratch-based routine on a fixed-shape input | `RAM.Small.cleanCompute_unary`, `RAM.Small.cleanCompute_binary` | the routine writes only in registers `2 .. 9` |
| composition | `RAM.Closure.polyTime_comp` | polynomial bound on the size of the intermediate result |
| composition, quasipolynomial | `RAM.Closure.quasiPolyTime_comp`, `..._comp_poly`, `..._comp_quasi` | same |
| composition, search problems | `RAM.Closure.polyTimeRel_comp`, `RAM.Closure.quasiPolyTimeRel_comp` | same |
| recursion (`q` calls, `p` work per call) | `RAM.Closure.polyTime_recursion`, `RAM.Closure.quasiPolyTime_recursion` | clean routines for set-up, one call, read-off; bounds on the number of calls and on the work per call |
| bounded iteration of a *program* | `RAM.runsTo_iterate` | a clean routine for `(k, s) ↦ (k - 1, step s)` |
| frame rule for a call | `RAM.CleanCompute.frame`, `RAM.CleanCompute.frame'`, `RAM.CleanSolve.frame` | the caller's data lies above `2 ^ T * B` |
| **procedure call keeping the caller's data** | `RAM.runsTo_reloc`, `RAM.CleanCompute.runsTo_reloc`, `RAM.CleanSolve.runsTo_reloc` | three reserved registers below the base address `d`, the argument written from `d` on; costs `10 * T` |
| the workspace convention | `RAM.initMemAt`, `RAM.CleanComputeAt`, `RAM.PolyTimeCleanAt`, `RAM.QuasiPolyTimeCleanAt` (and the relational forms) | — |
| top-level convention → workspace convention | `RAM.cleanComputeAt_of_cleanCompute`, `RAM.cleanSolveAt_of_cleanSolve`, `RAM.polyTimeCleanAt_of_polyTimeClean`, `RAM.quasiPolyTimeCleanAt_of_quasiPolyTimeClean`, and the two relational forms | `3 ≤ K` |
| pairing at the workspace convention | `RAM.Closure.polyTimeAt_pair`, `RAM.Closure.quasiPolyTimeAt_pair` | `16 ≤ K`; polynomial bounds on the sizes of `f a` and `g a` |
| projections at the workspace convention | `RAM.Closure.polyTimeAt_fst`, `RAM.Closure.polyTimeAt_snd` | `16 ≤ K` |
| conditional at the workspace convention | `RAM.Closure.polyTimeAt_ite` | `16 ≤ K`; `p`, `f`, `g` clean at `K` |
| recursion at the workspace convention | `RAM.Closure.polyTimeAt_recursion`, `RAM.Closure.quasiPolyTimeAt_recursion` | as at the top level, loop on register `K + 2` |
| bounded iteration `a ↦ step^[k a] a` | `RAM.Closure.polyTimeAt_iterate`, `RAM.Closure.quasiPolyTimeAt_iterate` | `16 ≤ K`; a bound on `k a` and one on the size of every intermediate value |
| composition at the workspace convention | `RAM.CleanComputeAt.comp`, `RAM.PolyTimeCleanAt.comp`, `RAM.QuasiPolyTimeCleanAt.comp`, `RAM.PolyTimeCleanRelAt.comp`, `RAM.QuasiPolyTimeCleanRelAt.comp` | polynomial bound on the size of the intermediate result |
| composition, quasipolynomial, with a *quasipolynomially* large intermediate result | `RAM.QuasiPolyTimeCleanAt.comp_quasiSize`, `RAM.QuasiPolyTimeCleanRelAt.comp_quasiSize` | quasipolynomial bound on that size |
| closure of the bounds themselves | `RAM.PolyBound.add`, `..mul`, `..comp`, `RAM.QuasiPolyBound.add`, `..mul`, `..comp`, `..comp_poly`, `RAM.PolyBound.comp_quasiPoly`, `RAM.PolyBound.quasiPoly` | — |
| polynomial time from clean time | `RAM.PolyTimeClean.polyTime`, `RAM.QuasiPolyTimeClean.quasiPolyTime` | — |

## The function-level interface (`Workspace/Machine/PolyFun.lean`)

The table above is the *machine-level* interface: every entry carries the register count `16 ≤ K`
of the workspace convention and a polynomial bound on the size of each intermediate result.
`Workspace/Machine/PolyFun.lean` packages both away:

`RAM.PolyFun f` = `RAM.PolyTimeCleanAt 16 f` together with `RAM.SizeBound f`
(`Enc.size (f a) ≤ c * (Enc.size a + 1) ^ d`), and `RAM.QuasiPolyFun f` likewise.  Its rules —
`RAM.PolyFun.comp`, `..pair`, `..ite`, `..iterate`, `RAM.polyFun_id`, `..const`, `..fst`,
`..snd`, `..add`, `..sub`, `..min`, `..max`, `..le`, `..natSize`, `..log2`, and the
`QuasiPolyFun` forms — carry no side condition at all except in `iterate`, where the number of
rounds and the size of the intermediate states must still be bounded by hand.  The derived forms
`RAM.PolyFun.op₂`, `..add`, `..sub`, `..min'`, `..max'`, `..le`, `..natEq`, `RAM.polyFun_swap`,
`RAM.polyFun_natEq` are the shapes a procedure is written in, and `RAM.PolyFun.of_eq` transfers
membership along a pointwise identity, which is how an assembled composite is turned into the
function one meant to write.  **This is the interface a later section should use.**

## Not available yet, and why

The mechanism for a procedure call that keeps the caller's data is `RAM.runsTo_reloc`
(`Workspace/Machine/Reloc.lean`): the callee is relocated to a base address `d` held in a
reserved register, so it works at addresses `d` and above and the caller keeps everything below
`d`.  `Workspace/Machine/Layout.lean` turns it into a stage calculus for routines of the
workspace convention, and `Pairing.lean`, `Combine.lean`, `Iterate.lean` build the combinators
above from it.  What is still missing:

* **The workspace convention back to the top-level convention**: `RAM.PolyFun f → RAM.PolyTime f`
  and `RAM.QuasiPolyFun f → RAM.QuasiPolyTime f`, which is needed once, for the final theorem.
  The relocation of `Reloc.lean` goes the other way and does not give it.  "What remains" item 1
  of `Workspace/Machine/DESIGN.md` now contains a **complete construction** for it — a parking
  phase, a halving loop, a descending shift loop and a descending read-back — with every
  disjointness side condition checked; what is missing is only the Lean text, about a hundred
  machine instructions carried through the Hoare rules.  Nothing else in this file depends on it.
* **Multiplication and division with remainder.**  Not blocked by anything above: the input
  `(a, b) : ℕ × ℕ` occupies a fixed number of registers, so `RAM.Small.cleanCompute_binary`
  packages them as it packages `+`, `min` and `≤`.  What is missing is only the two routines
  themselves, the nested loops described in the module docstring of `Arith.lean`.
* **The list primitives** (length, `get`, `set`, `cons`, append, `range`, `map`, `filter`,
  `foldl`).  The *encodings* are all in place already (`RAM.Enc` is defined for `List α` for
  every `Enc α`, hence for nested lists, for `Fin n → α` and for `Equiv.Perm (Fin n)`), and
  `map`, `filter`, `foldl` are bounded iterations (`RAM.PolyFun.iterate`) over a state
  `(done, todo)` once the *destructor* is available.  The one genuinely missing machine routine
  is that destructor, `uncons : List α → Option (α × List α)`: the encoding of `a :: l` is
  `frame (encode a) ++ encList encode l` while that of `(a, l)` frames the tail as well, so
  `uncons` has to read the first frame's length out of the workspace and re-lay the two blocks.
  It is a `Layout.lean` assembly of the same shape as `Pairing.lean`, with the segment
  parameters `i`, `c` of `RAM.Layout.runsTo_pushBlock` taken from registers rather than fixed.
-/

namespace RAM
namespace Closure

variable {α β γ σ : Type*}

/-! ## The basic functions -/

/-- The identity is computed by the empty program in zero steps. -/
theorem polyTime_id [Enc α] : PolyTimeClean (id : α → α) := polyTimeClean_id

/-- A constant function is computed cleanly in linear time (erase the input, write the
answer). -/
theorem polyTime_const [Enc α] [Enc β] (c : β) : PolyTimeClean (fun _ : α => c) :=
  polyTimeClean_const c

theorem quasiPolyTime_const [Enc α] [Enc β] (c : β) : QuasiPolyTimeClean (fun _ : α => c) :=
  quasiPolyTimeClean_const c

/-- Every function of one bit is computed cleanly in linear time. -/
theorem polyTime_ofBool [Enc β] (f : Bool → β) : PolyTimeClean f := polyTimeClean_ofBool f

/-- A conditional whose branches are constants, over a clean polynomial-time predicate. -/
theorem polyTime_ifConst [Enc α] [Enc β] {p : α → Bool} (hp : PolyTimeClean p) (c₁ c₀ : β) :
    PolyTimeClean (fun a => if p a then c₁ else c₀) := polyTimeClean_ifConst hp c₁ c₀

/-! ## Arithmetic on inputs of fixed shape

For an input whose encoding occupies a fixed number of registers the scratch registers may have
fixed indices, so the routines of `Arith.lean` apply directly; `Workspace/Machine/Small.lean`
packages them. -/

/-- The bit length `Nat.size`, in `6 * Nat.size a + 16` steps. -/
theorem polyTime_size : PolyTimeClean (fun a : ℕ => Nat.size a) := Small.polyTimeClean_size

/-- The binary logarithm. -/
theorem polyTime_log2 : PolyTimeClean (fun a : ℕ => Nat.log 2 a) := Small.polyTimeClean_log2

theorem polyTime_add : PolyTimeClean (fun p : ℕ × ℕ => p.1 + p.2) := Small.polyTimeClean_add

/-- Truncated subtraction, which is the machine's own operation. -/
theorem polyTime_sub : PolyTimeClean (fun p : ℕ × ℕ => p.1 - p.2) := Small.polyTimeClean_sub

theorem polyTime_min : PolyTimeClean (fun p : ℕ × ℕ => min p.1 p.2) := Small.polyTimeClean_min

theorem polyTime_max : PolyTimeClean (fun p : ℕ × ℕ => max p.1 p.2) := Small.polyTimeClean_max

theorem polyTime_le : PolyTimeClean (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) :=
  Small.polyTimeClean_le

/-! ## Composition -/

/-- **Composition in polynomial time.**  The size hypothesis is genuinely needed: a `T`-step
program can write an output whose *encoding* is exponentially long. -/
theorem polyTime_comp [Enc α] [Enc β] [Enc γ] {f : α → β} {g : β → γ} {S : ℕ → ℕ}
    (hf : PolyTimeClean f) (hg : PolyTimeClean g) (hSpoly : PolyBound S)
    (hS : ∀ a, Enc.size (f a) ≤ S (Enc.size a)) : PolyTimeClean (fun a => g (f a)) :=
  hf.comp hg hSpoly hS

/-- **Composition in quasipolynomial time.** -/
theorem quasiPolyTime_comp [Enc α] [Enc β] [Enc γ] {f : α → β} {g : β → γ} {S : ℕ → ℕ}
    (hf : QuasiPolyTimeClean f) (hg : QuasiPolyTimeClean g) (hSpoly : PolyBound S)
    (hS : ∀ a, Enc.size (f a) ≤ S (Enc.size a)) : QuasiPolyTimeClean (fun a => g (f a)) :=
  hf.comp hg hSpoly hS

theorem quasiPolyTime_comp_poly [Enc α] [Enc β] [Enc γ] {f : α → β} {g : β → γ} {S : ℕ → ℕ}
    (hf : QuasiPolyTimeClean f) (hg : PolyTimeClean g) (hSpoly : PolyBound S)
    (hS : ∀ a, Enc.size (f a) ≤ S (Enc.size a)) : QuasiPolyTimeClean (fun a => g (f a)) :=
  hf.comp_poly hg hSpoly hS

theorem quasiPolyTime_comp_quasi [Enc α] [Enc β] [Enc γ] {f : α → β} {g : β → γ} {S : ℕ → ℕ}
    (hf : PolyTimeClean f) (hg : QuasiPolyTimeClean g) (hSpoly : PolyBound S)
    (hS : ∀ a, Enc.size (f a) ≤ S (Enc.size a)) : QuasiPolyTimeClean (fun a => g (f a)) :=
  hf.comp_quasi hg hSpoly hS

/-- **Composition of search problems**, the form in which the paper's reductions appear (a
routine returns *some* admissible answer, for instance some generating set). -/
theorem polyTimeRel_comp [Enc α] [Enc β] [Enc γ] {R : α → β → Prop} {R' : β → γ → Prop}
    {S : ℕ → ℕ} (hR : PolyTimeCleanRel R) (hR' : PolyTimeCleanRel R') (hSpoly : PolyBound S)
    (hS : ∀ a b, R a b → Enc.size b ≤ S (Enc.size a)) :
    PolyTimeCleanRel (fun a c => ∃ b, R a b ∧ R' b c) := hR.comp hR' hSpoly hS

theorem quasiPolyTimeRel_comp [Enc α] [Enc β] [Enc γ] {R : α → β → Prop} {R' : β → γ → Prop}
    {S : ℕ → ℕ} (hR : QuasiPolyTimeCleanRel R) (hR' : QuasiPolyTimeCleanRel R')
    (hSpoly : PolyBound S) (hS : ∀ a b, R a b → Enc.size b ≤ S (Enc.size a)) :
    QuasiPolyTimeCleanRel (fun a c => ∃ b, R a b ∧ R' b c) := hR.comp hR' hSpoly hS

/-! ## Recursion

The scheme of Sec. 11.4 of the paper: `q(n)` calls, `p(n)` work per call.  The recursion is run
by keeping the pending calls as data; see `Workspace/Machine/Recursion.lean`. -/

/-- **The recursion theorem in polynomial time.** -/
theorem polyTime_recursion [Enc α] [Enc β] [Enc σ] {P₁ Q P₃ : Program}
    {setUp : α → ℕ × σ} {step : σ → σ} {readOff : σ → β} {T₁ T₂ T₃ p q u : ℕ → ℕ}
    (hP₁ : CleanCompute P₁ setUp T₁) (hT₁ : PolyBound T₁)
    (hQ : CleanCompute Q (fun x : ℕ × σ => (x.1 - 1, step x.2)) T₂)
    (hP₃ : CleanCompute P₃ (fun x : ℕ × σ => readOff x.2) T₃)
    (hq : ∀ a : α, (setUp a).1 ≤ q (Enc.size a)) (hqb : PolyBound q)
    (hp : ∀ (a : α), ∀ j < (setUp a).1,
      T₂ (Enc.size (((setUp a).1 - j, step^[j] (setUp a).2) : ℕ × σ)) ≤ p (Enc.size a))
    (hpb : PolyBound p)
    (hu : ∀ a : α,
      T₃ (Enc.size ((0, step^[(setUp a).1] (setUp a).2) : ℕ × σ)) ≤ u (Enc.size a))
    (hub : PolyBound u) :
    PolyTimeClean (fun a => readOff (step^[(setUp a).1] (setUp a).2)) :=
  polyTimeClean_recursion hP₁ hT₁ hQ hP₃ hq hqb hp hpb hu hub

/-- **The recursion theorem in quasipolynomial time**, the form Sec. 11.4 uses. -/
theorem quasiPolyTime_recursion [Enc α] [Enc β] [Enc σ] {P₁ Q P₃ : Program}
    {setUp : α → ℕ × σ} {step : σ → σ} {readOff : σ → β} {T₁ T₂ T₃ p q u : ℕ → ℕ}
    (hP₁ : CleanCompute P₁ setUp T₁) (hT₁ : QuasiPolyBound T₁)
    (hQ : CleanCompute Q (fun x : ℕ × σ => (x.1 - 1, step x.2)) T₂)
    (hP₃ : CleanCompute P₃ (fun x : ℕ × σ => readOff x.2) T₃)
    (hq : ∀ a : α, (setUp a).1 ≤ q (Enc.size a)) (hqb : QuasiPolyBound q)
    (hp : ∀ (a : α), ∀ j < (setUp a).1,
      T₂ (Enc.size (((setUp a).1 - j, step^[j] (setUp a).2) : ℕ × σ)) ≤ p (Enc.size a))
    (hpb : QuasiPolyBound p)
    (hu : ∀ a : α,
      T₃ (Enc.size ((0, step^[(setUp a).1] (setUp a).2) : ℕ × σ)) ≤ u (Enc.size a))
    (hub : QuasiPolyBound u) :
    QuasiPolyTimeClean (fun a => readOff (step^[(setUp a).1] (setUp a).2)) :=
  quasiPolyTimeClean_recursion hP₁ hT₁ hQ hP₃ hq hqb hp hpb hu hub

/-! ## Pairing, projections, the conditional and iteration at the workspace convention

These are the combinators that need a workspace: they lay out several results in memory at once,
so they need registers with fixed indices.  They are built in `Workspace/Machine/Pairing.lean`,
`Combine.lean` and `Iterate.lean`. -/

/-- **Pairing.**  The size hypotheses are genuinely needed, for the same reason as in
`polyTime_comp`: the result of a `T`-step clean routine may have an exponentially long
encoding, and the pairing routine copies both results. -/
theorem polyTimeAt_pair [Enc α] [Enc β] [Enc γ] {K : ℕ} (hK : 16 ≤ K) {f : α → β} {g : α → γ}
    {Sf Sg : ℕ → ℕ} (hf : PolyTimeCleanAt K f) (hg : PolyTimeCleanAt K g) (hSfb : PolyBound Sf)
    (hSgb : PolyBound Sg) (hSf : ∀ a, Enc.size (f a) ≤ Sf (Enc.size a))
    (hSg : ∀ a, Enc.size (g a) ≤ Sg (Enc.size a)) :
    PolyTimeCleanAt K (fun a => (f a, g a)) :=
  polyTimeCleanAt_pair hK hf hg hSfb hSgb hSf hSg

theorem quasiPolyTimeAt_pair [Enc α] [Enc β] [Enc γ] {K : ℕ} (hK : 16 ≤ K) {f : α → β}
    {g : α → γ} {Sf Sg : ℕ → ℕ} (hf : QuasiPolyTimeCleanAt K f) (hg : QuasiPolyTimeCleanAt K g)
    (hSfb : PolyBound Sf) (hSgb : PolyBound Sg) (hSf : ∀ a, Enc.size (f a) ≤ Sf (Enc.size a))
    (hSg : ∀ a, Enc.size (g a) ≤ Sg (Enc.size a)) :
    QuasiPolyTimeCleanAt K (fun a => (f a, g a)) :=
  quasiPolyTimeCleanAt_pair hK hf hg hSfb hSgb hSf hSg

/-- **The projections.** -/
theorem polyTimeAt_fst [Enc α] [Enc β] {K : ℕ} (hK : 16 ≤ K) :
    PolyTimeCleanAt K (Prod.fst : α × β → α) := polyTimeCleanAt_fst hK

theorem polyTimeAt_snd [Enc α] [Enc β] {K : ℕ} (hK : 16 ≤ K) :
    PolyTimeCleanAt K (Prod.snd : α × β → β) := polyTimeCleanAt_snd hK

/-- **The conditional.** -/
theorem polyTimeAt_ite [Enc α] [Enc β] {K : ℕ} (hK : 16 ≤ K) {p : α → Bool} {f g : α → β}
    (hp : PolyTimeCleanAt K p) (hf : PolyTimeCleanAt K f) (hg : PolyTimeCleanAt K g) :
    PolyTimeCleanAt K (fun a => if p a then f a else g a) := polyTimeCleanAt_ite hK hp hf hg

/-- **The recursion theorem at the workspace convention.** -/
theorem polyTimeAt_recursion [Enc α] [Enc β] [Enc σ] {K : ℕ} {P₁ Q P₃ : Program}
    {setUp : α → ℕ × σ} {step : σ → σ} {readOff : σ → β} {T₁ T₂ T₃ p q u : ℕ → ℕ}
    (hP₁ : CleanComputeAt K P₁ setUp T₁) (hT₁ : PolyBound T₁)
    (hQ : CleanComputeAt K Q (fun x : ℕ × σ => (x.1 - 1, step x.2)) T₂)
    (hP₃ : CleanComputeAt K P₃ (fun x : ℕ × σ => readOff x.2) T₃)
    (hq : ∀ a : α, (setUp a).1 ≤ q (Enc.size a)) (hqb : PolyBound q)
    (hp : ∀ (a : α), ∀ j < (setUp a).1,
      T₂ (Enc.size (((setUp a).1 - j, step^[j] (setUp a).2) : ℕ × σ)) ≤ p (Enc.size a))
    (hpb : PolyBound p)
    (hu : ∀ a : α,
      T₃ (Enc.size ((0, step^[(setUp a).1] (setUp a).2) : ℕ × σ)) ≤ u (Enc.size a))
    (hub : PolyBound u) :
    PolyTimeCleanAt K (fun a => readOff (step^[(setUp a).1] (setUp a).2)) :=
  polyTimeCleanAt_recursion hP₁ hT₁ hQ hP₃ hq hqb hp hpb hu hub

theorem quasiPolyTimeAt_recursion [Enc α] [Enc β] [Enc σ] {K : ℕ} {P₁ Q P₃ : Program}
    {setUp : α → ℕ × σ} {step : σ → σ} {readOff : σ → β} {T₁ T₂ T₃ p q u : ℕ → ℕ}
    (hP₁ : CleanComputeAt K P₁ setUp T₁) (hT₁ : QuasiPolyBound T₁)
    (hQ : CleanComputeAt K Q (fun x : ℕ × σ => (x.1 - 1, step x.2)) T₂)
    (hP₃ : CleanComputeAt K P₃ (fun x : ℕ × σ => readOff x.2) T₃)
    (hq : ∀ a : α, (setUp a).1 ≤ q (Enc.size a)) (hqb : QuasiPolyBound q)
    (hp : ∀ (a : α), ∀ j < (setUp a).1,
      T₂ (Enc.size (((setUp a).1 - j, step^[j] (setUp a).2) : ℕ × σ)) ≤ p (Enc.size a))
    (hpb : QuasiPolyBound p)
    (hu : ∀ a : α,
      T₃ (Enc.size ((0, step^[(setUp a).1] (setUp a).2) : ℕ × σ)) ≤ u (Enc.size a))
    (hub : QuasiPolyBound u) :
    QuasiPolyTimeCleanAt K (fun a => readOff (step^[(setUp a).1] (setUp a).2)) :=
  quasiPolyTimeCleanAt_recursion hP₁ hT₁ hQ hP₃ hq hqb hp hpb hu hub

/-- **Bounded iteration** `a ↦ step^[k a] a`: `q` bounds the number of iterations and `p` the
size of every value the iteration passes through. -/
theorem polyTimeAt_iterate [Enc α] {K : ℕ} (hK : 16 ≤ K) {step : α → α} {k : α → ℕ}
    {q p : ℕ → ℕ} (hstep : PolyTimeCleanAt K (fun x : ℕ × α => (x.1 - 1, step x.2)))
    (hk : PolyTimeCleanAt K (fun a => (k a, a)))
    (hq : ∀ a : α, k a ≤ q (Enc.size a)) (hqb : PolyBound q)
    (hp : ∀ (a : α), ∀ j ≤ k a, Enc.size ((k a - j, step^[j] a) : ℕ × α) ≤ p (Enc.size a))
    (hpb : PolyBound p) : PolyTimeCleanAt K (fun a => step^[k a] a) :=
  polyTimeCleanAt_iterate hK hstep hk hq hqb hp hpb

theorem quasiPolyTimeAt_iterate [Enc α] {K : ℕ} (hK : 16 ≤ K) {step : α → α} {k : α → ℕ}
    {q p : ℕ → ℕ} (hstep : QuasiPolyTimeCleanAt K (fun x : ℕ × α => (x.1 - 1, step x.2)))
    (hk : QuasiPolyTimeCleanAt K (fun a => (k a, a)))
    (hq : ∀ a : α, k a ≤ q (Enc.size a)) (hqb : QuasiPolyBound q)
    (hp : ∀ (a : α), ∀ j ≤ k a, Enc.size ((k a - j, step^[j] a) : ℕ × α) ≤ p (Enc.size a))
    (hpb : QuasiPolyBound p) : QuasiPolyTimeCleanAt K (fun a => step^[k a] a) :=
  quasiPolyTimeCleanAt_iterate hK hstep hk hq hqb hp hpb

/-! ## From the clean classes to the time classes of layer (a) -/

theorem polyTime_of_clean [Enc α] [Enc β] {f : α → β} (h : PolyTimeClean f) : PolyTime f :=
  h.polyTime

theorem quasiPolyTime_of_clean [Enc α] [Enc β] {f : α → β} (h : QuasiPolyTimeClean f) :
    QuasiPolyTime f := h.quasiPolyTime

theorem polyTimeRel_of_clean [Enc α] [Enc β] {R : α → β → Prop} (h : PolyTimeCleanRel R) :
    PolyTimeRel R := h.polyTimeRel

theorem quasiPolyTimeRel_of_clean [Enc α] [Enc β] {R : α → β → Prop}
    (h : QuasiPolyTimeCleanRel R) : QuasiPolyTimeRel R := h.quasiPolyTimeRel

/-- A polynomial-time clean function is quasipolynomial-time clean. -/
theorem quasiPolyTime_of_polyTime [Enc α] [Enc β] {f : α → β} (h : PolyTimeClean f) :
    QuasiPolyTimeClean f := h.quasiPolyTimeClean

/-! ## The workspace convention

`RAM.initMemAt K l` is the top-level convention with `K` zeroed work registers below it
(`Workspace/Machine/Offset.lean`).  It exists because at the top-level convention no register
with a fixed index is free, so no routine can even set a loop counter.  Everything proved at the
top-level convention transfers to it by relocation (`Workspace/Machine/Reloc.lean`), at ten times
the cost plus four steps; the converse direction is still missing. -/

/-- A clean polynomial-time routine is one at the workspace convention with `K ≥ 3` work
registers. -/
theorem polyTimeAt_of_polyTime [Enc α] [Enc β] {f : α → β} {K : ℕ} (hK : 3 ≤ K)
    (h : PolyTimeClean f) : PolyTimeCleanAt K f := polyTimeCleanAt_of_polyTimeClean hK h

theorem quasiPolyTimeAt_of_quasiPolyTime [Enc α] [Enc β] {f : α → β} {K : ℕ} (hK : 3 ≤ K)
    (h : QuasiPolyTimeClean f) : QuasiPolyTimeCleanAt K f :=
  quasiPolyTimeCleanAt_of_quasiPolyTimeClean hK h

theorem polyTimeRelAt_of_polyTimeRel [Enc α] [Enc β] {R : α → β → Prop} {K : ℕ} (hK : 3 ≤ K)
    (h : PolyTimeCleanRel R) : PolyTimeCleanRelAt K R := polyTimeCleanRelAt_of_polyTimeCleanRel hK h

theorem quasiPolyTimeRelAt_of_quasiPolyTimeRel [Enc α] [Enc β] {R : α → β → Prop} {K : ℕ}
    (hK : 3 ≤ K) (h : QuasiPolyTimeCleanRel R) : QuasiPolyTimeCleanRelAt K R :=
  quasiPolyTimeCleanRelAt_of_quasiPolyTimeCleanRel hK h

/-- **Composition at the workspace convention.** -/
theorem polyTimeAt_comp [Enc α] [Enc β] [Enc γ] {K : ℕ} {f : α → β} {g : β → γ} {S : ℕ → ℕ}
    (hf : PolyTimeCleanAt K f) (hg : PolyTimeCleanAt K g) (hSpoly : PolyBound S)
    (hS : ∀ a, Enc.size (f a) ≤ S (Enc.size a)) : PolyTimeCleanAt K (fun a => g (f a)) :=
  hf.comp hg hSpoly hS

theorem quasiPolyTimeAt_comp [Enc α] [Enc β] [Enc γ] {K : ℕ} {f : α → β} {g : β → γ} {S : ℕ → ℕ}
    (hf : QuasiPolyTimeCleanAt K f) (hg : QuasiPolyTimeCleanAt K g) (hSpoly : PolyBound S)
    (hS : ∀ a, Enc.size (f a) ≤ S (Enc.size a)) : QuasiPolyTimeCleanAt K (fun a => g (f a)) :=
  hf.comp hg hSpoly hS

end Closure
end RAM
