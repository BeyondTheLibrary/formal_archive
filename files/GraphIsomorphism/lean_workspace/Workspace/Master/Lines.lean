/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15: the individual lines of Procedure String-Isomorphism.
-/
import Workspace.Master.Assemble
import Workspace.Master.Bridge
import Workspace.TopAction.TopAction4

/-!
# The lines of Sec. 15, one at a time

`Workspace/Master/Assemble.lean` turns seven branches into one round
(`Babai.Sec15Inputs`, `Babai.masterStep_of_procedure`).  This file fills the branches with
the **named** reductions of Secs. 11–14 and proves, for each of them, the three facts the
round needs: the branch is correct, every instance it produces makes progress, and it makes
few calls.

What is here:

* line 4a (`Babai.line4aReduction`): the trivial case `t = 1`.  The branch is a leaf: it
  returns a set that is written down directly from the strings, with no recursive call.
* line 4b (`Babai.topAction4Reduction`, Sec. 12): Cor. 12.0.10.  Correctness, the progress
  `3n' ≤ 2n` (`Babai.decreases_topAction4Reduction`) and the call count
  (`Babai.calls_length_topAction4Reduction`) all sit next to `Babai.Corollary_12_0_10` in
  `Workspace/TopAction/TopAction4.lean`.
* lines 4c and 4d, and lines 6a and 7a (`Babai.designAlignReduction`): the Extended Design
  Lemma's canonical structure, the `q(m)`-fold branching over its versions
  (`Workspace/Master/Bridge.lean`), Procedure Align on each branch, and the Chain Rule over
  the color classes.

What is not here: lines 1, 2 and 5.  Procedure Reduce-to-Johnson (§11.3), the imprimitive
Luks reduction of line 2 and Procedure AggregateCertificates (Thm. 13.2.1) are not yet
available as named reductions; `Workspace/Master/DESIGN.md` says under "Mismatches" what
each of them would have to provide.
-/

universe u v w

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise

/-! ### Line 4a: the trivial case `t = 1`

> 4a. if `t = 1` then find `Iso_G(x,y)`, exit (: trivial case: `Ω = Γ`, `G ≥ A(Ω)`;
>     isomorphism only depends on the multiplicity of each letter in the strings `x, y` :)

The branch makes no recursive call, so what has to be said about it is only that the set it
returns is `Iso^Δ_K(x,y)`, and that this set is written down directly from the strings. -/

section Line4a

variable {Ω : Type u} {A : Type v}

/-- The number of positions of the window `Δ` that carry the letter `a`: the *multiplicity*
of `a` in the string `x`, in the sense of line 4a of Sec. 15. -/
noncomputable def letterMult (Δ : Set Ω) (x : Ω → A) (a : A) : ℕ := {u ∈ Δ | x u = a}.ncard

/-- §15, line 4a: the answer, written down directly from the strings — the permutations of
the candidate set that match `x` and `y` position by position on the window. -/
def matchingSet (K : Set (Equiv.Perm Ω)) (Δ : Set Ω) (x y : Ω → A) : Set (Equiv.Perm Ω) :=
  {τ ∈ K | ∀ u ∈ Δ, x u = y (τ u)}

/-- §15, **line 4a** as a reduction: *"find `Iso_G(x,y)`, exit"* — a leaf, with no
recursive call. -/
def line4aReduction (I : SIInstance Ω A) : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  .done (matchingSet I.K I.Δ I.x I.y)

/-- Line 4a returns the answer. -/
theorem run_line4aReduction (I : SIInstance Ω A) :
    (line4aReduction I).run = I.answer := rfl

/-- Line 4a makes no recursive call: it exits. -/
theorem calls_line4aReduction (I : SIInstance Ω A) : (line4aReduction I).calls = [] := rfl

/-- §15, line 4a, the easy half of the parenthetical *"isomorphism only depends on the
multiplicity of each letter"*: an isomorphism matches the letters position by position, so
it makes the multiplicities agree.

*Proof.*  If `τ ∈ Iso_K(x,y)` then `x = y ∘ τ`, so `τ` maps `{u | x u = a}` onto
`{u | y u = a}` bijectively. -/
theorem letterMult_eq_of_mem_strIso [Finite Ω] {K : Set (Equiv.Perm Ω)} {x y : Ω → A}
    {τ : Equiv.Perm Ω} (hτ : τ ∈ strIso K x y) (a : A) :
    letterMult Set.univ x a = letterMult Set.univ y a := by
  have hxy : ∀ u, x u = y (τ u) := by
    intro u
    have := congrArg (fun z : Ω → A => z (τ u)) hτ.2
    simpa [strAct] using this
  have himg : (fun u => τ u) '' {u | x u = a} = {u | y u = a} := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      show y (τ u) = a
      rw [← hxy u]; exact hu
    · intro hv
      refine ⟨τ⁻¹ v, ?_, by simp⟩
      show x (τ⁻¹ v) = a
      rw [hxy (τ⁻¹ v)]
      simpa using hv
  have hcard : {u : Ω | x u = a}.ncard = {u : Ω | y u = a}.ncard := by
    rw [← himg]
    exact (Set.ncard_image_of_injective _ (Equiv.injective _)).symm
  simpa [letterMult, Set.sep_univ] using hcard

/-- §15, line 4a, the other half of *"isomorphism only depends on the multiplicity of each
letter"*, **as the paper's comment would have it**: for `G ≥ A(Ω)`, equal multiplicities
give an isomorphism.

This is false as stated; `Babai.line4a_multiplicities_not_sufficient` below is a
counterexample.  It becomes true once some letter occurs at least twice, which is the form
stated here.  See the entry "Sec. 15, line 4a" in the corrected paper.

*Proof.*  Equal multiplicities make the fibers of `x` and of `y` equinumerous, so a family
of bijections between them glues to a permutation `e` of `Ω` with `y(e u) = x u` for every
`u` (`Equiv.ofFiberEquiv`), that is `x^e = y`.  If `e` is even we are done.  If it is odd,
let `u ≠ v` be two positions where `x` has the same letter — they exist because `x` is not
injective — and replace `e` by `e·(u v)`: the transposition fixes `x`, so the product is
still an isomorphism, and its sign is the opposite one. -/
theorem line4a_nonempty_of_letterMult [Fintype Ω] [DecidableEq Ω]
    {G : Subgroup (Equiv.Perm Ω)} (hG : alternatingGroup Ω ≤ G) (x y : Ω → A)
    (hrep : ¬ Function.Injective x)
    (hmult : ∀ a : A, letterMult Set.univ x a = letterMult Set.univ y a) :
    (strIso (G : Set (Equiv.Perm Ω)) x y).Nonempty := by
  classical
  -- the fibers of `x` and of `y` are equinumerous
  have hfib : ∀ a : A, Nonempty ({u // x u = a} ≃ {u // y u = a}) := by
    intro a
    refine ⟨Fintype.equivOfCardEq ?_⟩
    have h1 : Nat.card {u // x u = a} = Nat.card {u // y u = a} := by
      show ({u | x u = a} : Set Ω).ncard = ({u | y u = a} : Set Ω).ncard
      have h := hmult a
      rwa [letterMult, letterMult, Set.sep_univ, Set.sep_univ] at h
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h1
  have eFib : ∀ a : A, {u // x u = a} ≃ {u // y u = a} := fun a => (hfib a).some
  -- the permutation they glue to
  set e : Equiv.Perm Ω := Equiv.ofFiberEquiv eFib with he
  have hey : ∀ u : Ω, y (e u) = x u := fun u => Equiv.ofFiberEquiv_map eFib u
  have hact : strAct x e = y := by
    funext v
    show x (e⁻¹ v) = y v
    have h := hey (e⁻¹ v)
    have h' : e (e⁻¹ v) = v := by simp
    rw [h'] at h
    exact h.symm
  by_cases hsign : e ∈ alternatingGroup Ω
  · exact ⟨e, hG hsign, hact⟩
  -- `e` is odd: correct it by a transposition that fixes `x`
  obtain ⟨u, v, huv, hne⟩ : ∃ u v : Ω, x u = x v ∧ u ≠ v := by
    rw [Function.Injective] at hrep
    push_neg at hrep
    obtain ⟨u, v, h1, h2⟩ := hrep
    exact ⟨u, v, h1, h2⟩
  have hxτ : strAct x (Equiv.swap u v) = x := by
    funext w
    show x ((Equiv.swap u v)⁻¹ w) = x w
    rw [Equiv.swap_inv]
    rcases eq_or_ne w u with rfl | hw1
    · rw [Equiv.swap_apply_left]; exact huv.symm
    · rcases eq_or_ne w v with rfl | hw2
      · rw [Equiv.swap_apply_right]; exact huv
      · rw [Equiv.swap_apply_of_ne_of_ne hw1 hw2]
  refine ⟨e * Equiv.swap u v, hG ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup] at hsign ⊢
    have hone : Equiv.Perm.sign e = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h
      · exact absurd h hsign
      · exact h
    rw [map_mul, hone, Equiv.Perm.sign_swap hne]
    decide
  · rw [strAct_mul x (Equiv.swap u v) e, hxτ, hact]

/-- §15, line 4a: the paper's parenthetical *"isomorphism only depends on the multiplicity
of each letter in the strings `x, y`"* is false for `G = A(Ω)`.

Take `Ω = Σ = {0,1,2}`, `x` the identity string and `y = x^{(0 1)}`.  Every letter occurs
once in each of `x` and `y`, so the multiplicities agree; but the only permutation carrying
`x` to `y` is the transposition `(0 1)`, which is not in `A(Ω)`, so `Iso_{A(Ω)}(x,y) = ∅`.
(For `G = S(Ω)` the comment is correct, and it is correct for `G = A(Ω)` as soon as some
letter occurs at least twice.) -/
theorem line4a_multiplicities_not_sufficient :
    ∃ (x y : Fin 3 → Fin 3),
      (∀ a : Fin 3, letterMult Set.univ x a = letterMult Set.univ y a) ∧
        strIso ((alternatingGroup (Fin 3) : Subgroup (Equiv.Perm (Fin 3))) :
          Set (Equiv.Perm (Fin 3))) x y = ∅ := by
  classical
  refine ⟨id, strAct id (Equiv.swap 0 1), ?_, ?_⟩
  · intro a
    have h : (Equiv.swap (0 : Fin 3) 1) ∈
        strIso (Set.univ : Set (Equiv.Perm (Fin 3))) (id : Fin 3 → Fin 3)
          (strAct id (Equiv.swap 0 1)) := ⟨trivial, rfl⟩
    exact letterMult_eq_of_mem_strIso h a
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro τ ⟨hτA, hτ⟩
    -- `x^τ = x^{(0 1)}` forces `τ = (0 1)`, which is odd
    have hinv : τ⁻¹ = (Equiv.swap (0 : Fin 3) 1)⁻¹ := by
      refine Equiv.ext fun u => ?_
      have := congrFun hτ u
      simpa [strAct] using this
    have hτeq : τ = Equiv.swap (0 : Fin 3) 1 := by
      have := congrArg (fun σ : Equiv.Perm (Fin 3) => σ⁻¹) hinv
      simpa using this
    rw [hτeq] at hτA
    have hs : Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) = 1 :=
      Equiv.Perm.mem_alternatingGroup.1 hτA
    rw [Equiv.Perm.sign_swap (by decide)] at hs
    exact absurd hs (by decide)

end Line4a

/-! ### Line 4b: Corollary 12.0.10

> 4b. else (: `t ≥ 2` :) view `x, y` as edge-colored `t`-uniform hypergraphs `H(x)` and
>     `H(y)` on vertex set `Γ`; if relative symmetry defect of `H(x)` is `< 1/2` then apply
>     Cor. 12.0.10

The named reduction is `Babai.topAction4Reduction` (Sec. 12), and Cor. 12.0.10
(`Babai.Corollary_12_0_10`) is its specification.  The three facts line 4b needs live next
to the corollary, in `Workspace/TopAction/TopAction4.lean`: correctness is the last clause
of the corollary, the progress `3n' ≤ 2n` is `Babai.decreases_topAction4Reduction`, and the
call count `≤ 7n` is `Babai.calls_length_topAction4Reduction`. -/

/-! ### Lines 4c and 4d, and lines 6a and 7a: the Design Lemma and Procedure Align

> 4c. else (: now their relative symmetry defect is `≥ 1/2` :) apply Extended Design Lemma
>     (Theorem 9.2.3)
> 4d. (: canonical structure `X` on `Γ` found: colored equipartition or Johnson scheme :)
>     apply Procedure Align to `X` (Sec. 14.1)

and, after line 5,

> 6a. apply Extended Design Lemma (Theorem 9.2.3); `X ←` canonical structure returned
> 7a. apply Procedure Align to `X` (Sec. 14.1)

Both are the same reduction.  The Extended Design Lemma reaches its canonical structure only
after individualization, so what is canonical is a whole tuple `Vers z` of versions of it
(Sec. 6), and Sec. 14.2 says to *"compare not one but `q(m)` instances of `X(y)` with
`X(x)`"*.  `Workspace/Master/Bridge.lean` has that step; here it is composed with Procedure
Align lines 1–3 (`Babai.alignBranch`) and lines 4–6, the Chain Rule over the color classes
of `X` (`Babai.alignChainReduction`). -/

section DesignAlign

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]
  {Γ : Type*} {𝒳 : Type*} [MulAction (Equiv.Perm Γ) 𝒳] {G : Subgroup (Equiv.Perm Ω)}

open scoped Classical in
/-- §15, **lines 4c and 4d** (equally, lines 6a and 7a): for the fixed version `X'` of the
canonical structure on `x`, branch over the versions `Y'` of the canonical structure on `y`;
on each branch align `y` by an element carrying `X'` to `Y'`, pass to
`G₁ = ϕ⁻¹(Aut(X'))`, and run the Chain Rule over the color classes `Δs` of `X'`. -/
noncomputable def designAlignReduction (ϕ : G →* Equiv.Perm Γ) (Vers : (Ω → A) → Set 𝒳)
    (x y : Ω → A) (hfin : (Vers y).Finite) (X' : 𝒳) (Δs : List (Set Ω)) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  versionsReduction Vers y hfin
    (fun Y' => alignBranch ϕ y X' Y' (fun G₁ z => alignChainReduction G₁ Δs x z))

open scoped Classical in
/-- §15, lines 4c–4d: **the branch is correct**.  The color classes of the canonical
structure are invariant under `G₁ = ϕ⁻¹(Aut(X'))` and cover `Ω`, so the Chain Rule computes
`Iso_{G₁}(x, z)` (Sec. 14.1, lines 4–6); by Eq. (70) each version-branch is then the piece
of `Iso_G(x,y)` belonging to that version, and by Eq. (40) the union of the pieces is
`Iso_G(x,y)`. -/
theorem run_designAlignReduction {ϕ : G →* Equiv.Perm Γ} {Vers : (Ω → A) → Set 𝒳}
    (hcan : IsCanonicalVersions ϕ Vers) (x y : Ω → A) {X' : 𝒳} (hX' : X' ∈ Vers x)
    (hfin : (Vers y).Finite) (Δs : List (Set Ω))
    (hinv : ∀ Δ ∈ Δs, IsInvariant (preimageSubgroup ϕ (structAut X')) Δ)
    (hcov : (⋃ Δ ∈ Δs, Δ) = (Set.univ : Set Ω)) :
    (designAlignReduction ϕ Vers x y hfin X' Δs).run =
      strIso (G : Set (Equiv.Perm Ω)) x y :=
  run_versionsReduction hcan x y hX' hfin _
    (fun Y' _ => run_alignBranch x y X' Y' _
      (fun z => run_alignChainReduction x z hinv hcov))

open scoped Classical in
/-- §15, lines 4c–4d, **the multiplicative cost of Eq. (71)**: the branch makes at most
`q · |Δs|` calls, where `q` bounds the number of versions of `X(y)` and `|Δs|` is the number
of color classes of `X'`, one Chain Rule call each. -/
theorem calls_length_designAlignReduction {ϕ : G →* Equiv.Perm Γ} {Vers : (Ω → A) → Set 𝒳}
    (x y : Ω → A) (hfin : (Vers y).Finite) (X' : 𝒳) (Δs : List (Set Ω)) {q : ℕ}
    (hq : (Vers y).ncard ≤ q) :
    ((designAlignReduction ϕ Vers x y hfin X' Δs).calls).length ≤ q * Δs.length :=
  calls_length_versionsReduction y hfin _ hq
    (fun Y' => calls_length_alignBranch y X' Y' _
      (fun G₁ z => calls_length_alignChainReduction G₁ Δs x z))

open scoped Classical in
/-- §15, lines 4c–4d: **every call has one of the color classes for its window**.  This is
what turns the sizes of the color classes of the canonical structure (a colored
`α`-partition, or a Johnson scheme on a large subset) into the progress
`Babai.MasterStep.decreases`. -/
theorem calls_designAlignReduction_window {ϕ : G →* Equiv.Perm Γ} {Vers : (Ω → A) → Set 𝒳}
    (x y : Ω → A) (hfin : (Vers y).Finite) (X' : 𝒳) (Δs : List (Set Ω)) :
    ∀ J ∈ (designAlignReduction ϕ Vers x y hfin X' Δs).calls, J.Δ ∈ Δs :=
  calls_versionsReduction y hfin _
    (fun Y' => calls_alignBranch y X' Y' _
      (fun G₁ z => calls_alignChainReduction_window G₁ Δs x z))

/-- §15, lines 4c–4d: **the progress**.  If every color class of the canonical structure has
at most `2n/3` elements, then every instance the branch produces has window size at most
`2n/3`.

This is the first branch of `Babai.MasterStep.decreases`.  The second branch — same window,
Johnson parameter at least halved — is Procedure Align lines 7–11 on the window of a
dominant color class, Eq. (73); it is not covered here (see `Workspace/Master/DESIGN.md`,
"Mismatches"). -/
theorem decreases_designAlignReduction {ϕ : G →* Equiv.Perm Γ} {Vers : (Ω → A) → Set 𝒳}
    (x y : Ω → A) (hfin : (Vers y).Finite) (X' : 𝒳) (Δs : List (Set Ω)) (n : ℕ)
    (hΔs : ∀ Δ ∈ Δs, 3 * Δ.ncard ≤ 2 * n) :
    ∀ J ∈ (designAlignReduction ϕ Vers x y hfin X' Δs).calls,
      3 * J.windowSize ≤ 2 * n := by
  classical
  intro J hJ
  exact hΔs J.Δ (calls_designAlignReduction_window x y hfin X' Δs J hJ)

open scoped Classical in
/-- §15, lines 4c–4d, **the progress, both forms**.  Sec. 14.2 splits the color classes of
the canonical structure into two kinds:

> we shall either reduce the domain (window) size `n` by a positive fraction, or reduce the
> Johnson parameter `k` by a positive fraction while not increasing `n`  (Sec. 11.4,
> explanation of item (v))

A color class with `5|Δ| ≤ 4n` is of the first kind.  There is at most one class that is
not, the *dominant* one, and on its window Procedure Align lines 7–11 replace `Γ` by the
reduced set `Γ*`, whose size is at most `m/2` (Eq. (73),
`Babai.Align_johnson_param_halved` and `Babai.Align_equipartition_param_halved` in
`Workspace/Canonical/AlignJohnson.lean`).  The hypothesis `hdom` is that conclusion for the
instances the branch produces.

Together these are exactly the two forms of `Babai.MakesProgress`. -/
theorem decreases_designAlignReduction_makesProgress {ι : Type*} {ϕ : G →* Equiv.Perm Γ}
    {Vers : (Ω → A) → Set 𝒳} (x y : Ω → A) (hfin : (Vers y).Finite) (X' : 𝒳)
    (Δs : List (Set Ω)) (win par : ι → ℕ) (i : ι) (lift : SIInstance Ω A → ι)
    (hwin : ∀ J : SIInstance Ω A, win (lift J) = J.windowSize)
    (hn : 1 ≤ win i)
    (hdom : ∀ J ∈ (designAlignReduction ϕ Vers x y hfin X' Δs).calls,
      5 * J.windowSize ≤ 4 * win i ∨
        (J.windowSize ≤ win i ∧ 1 ≤ par i ∧ 2 * par (lift J) ≤ par i)) :
    ∀ J ∈ (designAlignReduction ϕ Vers x y hfin X' Δs).calls,
      MakesProgress win par i (lift J) := by
  intro J hJ
  rcases hdom J hJ with h | h
  · exact Or.inl ⟨hn, by rw [hwin]; exact h⟩
  · exact Or.inr ⟨by rw [hwin]; exact h.1, h.2.1, h.2.2⟩

/-! ### Lines 4c-4d with a dominant color class: Procedure Align lines 7-11

> 6. If `(∃j)(|Δ_j| > m/2)` ("dominant color") then start the application of the Chain Rule
>    with the window `Ω(Δ_j)`.
> 7. … 11.

When the canonical structure has a dominant color class, the Chain Rule call on its window
is not answered by recursion on a smaller window — the window does not shrink — but by lines
7–11, which halve the Johnson parameter instead (Eq. (73)).  So the call is *expanded* by
the round of the dominant window (`Babai.AlignDominantRoundData.round`), and the calls of
that round are the ones passed to the recursion.  The expansion is written for an arbitrary
sub-reduction `f`, since the same wrapper serves the undominated case with `f` the trivial
one-call reduction. -/

open scoped Classical in
/-- §15, **lines 4c and 4d with a dominant color class**: the branch of
`Babai.designAlignReduction` with every Chain Rule call expanded by `f`. -/
noncomputable def designAlignDominantReduction (ϕ : G →* Equiv.Perm Γ)
    (Vers : (Ω → A) → Set 𝒳) (x y : Ω → A) (hfin : (Vers y).Finite) (X' : 𝒳)
    (Δs : List (Set Ω)) (f : SIInstance Ω A → SIReduction Ω A (Set (Equiv.Perm Ω))) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  (designAlignReduction ϕ Vers x y hfin X' Δs).expand f

open scoped Classical in
/-- §15, lines 4c–4d, **correctness**.  The sub-reduction has to be correct only on the
instances the Chain Rule produces, whose windows are the color classes. -/
theorem run_designAlignDominantReduction {ϕ : G →* Equiv.Perm Γ} {Vers : (Ω → A) → Set 𝒳}
    (hcan : IsCanonicalVersions ϕ Vers) (x y : Ω → A) {X' : 𝒳} (hX' : X' ∈ Vers x)
    (hfin : (Vers y).Finite) (Δs : List (Set Ω))
    (hinv : ∀ Δ ∈ Δs, IsInvariant (preimageSubgroup ϕ (structAut X')) Δ)
    (hcov : (⋃ Δ ∈ Δs, Δ) = (Set.univ : Set Ω))
    {f : SIInstance Ω A → SIReduction Ω A (Set (Equiv.Perm Ω))}
    (hf : ∀ J : SIInstance Ω A, J.Δ ∈ Δs → (f J).run = J.answer) :
    (designAlignDominantReduction ϕ Vers x y hfin X' Δs f).run =
      strIso (G : Set (Equiv.Perm Ω)) x y := by
  rw [designAlignDominantReduction,
    SIReduction.run_expand_of_calls hf _ (calls_designAlignReduction_window x y hfin X' Δs),
    run_designAlignReduction hcan x y hX' hfin Δs hinv hcov]

open scoped Classical in
/-- §15, lines 4c–4d, **the multiplicative cost**: `q` versions, `|Δs|` color classes, and
at most `c` calls for each expanded Chain Rule call. -/
theorem calls_length_designAlignDominantReduction {ϕ : G →* Equiv.Perm Γ}
    {Vers : (Ω → A) → Set 𝒳} (x y : Ω → A) (hfin : (Vers y).Finite) (X' : 𝒳)
    (Δs : List (Set Ω)) {q : ℕ} (hq : (Vers y).ncard ≤ q)
    {f : SIInstance Ω A → SIReduction Ω A (Set (Equiv.Perm Ω))} {c : ℕ}
    (hf : ∀ J : SIInstance Ω A, J.Δ ∈ Δs → (f J).run = J.answer)
    (hc : ∀ J : SIInstance Ω A, J.Δ ∈ Δs → (f J).calls.length ≤ c) :
    ((designAlignDominantReduction ϕ Vers x y hfin X' Δs f).calls).length
      ≤ q * Δs.length * c := by
  refine le_trans (SIReduction.calls_expand_length_le_of_calls hf hc _
    (calls_designAlignReduction_window x y hfin X' Δs)) ?_
  exact Nat.mul_le_mul_right c (calls_length_designAlignReduction x y hfin X' Δs hq)

open scoped Classical in
/-- §15, lines 4c–4d: **every call of the branch is a call of one of the sub-reductions**.
With `Q` the window bound this is `Babai.MasterStep.decreases`; with `Q` the group condition
it is `Babai.MasterStep.line4cd_group`. -/
theorem calls_designAlignDominantReduction {ϕ : G →* Equiv.Perm Γ} {Vers : (Ω → A) → Set 𝒳}
    (x y : Ω → A) (hfin : (Vers y).Finite) (X' : 𝒳) (Δs : List (Set Ω))
    {f : SIInstance Ω A → SIReduction Ω A (Set (Equiv.Perm Ω))}
    (hf : ∀ J : SIInstance Ω A, J.Δ ∈ Δs → (f J).run = J.answer)
    {Q : SIInstance Ω A → Prop}
    (hQ : ∀ J : SIInstance Ω A, J.Δ ∈ Δs → ∀ K ∈ (f J).calls, Q K) :
    ∀ K ∈ (designAlignDominantReduction ϕ Vers x y hfin X' Δs f).calls, Q K :=
  SIReduction.mem_calls_expand_of_calls hf hQ _
    (calls_designAlignReduction_window x y hfin X' Δs)

end DesignAlign

end Babai
