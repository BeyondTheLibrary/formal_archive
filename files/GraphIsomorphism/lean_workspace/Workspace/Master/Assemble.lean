/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15: the seven lines of Procedure String-Isomorphism, assembled into one round.
-/
import Workspace.Master.Cost

/-!
# The seven lines of Sec. 15, assembled

Sec. 15 reads, verbatim:

> **Procedure String-Isomorphism**
> Input: group `G ≤ S(Ω)`, strings `x, y : Ω → Σ`
> Output: `Iso_G(x,y)`
>
> 1. Apply Procedure Reduce-to-Johnson (Luks reductions, Sec. 11.3)
>    (: The rest of this algorithm constitutes the ProcessJohnsonAction routine announced
>    in Sec. 11.3 :)
> 2. (: `G` is transitive, `G`-action `Ḡ` on blocks is Johnson group isomorphic to `S_m` or
>    `A_m` :) set `ℓ = (log n)³`; if `m ≤ ℓ` then apply imprimitive Luks reduction to reduce
>    to kernel of the `G`-action on the blocks (brute force on small primitive group `Ḡ`,
>    multiplicative cost `ℓ!`)
> 3. (: `G`-action on blocks is isomorphic to `S(Γ)` or `A(Γ)`, `|Γ| = m > ℓ` :)
>    Let `ϕ : G → S(Γ)` be a giant representation (inferred from `G`)
>    Let `N = ker(ϕ)` and let `Φ = {B_T | T ∈ Γ^{(t)}}` be the set of standard blocks
>    (Thm. 10.5.1)
> 4. if `G` primitive (: i.e. `Ω = Φ` :)
> 4a.  if `t = 1` then find `Iso_G(x,y)`, exit (: trivial case: `Ω = Γ`, `G ≥ A(Ω)`;
>      isomorphism only depends on the multiplicity of each letter in the strings `x, y` :)
> 4b.  else (: `t ≥ 2` :) view `x, y` as edge-colored `t`-uniform hypergraphs `H(x)`, `H(y)`
>      on vertex set `Γ`; if relative symmetry defect of `H(x)` is `< 1/2` then apply
>      Cor. 12.0.10
> 4c.  else (: now their relative symmetry defect is `≥ 1/2` :) apply Extended Design Lemma
>      (Theorem 9.2.3)
> 4d.  (: canonical structure `X` on `Γ` found: colored equipartition or Johnson scheme :)
>      apply Procedure Align to `X` (Sec. 14.1)
> 5. else (: `G` imprimitive, i.e. `|Φ| ≤ (1/2)|Ω|` :) apply AggregateCertificates
>    (Theorem 13.2.1)
> 6.  if AggregateCertificates returns canonically embedded `k`-ary relational structure on
>     `Γ` with relative symmetry defect `≥ 1/2` then
> 6a.   apply Extended Design Lemma (Theorem 9.2.3); `X ←` canonical structure returned
> 7.  else (: AggregateCertificates returns canonical colored equipartition on `Γ` :)
>     `X ←` colored equipartition returned
> 7a. apply Procedure Align to `X` (Sec. 14.1)

Line 3 is not a branch; it fixes the notation (`ϕ`, `N`, `Φ`, `t`) that lines 4–7a use.  The
branches are therefore seven:

| branch | when it is taken |
|---|---|
| line 1 | the instance is not yet in the Johnson case |
| line 2 | Johnson case with `m ≤ ℓ` |
| line 4a | Johnson case, `m > ℓ`, `G` primitive, `t = 1` |
| line 4b | Johnson case, `m > ℓ`, `G` primitive, `t ≥ 2`, symmetry defect `< 1/2` |
| lines 4c, 4d | Johnson case, `m > ℓ`, `G` primitive, `t ≥ 2`, symmetry defect `≥ 1/2` |
| lines 5, 6, 6a, 7a | `G` imprimitive, AggregateCertificates returns a `k`-ary structure |
| lines 5, 7, 7a | `G` imprimitive, AggregateCertificates returns a colored equipartition |

`Babai.Sec15Inputs` is that table: the five tests of the pseudo-code as predicates on the
instance, the seven branches as reductions, and, for each branch, the three facts the
analysis of Sec. 15 uses — the branch is correct, it makes progress, it makes few calls —
each of them under exactly the tests that lead to the branch.
`Babai.masterStepFun` is the decision tree above, and `Babai.masterStep_of_procedure` turns
it into a `Babai.MasterStep`, so that `Babai.Theorem_1_1_1_math_of_sec15Inputs` is Theorem
1.1.1 for it.

**What a `Sec15Inputs` may not be.**  Each branch is a field, so it can in principle be
filled with the leaf `.done I.answer`, which is correct, makes no calls and therefore
satisfies every field.  A `Sec15Inputs` built that way says nothing.  The fields are
obligations to be discharged by the **named** reductions of Secs. 11–14
(`Babai.topAction4Reduction` for line 4b, `Babai.alignChainReduction` for lines 4d and 7a,
`Babai.versionsReduction` composed with `Babai.alignBranch` for lines 4c and 6a), which is
what `Workspace/Master/Lines.lean` does line by line; see the "Mismatches" section of
`Workspace/Master/DESIGN.md` for what is still missing and the Sec. 15 entry of
the corrected paper the accounting rule.
-/

universe u v w

namespace Babai

variable {Ω : Type u} {A : Type v} {ι : Type w}

/-- §15: the seven lines of Procedure String-Isomorphism.

The five `Is…` fields are the tests of the pseudo-code, the seven `line…` fields are the
branches, and the remaining fields are, for each branch, the three facts
`Babai.MasterStep` asks for, stated under the tests that lead to that branch.

Everything is read on a type `ι` of **hinted** instances (`Babai.MasterStep`): the tests of
lines 1–4 look at the Johnson structure the instance carries, and each branch says with
`lift` what structure it hands to each of its calls. -/
structure Sec15Inputs (Ω : Type u) (A : Type v) (ι : Type w) where
  /-- The String Isomorphism instance underneath a hinted instance. -/
  inst : ι → SIInstance Ω A
  /-- What a round attaches to each of its calls (line 11 of Procedure Align). -/
  lift : ι → SIInstance Ω A → ι
  /-- The instance with no hint, which is what Theorem 1.1.1 starts from. -/
  top : SIInstance Ω A → ι
  /-- Attaching a hint does not change the instance. -/
  lift_inst : ∀ (i : ι) (J : SIInstance Ω A), inst (lift i J) = J
  /-- The top instance is the instance it is built from. -/
  inst_top : ∀ I : SIInstance Ω A, inst (top I) = I
  /-- Line 2: the Johnson parameter `m = |Γ|` of the instance. -/
  param : ι → ℕ
  /-- Line 2: *"set `ℓ = (log n)³`"*, as a function of the window size `n`. -/
  ell : ℕ → ℕ
  /-- The number of instances one round produces, as a function of the window size. -/
  roundCost : ℕ → ℕ
  /-- Line 1 has been carried out: the instance is in the Johnson case (Def. 11.4.1), i.e.
  the group is transitive on the window and acts on a system of imprimitivity as a Johnson
  group.  Line 1 is taken exactly when this fails. -/
  IsJohnson : ι → Prop
  /-- Line 4: *"if `G` primitive (: i.e. `Ω = Φ` :)"* — the standard blocks are singletons,
  so the window is the set of standard blocks. -/
  IsPrimitiveCase : ι → Prop
  /-- Line 4a: *"if `t = 1`"*, `t` being the parameter of the standard blocks
  `Φ = {B_T | T ∈ Γ^{(t)}}` of line 3. -/
  TIsOne : ι → Prop
  /-- Line 4b: *"if relative symmetry defect of `H(x)` is `< 1/2`"*. -/
  SmallDefect : ι → Prop
  /-- Line 6: *"if AggregateCertificates returns canonically embedded `k`-ary relational
  structure on `Γ` with relative symmetry defect `≥ 1/2`"*. -/
  AggregatesToStructure : ι → Prop
  /-- Line 1: Procedure Reduce-to-Johnson (Luks reductions, §11.3). -/
  line1 : ι → SIReduction Ω A (Set (Equiv.Perm Ω))
  /-- Line 2: the imprimitive Luks reduction to the kernel of the `G`-action on the blocks,
  at multiplicative cost `ℓ!`. -/
  line2 : ι → SIReduction Ω A (Set (Equiv.Perm Ω))
  /-- Line 4a: the trivial case `t = 1`, where `Iso_G(x,y)` depends only on the multiplicity
  of each letter. -/
  line4a : ι → SIReduction Ω A (Set (Equiv.Perm Ω))
  /-- Line 4b: Cor. 12.0.10. -/
  line4b : ι → SIReduction Ω A (Set (Equiv.Perm Ω))
  /-- Lines 4c and 4d: the Extended Design Lemma (Thm. 9.2.3) followed by Procedure Align. -/
  line4cd : ι → SIReduction Ω A (Set (Equiv.Perm Ω))
  /-- Lines 5, 6, 6a and 7a: AggregateCertificates (Thm. 13.2.1) returning a `k`-ary
  relational structure, the Extended Design Lemma on it, then Procedure Align. -/
  line56a7a : ι → SIReduction Ω A (Set (Equiv.Perm Ω))
  /-- Lines 5, 7 and 7a: AggregateCertificates returning a colored equipartition, then
  Procedure Align. -/
  line567a : ι → SIReduction Ω A (Set (Equiv.Perm Ω))
  /-- Line 3: `Γ` labels a system of imprimitivity of the window, so `m ≤ n` in the
  Johnson case.  Outside the Johnson case the instance is given the value `2n`; see
  `Babai.MasterStep.param_le`. -/
  param_le : ∀ i : ι, param i ≤ 2 * (inst i).windowSize
  /-- Line 1 is correct. -/
  line1_run : ∀ i : ι, IsGroupInstance (inst i) → ¬ IsJohnson i →
      (line1 i).run = (inst i).answer
  /-- Line 1 makes progress. -/
  line1_decreases : ∀ i : ι, IsGroupInstance (inst i) → ¬ IsJohnson i →
      (∀ J ∈ (line1 i).calls,
        MakesProgress (fun j => (inst j).windowSize) param i (lift i J)) ∨
        IsChainRuleRound (fun j => (inst j).windowSize) param i
          ((line1 i).calls.map (lift i))
  /-- Line 1 makes at most `roundCost n` calls. -/
  line1_calls : ∀ i : ι, IsGroupInstance (inst i) → ¬ IsJohnson i →
      ((line1 i).calls).length ≤ roundCost (inst i).windowSize
  /-- Line 2 is correct. -/
  line2_run : ∀ i : ι, IsGroupInstance (inst i) → IsJohnson i →
      param i ≤ ell (inst i).windowSize → (line2 i).run = (inst i).answer
  /-- Line 2 makes progress: the kernel of the action on the blocks fixes every block, so
  its orbits lie inside blocks. -/
  line2_decreases : ∀ i : ι, IsGroupInstance (inst i) → IsJohnson i →
      param i ≤ ell (inst i).windowSize → ∀ J ∈ (line2 i).calls,
      MakesProgress (fun j => (inst j).windowSize) param i (lift i J)
  /-- Line 2 makes at most `roundCost n` calls (the multiplicative cost `ℓ!`). -/
  line2_calls : ∀ i : ι, IsGroupInstance (inst i) → IsJohnson i →
      param i ≤ ell (inst i).windowSize →
      ((line2 i).calls).length ≤ roundCost (inst i).windowSize
  /-- Line 4a is correct. -/
  line4a_run : ∀ i : ι, IsGroupInstance (inst i) → IsJohnson i →
      ¬ param i ≤ ell (inst i).windowSize → IsPrimitiveCase i → TIsOne i →
      (line4a i).run = (inst i).answer
  /-- Line 4a makes no calls: it *"finds `Iso_G(x,y)`"* and exits. -/
  line4a_calls : ∀ i : ι, IsGroupInstance (inst i) → IsJohnson i →
      ¬ param i ≤ ell (inst i).windowSize → IsPrimitiveCase i → TIsOne i →
      (line4a i).calls = []
  /-- Line 4b is correct. -/
  line4b_run : ∀ i : ι, IsGroupInstance (inst i) → IsJohnson i →
      ¬ param i ≤ ell (inst i).windowSize → IsPrimitiveCase i → ¬ TIsOne i →
      SmallDefect i → (line4b i).run = (inst i).answer
  /-- Line 4b makes progress. -/
  line4b_decreases : ∀ i : ι, IsGroupInstance (inst i) → IsJohnson i →
      ¬ param i ≤ ell (inst i).windowSize → IsPrimitiveCase i → ¬ TIsOne i →
      SmallDefect i → ∀ J ∈ (line4b i).calls,
      MakesProgress (fun j => (inst j).windowSize) param i (lift i J)
  /-- Line 4b makes at most `roundCost n` calls. -/
  line4b_calls : ∀ i : ι, IsGroupInstance (inst i) → IsJohnson i →
      ¬ param i ≤ ell (inst i).windowSize → IsPrimitiveCase i → ¬ TIsOne i →
      SmallDefect i → ((line4b i).calls).length ≤ roundCost (inst i).windowSize
  /-- Lines 4c and 4d are correct. -/
  line4cd_run : ∀ i : ι, IsGroupInstance (inst i) → IsJohnson i →
      ¬ param i ≤ ell (inst i).windowSize → IsPrimitiveCase i → ¬ TIsOne i →
      ¬ SmallDefect i → (line4cd i).run = (inst i).answer
  /-- Lines 4c and 4d make progress. -/
  line4cd_decreases : ∀ i : ι, IsGroupInstance (inst i) → IsJohnson i →
      ¬ param i ≤ ell (inst i).windowSize → IsPrimitiveCase i → ¬ TIsOne i →
      ¬ SmallDefect i → ∀ J ∈ (line4cd i).calls,
      MakesProgress (fun j => (inst j).windowSize) param i (lift i J)
  /-- Lines 4c and 4d make at most `roundCost n` calls (the multiplicative cost `q(m)`). -/
  line4cd_calls : ∀ i : ι, IsGroupInstance (inst i) → IsJohnson i →
      ¬ param i ≤ ell (inst i).windowSize → IsPrimitiveCase i → ¬ TIsOne i →
      ¬ SmallDefect i → ((line4cd i).calls).length ≤ roundCost (inst i).windowSize
  /-- Lines 5, 6, 6a and 7a are correct. -/
  line56a7a_run : ∀ i : ι, IsGroupInstance (inst i) → IsJohnson i →
      ¬ param i ≤ ell (inst i).windowSize → ¬ IsPrimitiveCase i →
      AggregatesToStructure i → (line56a7a i).run = (inst i).answer
  /-- Lines 5, 6, 6a and 7a make progress. -/
  line56a7a_decreases : ∀ i : ι, IsGroupInstance (inst i) → IsJohnson i →
      ¬ param i ≤ ell (inst i).windowSize → ¬ IsPrimitiveCase i →
      AggregatesToStructure i → ∀ J ∈ (line56a7a i).calls,
      MakesProgress (fun j => (inst j).windowSize) param i (lift i J)
  /-- Lines 5, 6, 6a and 7a make at most `roundCost n` calls. -/
  line56a7a_calls : ∀ i : ι, IsGroupInstance (inst i) → IsJohnson i →
      ¬ param i ≤ ell (inst i).windowSize → ¬ IsPrimitiveCase i →
      AggregatesToStructure i →
      ((line56a7a i).calls).length ≤ roundCost (inst i).windowSize
  /-- Lines 5, 7 and 7a are correct. -/
  line567a_run : ∀ i : ι, IsGroupInstance (inst i) → IsJohnson i →
      ¬ param i ≤ ell (inst i).windowSize → ¬ IsPrimitiveCase i →
      ¬ AggregatesToStructure i → (line567a i).run = (inst i).answer
  /-- Lines 5, 7 and 7a make progress. -/
  line567a_decreases : ∀ i : ι, IsGroupInstance (inst i) → IsJohnson i →
      ¬ param i ≤ ell (inst i).windowSize → ¬ IsPrimitiveCase i →
      ¬ AggregatesToStructure i → ∀ J ∈ (line567a i).calls,
      MakesProgress (fun j => (inst j).windowSize) param i (lift i J)
  /-- Lines 5, 7 and 7a make at most `roundCost n` calls. -/
  line567a_calls : ∀ i : ι, IsGroupInstance (inst i) → IsJohnson i →
      ¬ param i ≤ ell (inst i).windowSize → ¬ IsPrimitiveCase i →
      ¬ AggregatesToStructure i →
      ((line567a i).calls).length ≤ roundCost (inst i).windowSize
  /-- Line 1 produces group instances (`Babai.IsGroupInstance`).  Line 4a needs no such
  field, because it makes no calls. -/
  line1_group : ∀ i : ι, IsGroupInstance (inst i) → ¬ IsJohnson i →
      ∀ J ∈ (line1 i).calls, IsGroupInstance J
  /-- Line 2 produces group instances. -/
  line2_group : ∀ i : ι, IsGroupInstance (inst i) → IsJohnson i →
      param i ≤ ell (inst i).windowSize → ∀ J ∈ (line2 i).calls, IsGroupInstance J
  /-- Line 4b produces group instances. -/
  line4b_group : ∀ i : ι, IsGroupInstance (inst i) → IsJohnson i →
      ¬ param i ≤ ell (inst i).windowSize → IsPrimitiveCase i → ¬ TIsOne i →
      SmallDefect i → ∀ J ∈ (line4b i).calls, IsGroupInstance J
  /-- Lines 4c and 4d produce group instances. -/
  line4cd_group : ∀ i : ι, IsGroupInstance (inst i) → IsJohnson i →
      ¬ param i ≤ ell (inst i).windowSize → IsPrimitiveCase i → ¬ TIsOne i →
      ¬ SmallDefect i → ∀ J ∈ (line4cd i).calls, IsGroupInstance J
  /-- Lines 5, 6, 6a and 7a produce group instances. -/
  line56a7a_group : ∀ i : ι, IsGroupInstance (inst i) → IsJohnson i →
      ¬ param i ≤ ell (inst i).windowSize → ¬ IsPrimitiveCase i →
      AggregatesToStructure i → ∀ J ∈ (line56a7a i).calls, IsGroupInstance J
  /-- Lines 5, 7 and 7a produce group instances. -/
  line567a_group : ∀ i : ι, IsGroupInstance (inst i) → IsJohnson i →
      ¬ param i ≤ ell (inst i).windowSize → ¬ IsPrimitiveCase i →
      ¬ AggregatesToStructure i → ∀ J ∈ (line567a i).calls, IsGroupInstance J

namespace Sec15Inputs

variable (D : Sec15Inputs Ω A ι)

open scoped Classical in
/-- §15, **one round of Procedure String-Isomorphism**: the decision tree of lines 1–7a.

Line 1 first; then line 2's test `m ≤ ℓ`; then line 4's test *"`G` primitive"*, which sends
the run either to lines 4a–4d or to lines 5–7a. -/
noncomputable def step (i : ι) : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  if ¬ D.IsJohnson i then D.line1 i
  else if D.param i ≤ D.ell (D.inst i).windowSize then D.line2 i
  else if D.IsPrimitiveCase i then
    if D.TIsOne i then D.line4a i
    else if D.SmallDefect i then D.line4b i
    else D.line4cd i
  else
    if D.AggregatesToStructure i then D.line56a7a i else D.line567a i

open scoped Classical in
/-- The seven branches of `Babai.Sec15Inputs.step`, each with the tests that lead to it.
Every proof about a round is this case analysis followed by the corresponding fields. -/
theorem step_cases (i : ι) :
    (¬ D.IsJohnson i ∧ D.step i = D.line1 i) ∨
    (D.IsJohnson i ∧ D.param i ≤ D.ell (D.inst i).windowSize ∧ D.step i = D.line2 i) ∨
    (D.IsJohnson i ∧ ¬ D.param i ≤ D.ell (D.inst i).windowSize ∧ D.IsPrimitiveCase i ∧
      D.TIsOne i ∧ D.step i = D.line4a i) ∨
    (D.IsJohnson i ∧ ¬ D.param i ≤ D.ell (D.inst i).windowSize ∧ D.IsPrimitiveCase i ∧
      ¬ D.TIsOne i ∧ D.SmallDefect i ∧ D.step i = D.line4b i) ∨
    (D.IsJohnson i ∧ ¬ D.param i ≤ D.ell (D.inst i).windowSize ∧ D.IsPrimitiveCase i ∧
      ¬ D.TIsOne i ∧ ¬ D.SmallDefect i ∧ D.step i = D.line4cd i) ∨
    (D.IsJohnson i ∧ ¬ D.param i ≤ D.ell (D.inst i).windowSize ∧ ¬ D.IsPrimitiveCase i ∧
      D.AggregatesToStructure i ∧ D.step i = D.line56a7a i) ∨
    (D.IsJohnson i ∧ ¬ D.param i ≤ D.ell (D.inst i).windowSize ∧ ¬ D.IsPrimitiveCase i ∧
      ¬ D.AggregatesToStructure i ∧ D.step i = D.line567a i) := by
  classical
  by_cases hJ : D.IsJohnson i
  · by_cases hℓ : D.param i ≤ D.ell (D.inst i).windowSize
    · exact Or.inr (Or.inl ⟨hJ, hℓ, by rw [step, if_neg (not_not.2 hJ), if_pos hℓ]⟩)
    · by_cases hp : D.IsPrimitiveCase i
      · by_cases ht : D.TIsOne i
        · exact Or.inr (Or.inr (Or.inl ⟨hJ, hℓ, hp, ht, by
            rw [step, if_neg (not_not.2 hJ), if_neg hℓ, if_pos hp, if_pos ht]⟩))
        · by_cases hd : D.SmallDefect i
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hJ, hℓ, hp, ht, hd, by
              rw [step, if_neg (not_not.2 hJ), if_neg hℓ, if_pos hp, if_neg ht,
                if_pos hd]⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hJ, hℓ, hp, ht, hd, by
              rw [step, if_neg (not_not.2 hJ), if_neg hℓ, if_pos hp, if_neg ht,
                if_neg hd]⟩))))
      · by_cases ha : D.AggregatesToStructure i
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hJ, hℓ, hp, ha, by
            rw [step, if_neg (not_not.2 hJ), if_neg hℓ, if_neg hp, if_pos ha]⟩)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hJ, hℓ, hp, ha, by
            rw [step, if_neg (not_not.2 hJ), if_neg hℓ, if_neg hp, if_neg ha]⟩)))))
  · exact Or.inl ⟨hJ, by rw [step, if_pos hJ]⟩

end Sec15Inputs

/-- §15, **Procedure String-Isomorphism** as one round of the Master Algorithm: the decision
tree of lines 1–7a, with the three properties its analysis uses.

Each property is proved by the case analysis `Babai.Sec15Inputs.step_cases` over the seven
branches, followed by the field of `Sec15Inputs` belonging to the branch.  Line 4a needs no
progress field, because it makes no calls. -/
noncomputable def masterStep_of_procedure (D : Sec15Inputs Ω A ι) : MasterStep Ω A ι where
  inst := D.inst
  step := D.step
  lift := D.lift
  top := D.top
  inst_top := D.inst_top
  lift_inst := fun i J _ => D.lift_inst i J
  param := D.param
  roundCost := D.roundCost
  param_le := D.param_le
  calls_isGroupInstance := by
    intro i hg
    rcases D.step_cases i with
      ⟨h1, hs⟩ | ⟨h1, h2, hs⟩ | ⟨h1, h2, h3, h4, hs⟩ | ⟨h1, h2, h3, h4, h5, hs⟩ |
      ⟨h1, h2, h3, h4, h5, hs⟩ | ⟨h1, h2, h3, h4, hs⟩ | ⟨h1, h2, h3, h4, hs⟩ <;> rw [hs]
    · exact D.line1_group i hg h1
    · exact D.line2_group i hg h1 h2
    · rw [D.line4a_calls i hg h1 h2 h3 h4]; simp
    · exact D.line4b_group i hg h1 h2 h3 h4 h5
    · exact D.line4cd_group i hg h1 h2 h3 h4 h5
    · exact D.line56a7a_group i hg h1 h2 h3 h4
    · exact D.line567a_group i hg h1 h2 h3 h4
  round_correct := by
    intro i hg
    rcases D.step_cases i with
      ⟨h1, hs⟩ | ⟨h1, h2, hs⟩ | ⟨h1, h2, h3, h4, hs⟩ | ⟨h1, h2, h3, h4, h5, hs⟩ |
      ⟨h1, h2, h3, h4, h5, hs⟩ | ⟨h1, h2, h3, h4, hs⟩ | ⟨h1, h2, h3, h4, hs⟩ <;> rw [hs]
    · exact D.line1_run i hg h1
    · exact D.line2_run i hg h1 h2
    · exact D.line4a_run i hg h1 h2 h3 h4
    · exact D.line4b_run i hg h1 h2 h3 h4 h5
    · exact D.line4cd_run i hg h1 h2 h3 h4 h5
    · exact D.line56a7a_run i hg h1 h2 h3 h4
    · exact D.line567a_run i hg h1 h2 h3 h4
  decreases := by
    intro i hg
    rcases D.step_cases i with
      ⟨h1, hs⟩ | ⟨h1, h2, hs⟩ | ⟨h1, h2, h3, h4, hs⟩ | ⟨h1, h2, h3, h4, h5, hs⟩ |
      ⟨h1, h2, h3, h4, h5, hs⟩ | ⟨h1, h2, h3, h4, hs⟩ | ⟨h1, h2, h3, h4, hs⟩ <;> rw [hs]
    · exact D.line1_decreases i hg h1
    · exact Or.inl (D.line2_decreases i hg h1 h2)
    · exact Or.inl (by rw [D.line4a_calls i hg h1 h2 h3 h4]; simp)
    · exact Or.inl (D.line4b_decreases i hg h1 h2 h3 h4 h5)
    · exact Or.inl (D.line4cd_decreases i hg h1 h2 h3 h4 h5)
    · exact Or.inl (D.line56a7a_decreases i hg h1 h2 h3 h4)
    · exact Or.inl (D.line567a_decreases i hg h1 h2 h3 h4)
  calls_length_le := by
    intro i hg
    rcases D.step_cases i with
      ⟨h1, hs⟩ | ⟨h1, h2, hs⟩ | ⟨h1, h2, h3, h4, hs⟩ | ⟨h1, h2, h3, h4, h5, hs⟩ |
      ⟨h1, h2, h3, h4, h5, hs⟩ | ⟨h1, h2, h3, h4, hs⟩ | ⟨h1, h2, h3, h4, hs⟩ <;> rw [hs]
    · exact D.line1_calls i hg h1
    · exact D.line2_calls i hg h1 h2
    · rw [D.line4a_calls i hg h1 h2 h3 h4]; simp
    · exact D.line4b_calls i hg h1 h2 h3 h4 h5
    · exact D.line4cd_calls i hg h1 h2 h3 h4 h5
    · exact D.line56a7a_calls i hg h1 h2 h3 h4
    · exact D.line567a_calls i hg h1 h2 h3 h4

/-- **Theorem 1.1.1** (Sec. 1.1), the mathematical half, for the Master Algorithm of
Sec. 15 assembled from its seven lines.

Procedure String-Isomorphism, run with the seven lines of `D`, returns `Iso_G(x,y)` and
generates at most `exp(30 (log₂ n + 2)^{c₁+2})` String Isomorphism instances, where
`q(n) ≤ exp((log₂ n + 2)^{c₁})` is the multiplicative cost of one round.  This is
`Babai.Theorem_1_1_1_math_of_masterStep` applied to
`Babai.masterStep_of_procedure`; what it adds is that the round is the decision tree of
lines 1–7a and not an arbitrary one.

The running time is not covered; see the Sec. 15 entry of the corrected paper. -/
theorem Theorem_1_1_1_math_of_sec15Inputs (D : Sec15Inputs Ω A ι)
    (hmono : Monotone D.roundCost) (c₁ : ℕ)
    (hq : ∀ n : ℕ, D.roundCost n ≤ 2 ^ ((Nat.log 2 n + 2) ^ c₁))
    (G : Subgroup (Equiv.Perm Ω)) (x y : Ω → A) :
    let M := masterStep_of_procedure D
    let I : SIInstance Ω A := ⟨(G : Set (Equiv.Perm Ω)), Set.univ, x, y⟩
    let i := M.top I
    let f := M.rank i + 1
    M.solve f i = strIso (G : Set (Equiv.Perm Ω)) x y ∧
      M.count f i ≤ 2 ^ (30 * (Nat.log 2 I.windowSize + 2) ^ (c₁ + 2)) :=
  Theorem_1_1_1_math_of_masterStep (masterStep_of_procedure D) hmono c₁ hq G x y

end Babai
