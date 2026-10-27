/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Luks's Descent (§11.1, Prop. 11.1.6) as a computable round.
-/
import Workspace.Algo.CosetUnion
import Workspace.Algo.ChainTransversal

/-!
# The Descent round (§11.1, Proposition 11.1.6)

> Let `H ≤ G`.  Then finding `Iso^Δ_G(x,y)` reduces to `|G : H|` instances of finding
> `Iso^Δ_H(x, y^σ)` for various `σ ∈ G`.
>
> *Proof.*  We can write `G = ⋃_σ Hσ` where `σ` ranges over a set of right coset
> representatives of `H` in `G`.  Applying Eq. (61) to this decomposition, we obtain
> `Iso^Δ_G(x,y) = ⋃_σ Iso^Δ_{Hσ}(x,y) = ⋃_σ Iso^Δ_H(x, y^{σ⁻¹})σ`.  (62)

This file writes Eq. (62) as an `Algo.Round`.

## The first form of Eq. (62), not the second

The round stops at the **middle** term of Eq. (62): the `σ`-th child is the instance whose
candidate set is the coset `Hσ` itself, and the strings are not shifted.  The reason is the
one given in the header of `Workspace/Algo/Luks.lean`: `Algo.Implements` asks the raw round to
walk the same tree for *every* raw answer that decodes to the true answer of a child, so a
child instance must be a function of the coset and not of a chosen representative.  The
answers then need no translation either, and the fold is the plain union of Eq. (61).

`Algo.RawWinSI` already stores a candidate set as a coset — generators and a representative —
so the `j`-th child is that instance with the generators of `H` and the representative `σ_j`.

## Which subgroup `H`, and why that matters

The only subgroups the paper ever descends to are **kernels of actions** (Prop. 2.2.6 (a));
Theorem 11.1.9 descends to `N = ker(G → S(ℬ))`.  A descent instance therefore carries not a
generating list of `H` but the list `Δ_H` of points whose pointwise stabilizer in `G` is `H`,
and the round computes the generators of `H` itself (`Algo.descKer`, from
`Algo.rawKerGens`).  Two things come with that:

* `H ≤ G` is a *theorem* (`Algo.descKer_le`), not a clause of the well-formedness predicate;
* the coset representatives are read off the stabilizer chain of `G` with `Δ_H` moved to the
  front of the base (`Workspace/Algo/ChainTransversal.lean`), so the `j`-th representative is
  a product of at most `|Δ_H|` table entries, computable in time polynomial in the number of
  **bits** of `j`.

## The index in binary, and the side of the cosets

Because of the second point the index `|G : H|` travels as a machine **natural**
(`Algo.winCosetIndex`), not in unary as an earlier version of this file had it.  A descent
instance is then polynomially small in the domain size alone, and
`Algo.descentRound.ground` is the size of the two strings, exactly as for the Chain Rule
round of `Workspace/Algo/Luks.lean`.  `Enc.size` of a natural is its bit length plus two
(`RAM.Small.size_nat`), and `|G : H| ≤ n^n` (`Algo.size_winCosetIndex_le`), so this is
honest.

The chain transversal produces **left** cosets `σ • H` (`Algo.cover_winCosetRep`), which is
the side `Babai.descent_of_cover` asks for, so the round does not invert anything.

## Main definitions

* `Algo.RawDescSI`, `Algo.decDescSI`, `Algo.DescWF` — raw descent instances, their decoding
  and their well-formedness;
* `Algo.descKer` — generators of the subgroup descended to (Prop. 2.2.6 (a));
* `Algo.descPerms` — the representatives `σ_j` of Eq. (62), decoded;
* `Algo.descentChain` — the mathematical round: Eq. (62) folded with `Algo.cosetHull`;
* `Algo.descChild`, `Algo.descentRound` — the computable round;
* `Algo.descentCost` — its cost data.

## Main results

* `Algo.run_descentChain` — **Eq. (62)**: the fold computes `Iso^Δ_G(x,y)`;
* `Algo.implements_descentRound` — **the link**: the raw round walks that tree;
* `Algo.cover_descPerms` — **Prop. 2.2.6 (a)** for this action: the candidate set is the
  union of the `|G : H|` left cosets `σ_j·H`;
* `Algo.run_descentRoundReduction` — the tree computes the answer of the instance, so
  `Algo.roundValue_eq` applies.

No axiom and no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)
open scoped Pointwise

variable {n : ℕ}

/-! ## The mathematical round: Eq. (62) folded

The answers of the children are unioned.  A machine holds an answer as a coset
(Definition 11.1.2), and the union of two cosets is not a coset, so the fold keeps the
smallest coset containing what it has seen (`Algo.cosetHull`).  At the end of the fold nothing
has been lost: the union of *all* the children's answers is `Iso^Δ_G(x,y)`, which is itself
empty or a coset (Observation 11.1.11), so its hull is itself. -/

/-- **Proposition 11.1.6 (Descent) as a reduction**, in the first form of Eq. (62): the `σ`-th
call is the instance with candidate set `σ·H`, and the answers are folded into the smallest
coset containing them. -/
noncomputable def descentChain {Ω A : Type*} (H : Set (Perm Ω)) (Δ : Set Ω) (x y : Ω → A) :
    Set (Perm Ω) → List (Perm Ω) → Babai.SIReduction Ω A (Set (Perm Ω))
  | acc, [] => .done acc
  | acc, σ :: rest =>
      .call ⟨σ • H, Δ, x, y⟩ fun ans => descentChain H Δ x y (cosetHull (acc ∪ ans)) rest

section Hull

variable {Γ : Type*} [Group Γ]

/-- The hull of a nonempty set is a coset. -/
theorem exists_cosetHull_eq {S : Set Γ} {τ : Γ} (hτ : τ ∈ S) :
    ∃ A : Subgroup Γ, cosetHull S = τ • (A : Set Γ) :=
  ⟨Subgroup.closure (τ⁻¹ • S), cosetHull_eq hτ⟩

theorem cosetHull_mono {S T : Set Γ} (h : S ⊆ T) : cosetHull S ⊆ cosetHull T := by
  rcases Set.eq_empty_or_nonempty T with rfl | ⟨τ, hτ⟩
  · rw [Set.subset_empty_iff.1 h, cosetHull_empty]
  obtain ⟨A, hA⟩ := exists_cosetHull_eq hτ
  rw [hA]
  exact cosetHull_subset_of_subset (le_trans h (le_trans (subset_cosetHull T) (le_of_eq hA)))

@[simp] theorem cosetHull_idem (S : Set Γ) : cosetHull (cosetHull S) = cosetHull S := by
  rcases Set.eq_empty_or_nonempty S with rfl | ⟨τ, hτ⟩
  · simp
  obtain ⟨A, hA⟩ := exists_cosetHull_eq hτ
  rw [hA, cosetHull_smul_subgroup]

/-- Folding with the hull is the hull of the union: what the fold of `Algo.descentChain`
keeps is the smallest coset containing the answers it has seen. -/
theorem cosetHull_hull_union (S T : Set Γ) :
    cosetHull (cosetHull S ∪ T) = cosetHull (S ∪ T) := by
  refine le_antisymm ?_ ?_
  · refine le_trans (cosetHull_mono (Set.union_subset ?_ ?_)) (le_of_eq (cosetHull_idem _))
    · exact cosetHull_mono Set.subset_union_left
    · exact le_trans Set.subset_union_right (subset_cosetHull _)
  · exact cosetHull_mono (Set.union_subset_union_left _ (subset_cosetHull S))

end Hull

/-- The value of the fold of `Algo.descentChain`. -/
theorem run_descentChain_fold {Ω A : Type*} (H : Set (Perm Ω)) (Δ : Set Ω) (x y : Ω → A) :
    ∀ (L : List (Perm Ω)) (acc : Set (Perm Ω)), cosetHull acc = acc →
      (descentChain H Δ x y acc L).run
        = cosetHull (acc ∪ ⋃ σ ∈ L, Babai.wIso Δ (σ • H) x y) := by
  intro L
  induction L with
  | nil =>
      intro acc hacc
      rw [descentChain, Babai.SIReduction.run_done]
      simp only [List.not_mem_nil, Set.iUnion_of_empty, Set.iUnion_empty, Set.union_empty]
      exact hacc.symm
  | cons σ rest ih =>
      intro acc hacc
      rw [descentChain, Babai.SIReduction.run_call]
      have hans : (⟨σ • H, Δ, x, y⟩ : Babai.SIInstance Ω A).answer
          = Babai.wIso Δ (σ • H) x y := rfl
      rw [hans, ih _ (cosetHull_idem _)]
      have hunion : (⋃ ρ ∈ (σ :: rest), Babai.wIso Δ (ρ • H) x y)
          = Babai.wIso Δ (σ • H) x y ∪ ⋃ ρ ∈ rest, Babai.wIso Δ (ρ • H) x y := by
        ext u
        simp only [Set.mem_iUnion, List.mem_cons, exists_prop, Set.mem_union]
        constructor
        · rintro ⟨ρ, (rfl | hρ), hu⟩
          · exact Or.inl hu
          · exact Or.inr ⟨ρ, hρ, hu⟩
        · rintro (hu | ⟨ρ, hρ, hu⟩)
          · exact ⟨σ, Or.inl rfl, hu⟩
          · exact ⟨ρ, Or.inr hρ, hu⟩
      rw [hunion, cosetHull_hull_union, Set.union_assoc]

/-- **Proposition 11.1.6, Eq. (62)**: the descent chain computes `Iso^Δ_C(x,y)`, provided the
list of representatives covers the candidate set `C` by cosets of `H` and the answer of the
instance is empty or a coset (Observation 11.1.11).

*Proof.*  Eq. (61) turns `Iso^Δ_C(x,y)` into the union of the children's answers
(`Babai.wIso_iUnion`), the fold keeps the smallest coset containing that union
(`Algo.run_descentChain_fold`), and a coset is its own hull. -/
theorem run_descentChain {Ω A : Type*} (H : Set (Perm Ω)) (Δ : Set Ω) (x y : Ω → A)
    (C : Set (Perm Ω)) (L : List (Perm Ω))
    (hcover : C = ⋃ σ ∈ L, σ • H)
    (hcoset : ∀ τ ∈ Babai.wIso Δ C x y,
      ∃ B : Subgroup (Perm Ω), Babai.wIso Δ C x y = τ • (B : Set (Perm Ω))) :
    (descentChain H Δ x y ∅ L).run = Babai.wIso Δ C x y := by
  have hsplit : Babai.wIso Δ C x y = ⋃ σ ∈ L, Babai.wIso Δ (σ • H) x y := by
    rw [hcover, Babai.wIso_iUnion]
    exact Set.iUnion_congr fun σ => Babai.wIso_iUnion _ _ _ _
  rw [run_descentChain_fold H Δ x y L ∅ cosetHull_empty, Set.empty_union, ← hsplit]
  rcases Set.eq_empty_or_nonempty (Babai.wIso Δ C x y) with h | ⟨τ, hτ⟩
  · rw [h, cosetHull_empty]
  · obtain ⟨B, hB⟩ := hcoset τ hτ
    rw [hB, cosetHull_smul_subgroup]

/-! ## Raw descent instances

The subgroup descended to is the **kernel of an action** (Prop. 2.2.6 (a)), the only kind of
subgroup the paper descends to: Theorem 11.1.9 descends to `N = ker(G → S(ℬ))`.  Here the
action is the restriction to a list of points `Δ_H`, whose kernel is the pointwise stabilizer
`G_{(Δ_H)}` (`Algo.mem_ker_winRestrictHom`).  So an instance carries `Δ_H` and the number of
cosets, not a generating list of `H` and a unary index. -/

/-- A raw instance of the descent round: an instance with a window (`Algo.RawWinSI`) together
with, when the round is to descend, the list `Δ_H` of points whose pointwise stabilizer in `G`
is the subgroup `H` descended to, and the index `|G : H|` **as a number**.  `none` marks an
instance the round hands on. -/
abbrev RawDescSI := RawWinSI × Option (List ℕ × ℕ)

/-- The instance a raw descent instance describes.  Paper: Definition 11.1.2. -/
noncomputable def decDescSI (n : ℕ) (I : RawDescSI) : Babai.SIInstance (Fin n) ℕ :=
  decWinSI n I.1

/-- The generators of the group of the instance, decoded. -/
noncomputable def descGens (n : ℕ) (W : RawWinSI) : List (Perm (Fin n)) := W.2.1.map (decPerm n)

theorem decGroup_eq_genGroup_descGens (n : ℕ) (W : RawWinSI) :
    decGroup n W.2.1 = genGroup (descGens n W) := rfl

/-- **Well-formed raw descent instances.**  Besides `Algo.WinWF`, the list `Δ_H` is a
repetition-free list of points of the domain, and the stored index is the number of cosets of
the kernel `G_{(Δ_H)}` in `G` that `Algo.winCosetIndex` computes. -/
def DescWF (n : ℕ) (I : RawDescSI) : Prop :=
  WinWF n I.1 ∧
    ∀ d idx, I.2 = some (d, idx) →
      d.Nodup ∧ (∀ x ∈ d, x < n) ∧
        idx = winCosetIndex n I.1.2.2.2.1 d (descGens n I.1)

/-- **Generators of the subgroup the round descends to**: the kernel of the action of `G` on
`Δ_H`, that is the pointwise stabilizer `G_{(Δ_H)}`.  Paper: Proposition 2.2.6 (a). -/
def descKer (W : RawWinSI) (d : List ℕ) : RawGens := rawKerGens ((W.2.2.2.1, W.2.1), d)

/-- The `j`-th representative of the child: the parent's representative times the `j`-th coset
representative of the kernel in `G`, read off the stabilizer chain
(`Algo.rawCosetRepBin`); the index `j` is a machine natural. -/
def descRep (W : RawWinSI) (q : List ℕ × ℕ) (j : ℕ) : RawPerm :=
  rawMul (W.2.2.1, rawCosetRepBin ((W.2.2.2.1, W.2.1), (q.1, j)))

/-- The child instances' representatives, decoded: the `σ_j` of Eq. (62). -/
noncomputable def descPerms (n : ℕ) (W : RawWinSI) (q : List ℕ × ℕ) : List (Perm (Fin n)) :=
  (List.range q.2).map (fun j => decPerm n (descRep W q j))

@[simp] theorem length_descPerms (n : ℕ) (W : RawWinSI) (q : List ℕ × ℕ) :
    (descPerms n W q).length = q.2 := by simp [descPerms]

theorem getElem_descPerms (n : ℕ) (W : RawWinSI) (q : List ℕ × ℕ) {j : ℕ}
    (hj : j < (descPerms n W q).length) :
    (descPerms n W q)[j] = decPerm n (descRep W q j) := by
  simp only [descPerms, List.getElem_map, List.getElem_range]

/-! ## The representatives are a transversal

Everything below is `Algo.cover_winCosetRep` — Proposition 2.2.6 (a) — with the raw generating
list of the instance read as an encoded list (`Algo.map_encPerm_decPerm`). -/

/-- Translating a covering union by an element on the left. -/
theorem smul_biUnion_index {Γ : Type*} [Group Γ] (σ₀ : Γ) (L : List ℕ) (f : ℕ → Γ)
    (H : Set Γ) :
    σ₀ • (⋃ j ∈ L, f j • H) = ⋃ σ ∈ L.map (fun j => σ₀ * f j), σ • H := by
  ext u
  have key : ∀ j : ℕ, ((σ₀ * f j)⁻¹ * u ∈ H) ↔ ((f j)⁻¹ * (σ₀⁻¹ * u) ∈ H) := by
    intro j
    rw [show (σ₀ * f j)⁻¹ * u = (f j)⁻¹ * (σ₀⁻¹ * u) by group]
  simp only [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_iUnion, exists_prop, List.mem_map,
    smul_eq_mul]
  constructor
  · rintro ⟨j, hj, hu⟩
    exact ⟨σ₀ * f j, ⟨j, hj, rfl⟩, (key j).2 hu⟩
  · rintro ⟨ρ, ⟨j, hj, rfl⟩, hu⟩
    exact ⟨j, hj, (key j).1 hu⟩

section Reps

variable {I : RawDescSI} {d : List ℕ} {idx : ℕ}

/-- The generator list of the instance is the encoding of its decoding. -/
theorem gens_eq (hI : DescWF n I) : I.1.2.1 = (descGens n I.1).map (encPerm n) :=
  (map_encPerm_decPerm hI.1.2.2.2.2.1).symm

/-- The kernel generators are well formed. -/
theorem wf_descKer (hI : DescWF n I) (hs : I.2 = some (d, idx)) :
    RawGens.WF n (descKer I.1 d) := by
  obtain ⟨hnd, hlt, -⟩ := hI.2 d idx hs
  have hx : I.1.2.2.2.1.length = n := hI.1.1
  show RawGens.WF n (rawKerGens ((I.1.2.2.2.1, I.1.2.1), d))
  rw [gens_eq hI]
  exact wf_rawKerGens hx hnd hlt _

/-- The kernel is given by at most `n²` generators. -/
theorem length_descKer_le (hI : DescWF n I) (hs : I.2 = some (d, idx)) :
    (descKer I.1 d).length ≤ n * n := by
  obtain ⟨hnd, hlt, -⟩ := hI.2 d idx hs
  have hx : I.1.2.2.2.1.length = n := hI.1.1
  show (rawKerGens ((I.1.2.2.2.1, I.1.2.1), d)).length ≤ n * n
  rw [gens_eq hI]
  exact length_rawKerGens_le hx hnd hlt _

/-- **The subgroup descended to is the kernel of the action on `Δ_H`.**  Paper:
Proposition 2.2.6 (a). -/
theorem decGroup_descKer (hI : DescWF n I) (hs : I.2 = some (d, idx)) :
    decGroup n (descKer I.1 d)
      = Babai.pointwiseStabilizer (genGroup (descGens n I.1)) {x : Fin n | (x : ℕ) ∈ d} := by
  obtain ⟨hnd, hlt, -⟩ := hI.2 d idx hs
  have hx : I.1.2.2.2.1.length = n := hI.1.1
  show decGroup n (rawKerGens ((I.1.2.2.2.1, I.1.2.1), d)) = _
  rw [gens_eq hI]
  exact decGroup_rawKerGens hx hnd hlt _

/-- The kernel lies in the group of the instance. -/
theorem descKer_le (hI : DescWF n I) (hs : I.2 = some (d, idx)) :
    decGroup n (descKer I.1 d) ≤ decGroup n I.1.2.1 := by
  rw [decGroup_descKer hI hs]
  intro a ha
  exact (Babai.mem_pointwiseStabilizer.1 ha).1

/-- The `j`-th representative of a child is well formed. -/
theorem wf_descRep (hI : DescWF n I) (hs : I.2 = some (d, idx)) (j : ℕ) :
    RawPerm.WF n (descRep I.1 (d, idx) j) := by
  obtain ⟨hnd, hlt, -⟩ := hI.2 d idx hs
  have hx : I.1.2.2.2.1.length = n := hI.1.1
  have hσ : RawPerm.WF n I.1.2.2.1 := hI.1.2.2.2.2.2.2.1
  show RawPerm.WF n (rawMul (I.1.2.2.1, rawCosetRepBin ((I.1.2.2.2.1, I.1.2.1), (d, j))))
  refine wf_rawMul hσ ?_
  rw [gens_eq hI]
  exact wf_rawCosetRepBin hx hnd hlt _ j

/-- The `j`-th representative, decoded. -/
theorem decPerm_descRep (hI : DescWF n I) (hs : I.2 = some (d, idx)) (j : ℕ) :
    decPerm n (descRep I.1 (d, idx) j)
      = decPerm n I.1.2.2.1 * winCosetRep n I.1.2.2.2.1 d (descGens n I.1) j := by
  obtain ⟨hnd, hlt, -⟩ := hI.2 d idx hs
  have hx : I.1.2.2.2.1.length = n := hI.1.1
  have hσ : RawPerm.WF n I.1.2.2.1 := hI.1.2.2.2.2.2.2.1
  show decPerm n (rawMul (I.1.2.2.1, rawCosetRepBin ((I.1.2.2.2.1, I.1.2.1), (d, j)))) = _
  rw [gens_eq hI, rawCosetRepBin_spec hx hnd hlt _ j, rawMul_of_wf hσ (wf_encPerm n _),
    decPerm_encPerm, decPerm_encPerm]

/-- **The cover Eq. (62) needs**: the candidate set of the instance is the union of the left
cosets `σ_j·H` of the kernel.  The representatives read off the stabilizer chain are on the
left already (`Algo.cover_winCosetRep`), so no inversion is needed. -/
theorem cover_descPerms (hI : DescWF n I) (hs : I.2 = some (d, idx)) :
    (decDescSI n I).K = ⋃ σ ∈ descPerms n I.1 (d, idx),
      σ • (decGroup n (descKer I.1 d) : Set (Perm (Fin n))) := by
  obtain ⟨hnd, hlt, hidx⟩ := hI.2 d idx hs
  have hx : I.1.2.2.2.1.length = n := hI.1.1
  have hK : (decDescSI n I).K
      = decPerm n I.1.2.2.1 • (decGroup n I.1.2.1 : Set (Perm (Fin n))) := by
    rw [decDescSI, decWinSI, decCoset_some]
  have hcov := cover_winCosetRep (n := n) hx hnd hlt (descGens n I.1)
  have hH : (decGroup n (descKer I.1 d) : Set (Perm (Fin n)))
      = (Babai.pointwiseStabilizer (genGroup (descGens n I.1)) {x : Fin n | (x : ℕ) ∈ d} :
          Set (Perm (Fin n))) := by
    rw [decGroup_descKer hI hs]
  have hlist : descPerms n I.1 (d, idx)
      = (List.range idx).map
          (fun j => decPerm n I.1.2.2.1 * winCosetRep n I.1.2.2.2.1 d (descGens n I.1) j) := by
    rw [descPerms]
    exact List.map_congr_left (fun j _ => decPerm_descRep hI hs j)
  rw [hK, hH, hlist, show (decGroup n I.1.2.1 : Set (Perm (Fin n)))
      = (genGroup (descGens n I.1) : Set (Perm (Fin n))) from rfl, hcov, ← hidx,
    smul_biUnion_index]

end Reps


/-! ## The computable round -/

/-- The `j`-th child of the descent round: the same window and strings, the generators of the
kernel `H = G_{(Δ_H)}` (Prop. 2.2.6 (a)), and the representative `σ_j` of Eq. (62).  The child
does not descend again. -/
def descChild (p : RawDescSI × ℕ × RawCoset) : Option RawDescSI :=
  p.1.2.elim none (fun q =>
    if q.2 ≤ p.2.1 then none
    else some ((p.1.1.1, descKer p.1.1 q.1, descRep p.1.1 q p.2.1,
      p.1.1.2.2.2.1, p.1.1.2.2.2.2), none))

/-- The fold step: the smallest coset containing the answers seen so far
(`Algo.rawCosetJoin`). -/
def descCombine (p : RawDescSI × ℕ × RawCoset × RawCoset) : RawCoset :=
  rawCosetJoin (p.1.1.2.2.2.1, p.2.2.1, p.2.2.2)

theorem descChild_eq_some {p : RawDescSI × ℕ × RawCoset} {J : RawDescSI}
    (hc : descChild p = some J) :
    ∃ q, p.1.2 = some q ∧ p.2.1 < q.2 ∧
      J = ((p.1.1.1, descKer p.1.1 q.1, descRep p.1.1 q p.2.1,
        p.1.1.2.2.2.1, p.1.1.2.2.2.2), none) := by
  rw [descChild] at hc
  rcases hq : p.1.2 with _ | q
  · rw [hq] at hc; exact absurd hc (by simp)
  · rw [hq] at hc
    simp only [Option.elim] at hc
    by_cases hj : q.2 ≤ p.2.1
    · rw [if_pos hj] at hc; exact absurd hc (by simp)
    · rw [if_neg hj] at hc
      exact ⟨q, rfl, by omega, (Option.some.inj hc).symm⟩

theorem descChild_eq_some_of {p : RawDescSI × ℕ × RawCoset} {q : List ℕ × ℕ}
    (hq : p.1.2 = some q) (hj : p.2.1 < q.2) :
    descChild p
      = some ((p.1.1.1, descKer p.1.1 q.1, descRep p.1.1 q p.2.1,
        p.1.1.2.2.2.1, p.1.1.2.2.2.2), none) := by
  rw [descChild, hq]
  simp only [Option.elim]
  rw [if_neg (by omega)]

/-- **The Descent round** (§11.1, Prop. 11.1.6, Eq. (62)).  `solve` is the rest of Procedure
String-Isomorphism: it answers an instance the round does not descend on. -/
def descentRound (n : ℕ) (solve : RawDescSI → RawCoset) :
    Round RawDescSI RawCoset RawCoset where
  WF := DescWF n
  ground := fun I => Enc.size I.1.2.2.2
  measure := fun I => I.2.elim 0 (fun _ => 1)
  width := fun I => I.2.elim 0 (fun q => q.2)
  child := descChild
  init := fun _ => none
  combine := descCombine
  finish := fun p => p.1.2.elim (solve p.1) (fun _ => p.2)
  bot := none
  child_eq_none := by
    intro I j s hj
    rw [descChild]
    obtain ⟨o, hq⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
    cases o with
    | none => rw [hq]; rfl
    | some q =>
        rw [hq] at hj ⊢
        simp only [Option.elim] at hj ⊢
        rw [if_pos hj]
  child_wf := by
    rintro I j s J hI hc
    obtain ⟨q, hq, hjlt, rfl⟩ := descChild_eq_some (p := (I, j, s)) hc
    obtain ⟨hx, hy, hnd, hlt, hgs, hgl, hσ, hinv⟩ := hI.1
    refine ⟨⟨hx, hy, hnd, hlt, wf_descKer hI hq, length_descKer_le hI hq,
      wf_descRep hI hq j, ?_⟩, ?_⟩
    · rw [rawIsInvariant_eq_true_iff (wf_descKer hI hq) hlt]
      exact isInvariant_of_le ((rawIsInvariant_eq_true_iff hgs hlt).1 hinv) (descKer_le hI hq)
    · intro d' idx' hcon
      exact absurd hcon (by simp)
  child_measure := by
    rintro I j s J hI hc
    obtain ⟨q, hq, hjlt, rfl⟩ := descChild_eq_some (p := (I, j, s)) hc
    show (Option.elim none 0 (fun _ => 1) : ℕ) < I.2.elim 0 (fun _ => 1)
    rw [hq]
    simp
  child_ground := by
    rintro I j s J hI hc
    obtain ⟨q, hq, hjlt, rfl⟩ := descChild_eq_some (p := (I, j, s)) hc
    exact le_refl _

/-! ## The link to the mathematical layer -/

/-- The mathematical round the descent round implements: the chain of Eq. (62) over the coset
representatives of the kernel, or the leaf that hands the instance to the rest of the
procedure. -/
noncomputable def descentRoundReduction (n : ℕ) (solve : RawDescSI → RawCoset)
    (I : RawDescSI) : Babai.SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  I.2.elim (.done (decCoset n (solve I))) (fun q =>
    descentChain (decGroup n (descKer I.1 q.1) : Set (Perm (Fin n))) (winSet n I.1.1)
      (decStrN n I.1.2.2.2.1) (decStrN n I.1.2.2.2.2) ∅ (descPerms n I.1 q))

/-- **The fold of the raw round walks the chain.** -/
theorem loopMatch_descentRound (n : ℕ) (solve : RawDescSI → RawCoset) {I : RawDescSI}
    (hI : DescWF n I) {q : List ℕ × ℕ} (hq : I.2 = some q) :
    ∀ (k j : ℕ), j + k = q.2 →
      ∀ (acc : Set (Perm (Fin n))) (s : RawCoset), decCoset n s = acc →
        LoopMatch (descentRound n solve) (decDescSI n) (decCoset n) I k j s
          (descentChain (decGroup n (descKer I.1 q.1) : Set (Perm (Fin n))) (winSet n I.1.1)
            (decStrN n I.1.2.2.2.1) (decStrN n I.1.2.2.2.2) acc
            ((descPerms n I.1 q).drop j)) := by
  have hx : I.1.2.2.2.1.length = n := hI.1.1
  intro k
  induction k with
  | zero =>
      intro j hj acc s hs
      have hdrop : (descPerms n I.1 q).drop j = [] := by
        apply List.drop_eq_nil_of_le
        rw [length_descPerms]; omega
      rw [hdrop, descentChain]
      refine LoopMatch.done 0 j s acc ?_ ?_
      · exact (descentRound n solve).child_eq_none I j s
          (by show I.2.elim 0 (fun q => q.2) ≤ j; rw [hq]; simp only [Option.elim]; omega)
      · show decCoset n (I.2.elim (solve I) (fun _ => s)) = acc
        rw [hq]
        exact hs
  | succ k ih =>
      intro j hj acc s hs
      have hjl : j < (descPerms n I.1 q).length := by rw [length_descPerms]; omega
      have hdrop : (descPerms n I.1 q).drop j
          = ((descPerms n I.1 q)[j]'hjl) :: (descPerms n I.1 q).drop (j + 1) :=
        List.drop_eq_getElem_cons hjl
      rw [hdrop, descentChain]
      have hjlt : j < q.2 := by rw [length_descPerms] at hjl; omega
      set J : RawDescSI :=
        ((I.1.1, descKer I.1 q.1, descRep I.1 q j, I.1.2.2.2.1, I.1.2.2.2.2), none) with hJ
      have hchild : (descentRound n solve).child (I, j, s) = some J :=
        descChild_eq_some_of (p := (I, j, s)) hq hjlt
      have hdec : decDescSI n J
          = ⟨((descPerms n I.1 q)[j]'hjl) • (decGroup n (descKer I.1 q.1) : Set (Perm (Fin n))),
              winSet n I.1.1, decStrN n I.1.2.2.2.1, decStrN n I.1.2.2.2.2⟩ := by
        rw [decDescSI, decWinSI, hJ]
        simp only
        rw [decCoset_some, getElem_descPerms]
      rw [← hdec]
      refine LoopMatch.call k j s J _ hchild ?_
      intro a ha
      refine ih (j + 1) (by omega) (cosetHull (acc ∪ (decDescSI n J).answer))
        ((descentRound n solve).combine (I, j, s, a)) ?_
      show decCoset n (descCombine (I, j, s, a)) = _
      rw [descCombine]
      simp only
      rw [decCoset_rawCosetJoin hx, hs, ha]

/-- **The link (Prop. 11.1.6, Eq. (62)).**  The descent round implements the chain of
Eq. (62) over the coset representatives of the kernel. -/
theorem implements_descentRound (n : ℕ) (solve : RawDescSI → RawCoset) :
    Implements (descentRound n solve) id (decDescSI n) (decCoset n)
      (descentRoundReduction n solve) := by
  intro I hI
  show LoopMatch (descentRound n solve) (decDescSI n) (decCoset n) I
    (I.2.elim 0 (fun q => q.2)) 0 none (descentRoundReduction n solve I)
  rw [descentRoundReduction]
  obtain ⟨o, hq⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
  cases o with
  | none =>
      rw [hq]
      simp only [Option.elim]
      refine LoopMatch.done _ 0 _ _ ?_ ?_
      · show descChild (I, 0, (none : RawCoset)) = none
        rw [descChild, hq]
        rfl
      · show decCoset n (I.2.elim (solve I) (fun _ => (none : RawCoset))) = _
        rw [hq]
        rfl
  | some q =>
      rw [hq]
      simp only [Option.elim]
      have := loopMatch_descentRound n solve hI hq q.2 0 (by omega) ∅ none rfl
      simpa using this

/-- **The mathematical round is correct**: its value is the answer of the instance, provided
`solve` answers the instances the round hands on.

*Proof.*  `Algo.cover_descPerms` gives the decomposition of the candidate set into left cosets
of the kernel `H` (Prop. 2.2.6 (a)), and Observation 11.1.11 (`Babai.wIso_eq_smul_wAut`) says
the answer is empty or a coset; `Algo.run_descentChain` is then Eq. (62). -/
theorem run_descentRoundReduction (n : ℕ) (solve : RawDescSI → RawCoset) {I : RawDescSI}
    (hI : DescWF n I) (hsolve : I.2 = none → decCoset n (solve I) = (decDescSI n I).answer) :
    (descentRoundReduction n solve I).run = (decDescSI n I).answer := by
  rw [descentRoundReduction]
  obtain ⟨o, hq⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
  cases o with
  | none =>
    rw [hq]
    simp only [Option.elim]
    rw [Babai.SIReduction.run_done]
    exact hsolve hq
  | some q =>
    rw [hq]
    simp only [Option.elim]
    have hinv : Babai.IsInvariant (decGroup n I.1.2.1) (winSet n I.1.1) :=
      (rawIsInvariant_eq_true_iff hI.1.2.2.2.2.1 hI.1.2.2.2.1).1 hI.1.2.2.2.2.2.2.2
    refine run_descentChain _ _ _ _ _ _ (cover_descPerms hI hq) ?_
    intro τ hτ
    refine ⟨Babai.wAutSubgroup (decGroup n I.1.2.1) (winSet n I.1.1) hinv
      (decStrN n I.1.2.2.2.1), ?_⟩
    have hK : (decDescSI n I).K
        = decPerm n I.1.2.2.1 • (decGroup n I.1.2.1 : Set (Perm (Fin n))) := by
      rw [decDescSI, decWinSI, decCoset_some]
    have h := Babai.wIso_eq_smul_wAut (G := decGroup n I.1.2.1) (Δ := winSet n I.1.1) hinv
      (decPerm n I.1.2.2.1) (σ' := τ) (x := decStrN n I.1.2.2.2.1)
      (y := decStrN n I.1.2.2.2.2) (by rwa [← hK])
    rw [hK, h]
    rfl

/-! ## The running time

Every routine of the round is a `RAM.PolyFun`.  The index of the kernel travels as a machine
**natural**, and the `j`-th representative is read off the stabilizer chain
(`Algo.rawCosetRepBin`), whose running time is polynomial in the size of the instance and in
the number of bits of `j`.  So an instance is polynomially small in the domain size alone and
`Algo.descentRound.ground` is the size of the two strings, as for the Chain Rule round. -/

theorem polyFun_descKer :
    PolyFun (fun z : (List ℕ × ℕ) × (RawWinSI × ℕ) => descKer z.2.1 z.1.1) := by
  have hdom : PolyFun (fun z : (List ℕ × ℕ) × (RawWinSI × ℕ) => z.2.1.2.2.2.1) :=
    ((((polyFun_snd.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp
      polyFun_snd).comp polyFun_fst
  have hgens : PolyFun (fun z : (List ℕ × ℕ) × (RawWinSI × ℕ) => z.2.1.2.1) :=
    ((polyFun_snd.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst
  have hd : PolyFun (fun z : (List ℕ × ℕ) × (RawWinSI × ℕ) => z.1.1) :=
    polyFun_fst.comp polyFun_fst
  exact (((hdom.pair hgens).pair hd).comp polyFun_rawKerGens).of_eq (fun _ => rfl)

theorem polyFun_descRep :
    PolyFun (fun z : (List ℕ × ℕ) × (RawWinSI × ℕ) => descRep z.2.1 z.1 z.2.2) := by
  have hdom : PolyFun (fun z : (List ℕ × ℕ) × (RawWinSI × ℕ) => z.2.1.2.2.2.1) :=
    ((((polyFun_snd.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp
      polyFun_snd).comp polyFun_fst
  have hgens : PolyFun (fun z : (List ℕ × ℕ) × (RawWinSI × ℕ) => z.2.1.2.1) :=
    ((polyFun_snd.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst
  have hrep : PolyFun (fun z : (List ℕ × ℕ) × (RawWinSI × ℕ) => z.2.1.2.2.1) :=
    (((polyFun_snd.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hd : PolyFun (fun z : (List ℕ × ℕ) × (RawWinSI × ℕ) => z.1.1) :=
    polyFun_fst.comp polyFun_fst
  have hj : PolyFun (fun z : (List ℕ × ℕ) × (RawWinSI × ℕ) => z.2.2) :=
    polyFun_snd.comp polyFun_snd
  exact ((hrep.pair (((hdom.pair hgens).pair (hd.pair hj)).comp
    polyFun_rawCosetRepBin)).comp polyFun_rawMul).of_eq (fun _ => rfl)

theorem polyFun_descChild : PolyFun descChild := by
  classical
  have hx : PolyFun (fun z : (List ℕ × ℕ) × (RawWinSI × ℕ) => z.2.1.2.2.2.1) :=
    ((((polyFun_snd.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp
      polyFun_snd).comp polyFun_fst
  have hy : PolyFun (fun z : (List ℕ × ℕ) × (RawWinSI × ℕ) => z.2.1.2.2.2.2) :=
    ((((polyFun_snd.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp
      polyFun_snd).comp polyFun_snd
  have hΔ : PolyFun (fun z : (List ℕ × ℕ) × (RawWinSI × ℕ) => z.2.1.1) :=
    (polyFun_snd.comp polyFun_fst).comp polyFun_fst
  have hcond : PolyFun (fun z : (List ℕ × ℕ) × (RawWinSI × ℕ) =>
      decide (z.1.2 ≤ z.2.2)) :=
    ((polyFun_fst.comp polyFun_snd).pair (polyFun_snd.comp polyFun_snd)).comp polyFun_le
  have hsome : PolyFun (fun z : (List ℕ × ℕ) × (RawWinSI × ℕ) =>
      (some ((z.2.1.1, descKer z.2.1 z.1.1, descRep z.2.1 z.1 z.2.2,
        z.2.1.2.2.2.1, z.2.1.2.2.2.2), none) : Option RawDescSI)) :=
    (((hΔ.pair (polyFun_descKer.pair (polyFun_descRep.pair (hx.pair hy)))).pair
      (polyFun_const (none : Option (List ℕ × ℕ)))).comp polyFun_some)
  have hbody : PolyFun (fun z : (List ℕ × ℕ) × (RawWinSI × ℕ) =>
      if z.1.2 ≤ z.2.2 then (none : Option RawDescSI)
      else some ((z.2.1.1, descKer z.2.1 z.1.1, descRep z.2.1 z.1 z.2.2,
        z.2.1.2.2.2.1, z.2.1.2.2.2.2), none)) :=
    (PolyFun.ite hcond (polyFun_const (none : Option RawDescSI)) hsome).of_eq (fun z => by
      by_cases h : z.1.2 ≤ z.2.2 <;> simp [h])
  have hopt := PolyFun.optionElim (polyFun_const (none : Option RawDescSI)) hbody
  have hin : PolyFun (fun p : RawDescSI × ℕ × RawCoset =>
      ((p.1.2, ((p.1.1, p.2.1) : RawWinSI × ℕ)) :
        Option (List ℕ × ℕ) × (RawWinSI × ℕ))) :=
    (polyFun_fst.comp polyFun_snd).pair
      ((polyFun_fst.comp polyFun_fst).pair (polyFun_snd.comp polyFun_fst))
  refine (hin.comp hopt).of_eq (fun p => ?_)
  rw [descChild]

theorem polyFun_descCombine : PolyFun descCombine := by
  have hx : PolyFun (fun p : RawDescSI × ℕ × RawCoset × RawCoset => p.1.1.2.2.2.1) :=
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp
      polyFun_snd).comp polyFun_fst
  exact ((hx.pair (((polyFun_snd.comp polyFun_snd).comp polyFun_fst).pair
    ((polyFun_snd.comp polyFun_snd).comp polyFun_snd))).comp
      polyFun_rawCosetJoin).of_eq (fun _ => rfl)

/-! ## The cost of the round

`Algo.Round.Cost` asks for one polynomial bounding instances, states and answers in terms of
`ground`, and here `ground` is the size of the pair of strings, as in `Algo.chainCost`.  The
descent data is a window of at most `n` points and a number below `n^n`
(`Algo.size_winCosetIndex_le`), so it is polynomially small too.

Proposition 11.1.6 alone says nothing about `|G : H|`, so the **width** bound is a parameter
of `Algo.descentCost`: the caller supplies a `RAM.QuasiPolyBound` for it.  In §15 that bound
is line 2, `|Ḡ| ≤ ℓ!` with `ℓ = (log n)³`. -/

/-- The size of the value of an `Option.elim` whose two branches are both small. -/
theorem size_elim_le {α β : Type*} [Enc β] (o : Option α) (a b : β) (bd : ℕ)
    (ha : Enc.size a ≤ bd) (hb : Enc.size b ≤ bd) :
    Enc.size (o.elim a (fun _ => b)) ≤ bd := by
  cases o with
  | none => exact ha
  | some _ => exact hb

/-- The size of the descent data: a window of at most `m` points below `m`, and the index of
the kernel, a natural of at most `m² + 1` bits. -/
def descDataBound (m : ℕ) : ℕ := 2 + 2 * strBound m + 2 * (m * m + 3)

/-- **The size bound of the descent round.** -/
def descBound (m : ℕ) : ℕ := 2 * chainBound m + 2 * descDataBound m

theorem chainBound_le_descBound (m : ℕ) : chainBound m ≤ descBound m := by
  have h1 : descBound m = 2 * chainBound m + 2 * descDataBound m := rfl
  omega

theorem four_le_descBound (m : ℕ) : 4 ≤ descBound m := by
  have h1 : descBound m = 2 * chainBound m + 2 * descDataBound m := rfl
  have h2 : descDataBound m = 2 + 2 * strBound m + 2 * (m * m + 3) := rfl
  omega

theorem polyBound_descDataBound : PolyBound descDataBound := by
  have hS : PolyBound strBound :=
    (polyBound_const 1).add (polyBound_id.mul
      (((polyBound_const 2).mul (polyBound_id.add (polyBound_const 2))).add
        (polyBound_const 1)))
  exact ((polyBound_const 2).add ((polyBound_const 2).mul hS)).add
    ((polyBound_const 2).mul ((polyBound_id.mul polyBound_id).add (polyBound_const 3)))

theorem polyBound_descBound : PolyBound descBound :=
  ((polyBound_const 2).mul polyBound_chainBound).add
    ((polyBound_const 2).mul polyBound_descDataBound)

theorem mono_descDataBound : Monotone descDataBound := by
  intro a b hab
  have h1 : strBound a ≤ strBound b :=
    Nat.add_le_add_left (Nat.mul_le_mul hab (by omega)) 1
  have h2 : a * a ≤ b * b := Nat.mul_le_mul hab hab
  have h3 : descDataBound a = 2 + 2 * strBound a + 2 * (a * a + 3) := rfl
  have h4 : descDataBound b = 2 + 2 * strBound b + 2 * (b * b + 3) := rfl
  omega

theorem mono_descBound : Monotone descBound := by
  intro a b hab
  have h1 : chainBound a ≤ chainBound b := mono_chainBound hab
  have h2 : descDataBound a ≤ descDataBound b := mono_descDataBound hab
  have h3 : descBound a = 2 * chainBound a + 2 * descDataBound a := rfl
  have h4 : descBound b = 2 * chainBound b + 2 * descDataBound b := rfl
  omega

/-- The domain size is at most the size of the strings, which is the ground size. -/
theorem le_ground {I : RawDescSI} (hI : DescWF n I) : n ≤ Enc.size I.1.2.2.2 :=
  le_size_strings hI.1

/-- **The descent data is polynomially small.**  The window is a repetition-free list of
points of the domain, and the index of the kernel is below `n^n`
(`Algo.size_winCosetIndex_le`). -/
theorem size_descData_le {I : RawDescSI} (hI : DescWF n I) :
    Enc.size I.2 ≤ descDataBound (Enc.size I.1.2.2.2) := by
  set m := Enc.size I.1.2.2.2 with hm
  have hnm : n ≤ m := le_ground hI
  have hbd : descDataBound m = 2 + 2 * strBound m + 2 * (m * m + 3) := rfl
  obtain ⟨o, ho⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
  cases o with
  | none =>
      rw [ho]
      have h1 : Enc.size (none : Option (List ℕ × ℕ)) = 2 := size_none
      omega
  | some q =>
      obtain ⟨hnd, hlt, hidx⟩ := hI.2 q.1 q.2 ho
      rw [ho]
      have h0 : Enc.size (some q) = Enc.size q + 2 := size_some_eq _
      have h1 : Enc.size q ≤ 2 * Enc.size q.1 + 2 * Enc.size q.2 := size_pair_le' q
      have h2 : Enc.size q.1 ≤ strBound m :=
        size_natList_le (le_trans (length_le_of_nodup_lt hnd hlt) hnm)
          (fun a ha => lt_of_lt_of_le (hlt a ha) hnm)
      have h3 : Enc.size q.2 ≤ m * m + 3 := by
        have e1 : Enc.size q.2 = Nat.size q.2 + 2 := Small.size_nat q.2
        have e2 : Nat.size q.2 ≤ n * n + 1 := by
          rw [hidx]
          exact size_winCosetIndex_le hnd hlt _
        have e3 : n * n ≤ m * m := Nat.mul_le_mul hnm hnm
        omega
      omega

/-- **A well-formed descent instance is small.** -/
theorem size_descSI_le {I : RawDescSI} (hI : DescWF n I) :
    Enc.size I ≤ descBound (Enc.size I.1.2.2.2) := by
  have h1 : Enc.size I ≤ 2 * Enc.size I.1 + 2 * Enc.size I.2 := size_pair_le' I
  have h2 : Enc.size I.1 ≤ chainBound (Enc.size I.1.2.2.2) := size_winSI_le hI.1
  have h3 : Enc.size I.2 ≤ descDataBound (Enc.size I.1.2.2.2) := size_descData_le hI
  have h4 : descBound (Enc.size I.1.2.2.2)
      = 2 * chainBound (Enc.size I.1.2.2.2) + 2 * descDataBound (Enc.size I.1.2.2.2) := rfl
  omega

/-- **The cost data of the descent round.**  `solve` is charged for, as in `Algo.chainCost`.
The width bound `wb` comes from the caller: Proposition 11.1.6 is stated for an arbitrary
subgroup and says nothing about `|G : H|`.  Paper: §15, line 2. -/
def descentCost (n : ℕ) (solve : RawDescSI → RawCoset)
    (hsolve : QuasiPolyFun solve)
    (hsize : ∀ I, DescWF n I → Enc.size (solve I) ≤ descBound (Enc.size I.1.2.2.2))
    (wb : ℕ → ℕ) (hwb : QuasiPolyBound wb)
    (hwidth : ∀ I, DescWF n I → I.2.elim 0 (fun q => q.2) ≤ wb (Enc.size I.1.2.2.2)) :
    Round.Cost (descentRound n solve) where
  bound := descBound
  polyBound_bound := polyBound_descBound
  mono_bound := mono_descBound
  widthBound := wb
  quasiPolyBound_widthBound := hwb
  quasiPolyFun_child := polyFun_descChild.quasiPolyFun
  quasiPolyFun_init := (polyFun_const (none : RawCoset)).quasiPolyFun
  quasiPolyFun_combine := polyFun_descCombine.quasiPolyFun
  quasiPolyFun_finish := by
    have hopt := QuasiPolyFun.optionElim
      (g := fun z : RawDescSI × RawCoset => solve z.1)
      (h := fun z : (List ℕ × ℕ) × (RawDescSI × RawCoset) => z.2.2)
      (polyFun_fst.comp_quasi hsolve) (polyFun_snd.comp polyFun_snd).quasiPolyFun
    have hin : PolyFun (fun p : RawDescSI × RawCoset =>
        ((p.1.2, p) : Option (List ℕ × ℕ) × (RawDescSI × RawCoset))) :=
      (polyFun_fst.comp polyFun_snd).pair polyFun_id
    exact (hin.comp_quasi hopt).of_eq (fun p => rfl)
  ground_le := by
    intro I
    show Enc.size I.1.2.2.2 ≤ Enc.size I
    have h1 : Enc.size I.1.2.2.2 ≤ Enc.size I.1 :=
      le_trans (size_snd_le' I.1.2.2) (le_trans (size_snd_le' I.1.2) (size_snd_le' I.1))
    have h2 : Enc.size I.1 ≤ Enc.size I := size_fst_le' I
    omega
  size_le := fun I hI => size_descSI_le hI
  init_le := by
    intro I hI
    have h1 : Enc.size ((descentRound n solve).init I) = 2 := size_none
    have h2 := four_le_descBound (Enc.size I.1.2.2.2)
    show Enc.size ((descentRound n solve).init I) ≤ descBound (Enc.size I.1.2.2.2)
    omega
  combine_le := by
    intro I j s a hI hs ha
    show Enc.size (descCombine (I, j, s, a)) ≤ descBound (Enc.size I.1.2.2.2)
    rw [descCombine]
    exact size_rawCosetJoin_le (n := n) hI.1.1 (le_ground hI)
      (chainBound_le_descBound _) hs ha
  finish_le := by
    intro I s hI hs
    show Enc.size (I.2.elim (solve I) (fun _ => s)) ≤ descBound (Enc.size I.1.2.2.2)
    exact size_elim_le I.2 _ _ _ (hsize I hI) hs
  bot_le := by
    intro m
    have h1 : Enc.size (none : RawCoset) = 2 := size_none
    have h2 := four_le_descBound m
    show Enc.size (none : RawCoset) ≤ descBound m
    omega
  width_le := fun I hI => hwidth I hI

end Algo
