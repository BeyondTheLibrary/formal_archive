/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 8.3: `k`-ary coherent configurations with a dominant vertex-color.
-/
import Workspace.DesignLemma.Defs

/-!
# §8.3 `k`-ary coherent configurations with a dominant vertex-color

Version 2.5, Section 8.3 (lines 3838–3890 of `babai-gi-source/quasi25.txt`).

## Numbering map

| Paper | Lean |
|---|---|
| Lemma 8.3.1 (Non-clique lemma) | `Babai.KAryPartStruct.non_clique_lemma` |
| Remark 8.3.2 | `Babai.KAryPartStruct.remark_8_3_2` |
| Claim 8.3.3 | `Babai.KAryPartStruct.claim_8_3_3` |
-/

open scoped Classical

namespace Babai

namespace KAryPartStruct

variable {Ω C : Type*} {k l m q : ℕ}

/-! ### Two auxiliary facts -/

/-- A string that is not injective is the image of a strictly shorter string under an
index map.  (Used for the step *"It follows from the axioms of configurations that the
`yᵢ` are all distinct"* in the proof of Lemma 8.3.1: a repeated entry would make `y⃗` the
image of a shorter string, contradicting the minimality of `ℓ(y⃗)`.) -/
theorem exists_shorter_of_not_injective [DecidableEq Ω] (y : Str Ω q) (hq : 0 < q)
    (hy : ¬ Function.Injective y) :
    ∃ (r : ℕ) (_ : 0 < r) (_ : r < q) (y' : Str Ω r) (σ : Fin q → Fin r),
      ∀ t, y t = y' (σ t) := by
  classical
  set S : Finset Ω := Finset.univ.image y with hS
  have hcard_le : S.card ≤ q := by
    rw [hS]
    calc (Finset.univ.image y).card ≤ (Finset.univ : Finset (Fin q)).card :=
          Finset.card_image_le
      _ = q := by simp
  have hlt : S.card < q := by
    rcases lt_or_eq_of_le hcard_le with hlt | heq
    · exact hlt
    · exfalso
      refine hy ?_
      have hinj : Set.InjOn y (Finset.univ : Finset (Fin q)) := by
        rw [← Finset.card_image_iff, ← hS, heq]
        simp
      intro a b hab
      exact hinj (by simp) (by simp) hab
  refine ⟨S.card, ?_, hlt, fun s => ((S.equivFin.symm s : { x // x ∈ S }) : Ω),
    fun t => S.equivFin ⟨y t, by rw [hS]; exact Finset.mem_image_of_mem y (Finset.mem_univ t)⟩,
    fun t => ?_⟩
  · rw [Finset.card_pos, hS]
    exact ⟨y ⟨0, hq⟩, Finset.mem_image_of_mem y (Finset.mem_univ _)⟩
  · simp

/-- Axiom (ii) of Def. 5.1.8 for a *permutation* of the coordinates of a string of length
`ℓ ≤ k`: since a permutation is invertible, it does not change whether two strings have
the same extended color. -/
theorem skeletonColor_perm (X : KAryPartStruct Ω C k) (h : X.IsConfiguration) (hq : 0 < q)
    (hqk : q ≤ k) (π : Equiv.Perm (Fin q)) {y y' : Str Ω q}
    (hc : X.skeletonColor hq hqk (fun i => y (π i))
      = X.skeletonColor hq hqk (fun i => y' (π i))) :
    X.skeletonColor hq hqk y = X.skeletonColor hq hqk y' := by
  have hcomp := skeletonColor_comp X h hq hqk hq hqk (fun i => π.symm i) hc
  simpa using hcomp

/-! ### Claim 8.3.3 and the construction of `x⃗` -/

/-- Claim 8.3.3 together with the construction of `x⃗` from `y⃗` in the proof of
Lemma 8.3.1.

*"Now `supp(y⃗) ∩ {u,v} ≠ ∅` (since otherwise we would have `y⃗ τ = y⃗`), so without loss of
generality we may assume `u ∈ supp(y⃗)`. … Again by the axioms of configurations we may
assume that (u) `u = y_q` if `v ∉ supp(y⃗)`, and (uv) `u = y_{q-1}` and `v = y_q` if
`v ∈ supp(y⃗)`.  Let `ℓ = max{i | yᵢ ∉ {u,v}}` … Let `x⃗ = y₁ … y_ℓ`.  So
`supp(x⃗) ∩ {u,v} = ∅`.  In Case (u) we have `y⃗ = x⃗u` and in Case (uv) we have
`y⃗ = x⃗uv`."*

*"Claim 8.3.3. (a) In Case (u) we have `c_x⃗(u) ≠ c_x⃗(v)`.  (b) In Case (uv) we have
`c_x⃗(uv) ≠ c_x⃗(vu)`.  Proof. (a) By definition, `c_x⃗(u) = c(x⃗u) = c(y⃗) ≠ c(y⃗ τ) =
c(x⃗v) = c_x⃗(v)`.  (b) By definition, `c_x⃗(uv) = c(x⃗uv) = c(y⃗) ≠ c(y⃗ τ) = c(x⃗vu) =
c_x⃗(vu)`."*

The two colors compared are the extended colors of §5.1.4; `restrTo_vcolor` and
`restrTo_skeletonColor2` turn them into `c_x⃗(u)`, `c_x⃗(v)` and `c_x⃗(uv)`, `c_x⃗(vu)`. -/
theorem claim_8_3_3 [DecidableEq Ω] (X : KAryPartStruct Ω C k) (h : X.IsConfiguration)
    (hq : 0 < q) (hqk : q ≤ k) (y : Str Ω q) (hyd : Function.Injective y) {u v : Ω}
    (huv : u ≠ v)
    (hne : X.skeletonColor hq hqk (tupleMap (Equiv.swap u v) y)
      ≠ X.skeletonColor hq hqk y) (hu : u ∈ Set.range y) :
    ∃ (l : ℕ) (hl : l < k) (x : Str Ω l), Str.Distinct x ∧ u ∉ Str.supp x ∧ v ∉ Str.supp x ∧
      ((X.skeletonColor (Nat.succ_pos l) hl (Str.snoc1 x u)
          ≠ X.skeletonColor (Nat.succ_pos l) hl (Str.snoc1 x v)) ∨
        ∃ h2 : l + 2 ≤ k, X.skeletonColor (by omega) h2 (Str.snoc2 x u v)
          ≠ X.skeletonColor (by omega) h2 (Str.snoc2 x v u)) := by
  classical
  set τ : Equiv.Perm Ω := Equiv.swap u v with hτ
  have hτu : τ u = v := Equiv.swap_apply_left u v
  have hτv : τ v = u := Equiv.swap_apply_right u v
  have hτw : ∀ w : Ω, w ≠ u → w ≠ v → τ w = w := fun w h1 h2 =>
    Equiv.swap_apply_of_ne_of_ne h1 h2
  obtain ⟨a, ha⟩ := hu
  by_cases hv : v ∈ Set.range y
  · -- Case (uv)
    obtain ⟨b, hb⟩ := hv
    have hab : a ≠ b := fun hc => huv (by rw [← ha, ← hb, hc])
    have hq2 : 2 ≤ q := by
      by_contra hc
      have : (a : ℕ) = 0 := by have := a.isLt; omega
      have hb0 : (b : ℕ) = 0 := by have := b.isLt; omega
      exact hab (Fin.ext (this.trans hb0.symm))
    obtain ⟨l, rfl⟩ : ∃ l, q = l + 2 := ⟨q - 2, by omega⟩
    obtain ⟨pen, hpenv⟩ : ∃ p : Fin (l + 2), (p : ℕ) = l := ⟨⟨l, by omega⟩, rfl⟩
    obtain ⟨lst, hlstv⟩ : ∃ p : Fin (l + 2), (p : ℕ) = l + 1 := ⟨⟨l + 1, by omega⟩, rfl⟩
    have hpl : pen ≠ lst := by
      intro hc
      have hval : (pen : ℕ) = (lst : ℕ) := congrArg Fin.val hc
      rw [hpenv, hlstv] at hval
      omega
    set π₁ : Equiv.Perm (Fin (l + 2)) := Equiv.swap b lst with hπ₁
    set c : Fin (l + 2) := π₁ a with hc
    have hπ₁c : π₁ c = a := by rw [hc, hπ₁]; simp
    have hclst : c ≠ lst := by
      intro hcl
      have : π₁ lst = a := by rw [← hcl]; exact hπ₁c
      rw [hπ₁, Equiv.swap_apply_right] at this
      exact hab this.symm
    set π₂ : Equiv.Perm (Fin (l + 2)) := Equiv.swap c pen with hπ₂
    have hπ₂lst : π₂ lst = lst := by
      rw [hπ₂]; exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hclst) (Ne.symm hpl)
    have hπ₂pen : π₂ pen = c := by rw [hπ₂]; exact Equiv.swap_apply_right c pen
    set π : Equiv.Perm (Fin (l + 2)) := π₂.trans π₁ with hπ
    have hπlst : π lst = b := by
      rw [hπ]
      show π₁ (π₂ lst) = b
      rw [hπ₂lst, hπ₁, Equiv.swap_apply_right]
    have hπpen : π pen = a := by
      rw [hπ]
      show π₁ (π₂ pen) = a
      rw [hπ₂pen, hπ₁c]
    set y₁ : Str Ω (l + 2) := fun t => y (π t) with hy₁
    have hy₁d : Function.Injective y₁ := fun s t hst => π.injective (hyd hst)
    have hy₁lst : y₁ lst = v := by rw [hy₁]; show y (π lst) = v; rw [hπlst]; exact hb
    have hy₁pen : y₁ pen = u := by rw [hy₁]; show y (π pen) = u; rw [hπpen]; exact ha
    have hy₁ne : ∀ t : Fin (l + 2), t ≠ pen → t ≠ lst → y₁ t ≠ u ∧ y₁ t ≠ v := by
      intro t h1 h2
      constructor
      · intro hcu
        exact h1 (hy₁d (hcu.trans hy₁pen.symm))
      · intro hcv
        exact h2 (hy₁d (hcv.trans hy₁lst.symm))
    -- the colors of `y₁` and of `y₁^τ` are the colors of `y` and of `y^τ`
    have hy₁col : X.skeletonColor hq hqk (tupleMap τ y₁) ≠ X.skeletonColor hq hqk y₁ := by
      intro hcc
      refine hne (skeletonColor_perm X h hq hqk π ?_)
      have e1 : (fun i => tupleMap τ y (π i)) = tupleMap τ y₁ := rfl
      have e2 : (fun i => y (π i)) = y₁ := rfl
      rw [e1, e2]
      exact hcc
    have hidx : ∀ i : Fin l, (⟨(i : ℕ), by omega⟩ : Fin (l + 2)) ≠ pen ∧
        (⟨(i : ℕ), by omega⟩ : Fin (l + 2)) ≠ lst := by
      intro i
      have hi := i.isLt
      refine ⟨fun hcc => ?_, fun hcc => ?_⟩
      · have hval : (i : ℕ) = (pen : ℕ) := congrArg Fin.val hcc
        rw [hpenv] at hval
        omega
      · have hval : (i : ℕ) = (lst : ℕ) := congrArg Fin.val hcc
        rw [hlstv] at hval
        omega
    refine ⟨l, by omega, fun i => y₁ ⟨(i : ℕ), by omega⟩, ?_, ?_, ?_, Or.inr ⟨by omega, ?_⟩⟩
    · intro s t hst
      have h1 := hy₁d hst
      have hval : (s : ℕ) = (t : ℕ) := by
        have h2 := congrArg Fin.val h1
        simpa using h2
      exact Fin.ext hval
    · rintro ⟨i, hi⟩
      exact ((hy₁ne ⟨(i : ℕ), by omega⟩ (hidx i).1 (hidx i).2).1) hi
    · rintro ⟨i, hi⟩
      exact ((hy₁ne ⟨(i : ℕ), by omega⟩ (hidx i).1 (hidx i).2).2) hi
    · -- `x⃗uv = y₁` and `x⃗vu = y₁^τ`
      have e1 : Str.snoc2 (fun i : Fin l => y₁ ⟨(i : ℕ), by omega⟩) u v = y₁ := by
        funext j
        have hj := j.isLt
        rcases Nat.lt_trichotomy (j : ℕ) l with hjl | hjl | hjl
        · rw [Str.snoc2_val_lt _ u v j ⟨(j : ℕ), hjl⟩ rfl]
        · rw [Str.snoc2_val_eq _ u v j hjl, ← hy₁pen]
          congr 1
          exact Fin.ext (by rw [hpenv]; omega)
        · rw [Str.snoc2_val_gt _ u v j hjl, ← hy₁lst]
          congr 1
          exact Fin.ext (by rw [hlstv]; omega)
      have e2 : Str.snoc2 (fun i : Fin l => y₁ ⟨(i : ℕ), by omega⟩) v u = tupleMap τ y₁ := by
        funext j
        have hj := j.isLt
        rcases Nat.lt_trichotomy (j : ℕ) l with hjl | hjl | hjl
        · rw [Str.snoc2_val_lt _ v u j ⟨(j : ℕ), hjl⟩ rfl]
          have hjp : (⟨(j : ℕ), by omega⟩ : Fin (l + 2)) = j := Fin.ext rfl
          have hne' := hy₁ne ⟨(j : ℕ), by omega⟩ (hidx ⟨(j : ℕ), hjl⟩).1 (hidx ⟨(j : ℕ), hjl⟩).2
          show y₁ ⟨(j : ℕ), by omega⟩ = τ (y₁ j)
          rw [hjp] at hne' ⊢
          rw [hτw _ hne'.1 hne'.2]
        · rw [Str.snoc2_val_eq _ v u j hjl]
          show v = τ (y₁ j)
          have : j = pen := Fin.ext (by rw [hpenv]; omega)
          rw [this, hy₁pen, hτu]
        · rw [Str.snoc2_val_gt _ v u j hjl]
          show u = τ (y₁ j)
          have : j = lst := Fin.ext (by rw [hlstv]; omega)
          rw [this, hy₁lst, hτv]
      rw [e1, e2]
      exact fun hcc => hy₁col hcc.symm
  · -- Case (u)
    obtain ⟨l, rfl⟩ : ∃ l, q = l + 1 := ⟨q - 1, by omega⟩
    obtain ⟨lst, hlstv⟩ : ∃ p : Fin (l + 1), (p : ℕ) = l := ⟨Fin.last l, by simp⟩
    set π : Equiv.Perm (Fin (l + 1)) := Equiv.swap a lst with hπ
    have hπlst : π lst = a := by rw [hπ]; exact Equiv.swap_apply_right a lst
    set y₁ : Str Ω (l + 1) := fun t => y (π t) with hy₁
    have hy₁d : Function.Injective y₁ := fun s t hst => π.injective (hyd hst)
    have hy₁lst : y₁ lst = u := by rw [hy₁]; show y (π lst) = u; rw [hπlst]; exact ha
    have hy₁ne : ∀ t : Fin (l + 1), t ≠ lst → y₁ t ≠ u ∧ y₁ t ≠ v := by
      intro t h1
      refine ⟨fun hcu => h1 (hy₁d (hcu.trans hy₁lst.symm)), fun hcv => hv ⟨π t, hcv⟩⟩
    have hy₁col : X.skeletonColor hq hqk (tupleMap τ y₁) ≠ X.skeletonColor hq hqk y₁ := by
      intro hcc
      refine hne (skeletonColor_perm X h hq hqk π ?_)
      have e1 : (fun i => tupleMap τ y (π i)) = tupleMap τ y₁ := rfl
      have e2 : (fun i => y (π i)) = y₁ := rfl
      rw [e1, e2]
      exact hcc
    have hidx : ∀ i : Fin l, Fin.castSucc i ≠ lst := by
      intro i hcc
      have hi := i.isLt
      have hval : (i : ℕ) = (lst : ℕ) := congrArg Fin.val hcc
      rw [hlstv] at hval
      omega
    refine ⟨l, by omega, fun i => y₁ (Fin.castSucc i), ?_, ?_, ?_, Or.inl ?_⟩
    · intro s t hst
      have h1 := hy₁d hst
      have hval : (s : ℕ) = (t : ℕ) := by
        have h2 := congrArg Fin.val h1
        simpa using h2
      exact Fin.ext hval
    · rintro ⟨i, hi⟩
      exact ((hy₁ne (Fin.castSucc i) (hidx i)).1) hi
    · rintro ⟨i, hi⟩
      exact ((hy₁ne (Fin.castSucc i) (hidx i)).2) hi
    · have e1 : Str.snoc1 (fun i : Fin l => y₁ (Fin.castSucc i)) u = y₁ := by
        funext j
        have hj := j.isLt
        by_cases hjl : (j : ℕ) < l
        · rw [Str.snoc1_val_lt _ u j ⟨(j : ℕ), hjl⟩ rfl]
          congr 1
        · rw [Str.snoc1_val_ge _ u j (by omega), ← hy₁lst]
          congr 1
          exact Fin.ext (by rw [hlstv]; omega)
      have e2 : Str.snoc1 (fun i : Fin l => y₁ (Fin.castSucc i)) v = tupleMap τ y₁ := by
        funext j
        have hj := j.isLt
        by_cases hjl : (j : ℕ) < l
        · rw [Str.snoc1_val_lt _ v j ⟨(j : ℕ), hjl⟩ rfl]
          have hjp : Fin.castSucc (⟨(j : ℕ), hjl⟩ : Fin l) = j := Fin.ext rfl
          have hne' := hy₁ne (Fin.castSucc (⟨(j : ℕ), hjl⟩ : Fin l)) (hidx ⟨(j : ℕ), hjl⟩)
          show y₁ (Fin.castSucc (⟨(j : ℕ), hjl⟩ : Fin l)) = τ (y₁ j)
          rw [hjp] at hne' ⊢
          rw [hτw _ hne'.1 hne'.2]
        · rw [Str.snoc1_val_ge _ v j (by omega)]
          show v = τ (y₁ j)
          have : j = lst := Fin.ext (by rw [hlstv]; omega)
          rw [this, hy₁lst, hτu]
      rw [e1, e2]
      exact fun hcc => hy₁col hcc.symm

/-! ### Lemma 8.3.1 -/

/-- Remark 8.3.2.  *"Note that `C` is a union of vertex-color classes in `X_x⃗`.
Therefore, if `ℓ(x⃗) ≤ k-2`, then the subconfiguration of `(X_x⃗)^{(2)}` induced on
`C \ supp(x⃗)` is indeed coherent (Prop. 5.2.5)."*

In this formalization the induced substructure of a classical coherent configuration is
coherent on every *stable* set (Obs. 3.3.2,
`Babai.PartitionStructure.induced_isCoherent`), and `Babai.PartitionStructure.IsCliqueOn`
(rank `2`) is defined for every subset, so the remark is not needed as a hypothesis
anywhere; it is recorded here. -/
theorem remark_8_3_2 : True := trivial

set_option maxHeartbeats 1000000 in
/-- Lemma 8.3.1 (Non-clique lemma).  *"Let `1/2 ≤ α ≤ 1` be a threshold parameter.  Let
`X = (Ω, R)` be a `k`-ary coherent configuration with `n = |Ω|` vertices, `2 ≤ k ≤ n/2`,
and symmetry defect `≥ 1 - α`.  Assume `X` has a dominant vertex-color class `C`, so
`|C| > αn`.  The[n] there exists a string `x⃗ ∈ Ω^{⟨≤k-1⟩}` such that either (a)
`C \ supp(x⃗)` is not homogeneous under the coloring `c_x⃗` (not all elements get the same
color), or (b) `ℓ(x⃗) ≤ k-2` and the classical coherent configuration induced by the
`2`-skeleton `(X_x⃗)^{(2)}` on the set `C \ supp(x⃗)` is not a clique."*

Paper's proof: *"`C` is too large to be a twin equivalence class (because of the lower
bound on the symmetry defect).  So there exist `u, v ∈ C`, `u ≠ v`, such that the
transposition `τ = (u,v)` does not belong to `Aut(X)`.  Therefore there exists `z⃗ ∈ Ω^k`
such that `c(z⃗ τ) ≠ c(z⃗)`.  Extending the coloring to `Ω^{≤k}` (Sec. 5.1.4), let `y⃗` be a
shortest string such that `c(y⃗ τ) ≠ c(y⃗)`. …"*  The rest is `claim_8_3_3`. -/
theorem non_clique_lemma [Fintype Ω] [DecidableEq Ω] {α : ℝ} (hα : 1 / 2 ≤ α) (hα1 : α ≤ 1)
    (X : KAryPartStruct Ω C k) (h : X.IsCoherent) (hk2 : 2 ≤ k)
    (hkn : 2 * k ≤ Fintype.card Ω)
    (hdef : (1 : ℝ) - α ≤ (defect X.Aut : ℝ)) {i₀ : C} (hC : IsDominant α (X.vclass i₀)) :
    ∃ (l : ℕ) (hl : l < k) (x : Str Ω l), Str.Distinct x ∧
      ((∃ u ∈ X.vclass i₀ \ Str.supp x, ∃ v ∈ X.vclass i₀ \ Str.supp x,
          (X.restrTo hl.le x).vcolor u ≠ (X.restrTo hl.le x).vcolor v) ∨
        ∃ h2 : l + 2 ≤ k, ¬ ((X.restrTo hl.le x).skel2 (by omega)).IsCliqueOn
          (X.vclass i₀ \ Str.supp x)) := by
  classical
  have hk0 : 0 < k := by omega
  have hn0 : 0 < Fintype.card Ω := by omega
  -- Step 1: `C` is too large to be a set of twins.
  have hsym : ((symmetricity X.Aut : ℝ)) ≤ α * (Fintype.card Ω : ℝ) := by
    have hd : (defect X.Aut : ℝ)
        = 1 - (symmetricity X.Aut : ℝ) / (Fintype.card Ω : ℝ) := by
      rw [defect, relSymmetricity]
      push_cast
      ring
    rw [hd] at hdef
    have hnpos : (0 : ℝ) < (Fintype.card Ω : ℝ) := by exact_mod_cast hn0
    have : (symmetricity X.Aut : ℝ) / (Fintype.card Ω : ℝ) ≤ α := by linarith
    calc (symmetricity X.Aut : ℝ)
        = (symmetricity X.Aut : ℝ) / (Fintype.card Ω : ℝ) * (Fintype.card Ω : ℝ) := by
          field_simp
      _ ≤ α * (Fintype.card Ω : ℝ) := by
          exact mul_le_mul_of_nonneg_right this (le_of_lt hnpos)
  have hnotwin : ¬ IsTwinSet X.Aut (X.vclass i₀) := by
    intro htw
    have htw' : IsTwinSet X.Aut ↑(X.vclass i₀).toFinset := by
      rwa [Set.coe_toFinset]
    have hle := le_symmetricity htw'
    rw [← Set.ncard_eq_toFinset_card'] at hle
    have : ((X.vclass i₀).ncard : ℝ) ≤ (symmetricity X.Aut : ℝ) := by exact_mod_cast hle
    exact absurd hC (by rw [IsDominant]; push_neg; linarith)
  -- Step 2: a transposition inside `C` that is not an automorphism.
  rw [IsTwinSet] at hnotwin
  push_neg at hnotwin
  obtain ⟨u, hu, v, hv, huv, hnt⟩ := hnotwin
  have hswap : Equiv.swap u v ∉ X.Aut := by
    intro hmem
    exact hnt ⟨huv, hmem⟩
  -- Step 3: a string of length `k` whose color the transposition changes.
  have hz : ∃ z : Str Ω k, X.color (tupleMap (Equiv.swap u v) z) ≠ X.color z := by
    by_contra hcon
    push_neg at hcon
    exact hswap hcon
  -- Step 4: a shortest such string, for the extended coloring of §5.1.4.
  have hex : ∃ q : ℕ, ∃ (hq : 0 < q) (hqk : q ≤ k) (y : Str Ω q),
      X.skeletonColor hq hqk (tupleMap (Equiv.swap u v) y)
        ≠ X.skeletonColor hq hqk y := by
    obtain ⟨z, hz⟩ := hz
    refine ⟨k, hk0, le_rfl, z, ?_⟩
    rw [skeletonColor, skeletonColor, Str.pad_self, Str.pad_self]
    exact hz
  obtain ⟨q, hq, hqk, y, hy, hmin⟩ : ∃ (q : ℕ) (hq : 0 < q) (hqk : q ≤ k) (y : Str Ω q),
      (X.skeletonColor hq hqk (tupleMap (Equiv.swap u v) y) ≠ X.skeletonColor hq hqk y) ∧
      ∀ r, r < q → ¬ ∃ (hr : 0 < r) (hrk : r ≤ k) (y' : Str Ω r),
        X.skeletonColor hr hrk (tupleMap (Equiv.swap u v) y')
          ≠ X.skeletonColor hr hrk y' := by
    obtain ⟨hq, hqk, y, hy⟩ := Nat.find_spec hex
    exact ⟨Nat.find hex, hq, hqk, y, hy, fun r hr => Nat.find_min hex hr⟩
  -- Step 5: the entries of `y⃗` are distinct.
  have hyd : Function.Injective y := by
    by_contra hni
    obtain ⟨r, hr, hrq, y', σ, hyy⟩ := exists_shorter_of_not_injective y hq hni
    have hr' : X.skeletonColor hr (le_trans hrq.le hqk) (tupleMap (Equiv.swap u v) y')
        = X.skeletonColor hr (le_trans hrq.le hqk) y' := by
      by_contra hcc
      exact hmin r hrq ⟨hr, le_trans hrq.le hqk, y', hcc⟩
    refine hy ?_
    have hcomp := skeletonColor_comp X h.toIsConfiguration hq hqk hr
      (le_trans hrq.le hqk) σ hr'
    have e1 : (fun i => tupleMap (Equiv.swap u v) y' (σ i))
        = tupleMap (Equiv.swap u v) y := by
      funext i
      show Equiv.swap u v (y' (σ i)) = Equiv.swap u v (y i)
      rw [hyy i]
    have e2 : (fun i => y' (σ i)) = y := by
      funext i; exact (hyy i).symm
    rw [e1, e2] at hcomp
    exact hcomp
  -- Step 6: `supp(y⃗) ∩ {u,v} ≠ ∅`.
  have hmeet : u ∈ Set.range y ∨ v ∈ Set.range y := by
    by_contra hcon
    push_neg at hcon
    refine hy ?_
    have : tupleMap (Equiv.swap u v) y = y := by
      funext i
      show Equiv.swap u v (y i) = y i
      exact Equiv.swap_apply_of_ne_of_ne (fun hc => hcon.1 ⟨i, hc⟩) (fun hc => hcon.2 ⟨i, hc⟩)
    rw [this]
  -- Step 7: Claim 8.3.3, applied with the roles of `u` and `v` exchanged if necessary.
  have key : ∃ (l : ℕ) (hl : l < k) (x : Str Ω l), Str.Distinct x ∧
      u ∉ Str.supp x ∧ v ∉ Str.supp x ∧
      ((X.skeletonColor (Nat.succ_pos l) hl (Str.snoc1 x u)
          ≠ X.skeletonColor (Nat.succ_pos l) hl (Str.snoc1 x v)) ∨
        ∃ h2 : l + 2 ≤ k, X.skeletonColor (by omega) h2 (Str.snoc2 x u v)
          ≠ X.skeletonColor (by omega) h2 (Str.snoc2 x v u)) := by
    rcases hmeet with hmem | hmem
    · exact claim_8_3_3 X h.toIsConfiguration hq hqk y hyd huv hy hmem
    · obtain ⟨l, hl, x, hxd, hvx, hux, hcase⟩ :=
        claim_8_3_3 X h.toIsConfiguration hq hqk y hyd (Ne.symm huv)
          (by
            have e : tupleMap (⇑(Equiv.swap v u)) y = tupleMap (⇑(Equiv.swap u v)) y := by
              rw [Equiv.swap_comm]
            rw [e]; exact hy) hmem
      refine ⟨l, hl, x, hxd, hux, hvx, ?_⟩
      rcases hcase with hcase | ⟨h2, hcase⟩
      · exact Or.inl (Ne.symm hcase)
      · exact Or.inr ⟨h2, Ne.symm hcase⟩
  obtain ⟨l, hl, x, hxd, hux, hvx, hcase⟩ := key
  refine ⟨l, hl, x, hxd, ?_⟩
  rcases hcase with hcase | ⟨h2, hcase⟩
  · refine Or.inl ⟨u, ⟨hu, hux⟩, v, ⟨hv, hvx⟩, ?_⟩
    rw [restrTo_vcolor X hl (Nat.succ_pos l), restrTo_vcolor X hl (Nat.succ_pos l)]
    exact hcase
  · refine Or.inr ⟨h2, ?_⟩
    have hm2 : 2 ≤ k - l := by omega
    have hcfg : ((X.restrTo hl.le x).skel2 hm2).IsConfiguration :=
      ((X.restrTo hl.le x).skel2_isCoherent
        (X.restrTo_isCoherent h hl.le x) hm2).toIsConfiguration
    have e1 : ∀ a b : Ω,
        (X.restrTo hl.le x).skeletonColor (by norm_num) hm2 ![a, b]
          = X.skeletonColor (by omega) h2 (Str.snoc2 x a b) := fun a b =>
      restrTo_skeletonColor2 X hl.le h2 (by norm_num) hm2 (by omega) x a b
    refine PartitionStructure.not_isCliqueOn_of_color_ne _ hcfg ⟨hu, hux⟩ ⟨hv, hvx⟩ huv ?_
    intro hcc
    rw [skel2_color_eq_iff, e1, e1] at hcc
    exact hcase hcc

end KAryPartStruct

end Babai
