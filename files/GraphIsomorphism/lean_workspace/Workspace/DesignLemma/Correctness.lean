/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 8.4: completing the proof of the Design Lemma (Theorem 8.2.1).
-/
import Workspace.DesignLemma.NonClique

/-!
# §8.4 Completing the proof of the Design Lemma

Version 2.5, Section 8.4 (lines 3891–3925 of `babai-gi-source/quasi25.txt`).

## Numbering map

| Paper | Lean |
|---|---|
| item (A) in the proof of Thm 8.2.1 | `Babai.KAryPartStruct.AllDominant` |
| item (B) in the proof of Thm 8.2.1 | `Babai.KAryPartStruct.AllClique` |
| Eq. (47) | `Babai.KAryPartStruct.dominantClass_subset_parent`, `.notMem_dominantClass_of_mem_supp` |
| Claim 8.4.1, Eq. (48) | `Babai.KAryPartStruct.claim_8_4_1` |
| Claim 8.4.2, Eq. (49) | `Babai.KAryPartStruct.claim_8_4_2` |
| Theorem 8.2.1 | `Babai.KAryPartStruct.theorem_8_2_1` |
| Remark 8.2.2 | `Babai.KAryPartStruct.remark_8_2_2` |
-/

open scoped Classical

namespace Babai

namespace KAryPartStruct

variable {Ω C : Type*} {k l : ℕ}

/-! ### Preliminaries on restrictions along a prefix -/

/-- The restriction by the empty string is the structure itself. -/
theorem restrTo_empty (X : KAryPartStruct Ω C k) :
    X.restrTo (Nat.zero_le k) Str.empty = X := by
  have hcol : ∀ y : Str Ω (k - 0),
      (X.restrTo (Nat.zero_le k) Str.empty).color y = X.color y := by
    intro y
    rw [restrTo_color]
    congr 1
  cases X with
  | mk c => exact congrArg KAryPartStruct.mk (funext hcol)

/-- Eq. (47), first half: *"the vertex-coloring by `c_x⃗` is a refinement of the
vertex-coloring of `c_y⃗`"* for the parent `y⃗` of `x⃗ = y⃗z`.

Proof: the extended color `c(y⃗zw)` determines `c(y⃗w)` by axiom (ii) of Def. 5.1.8 applied
to the index map `[ℓ+1] → [ℓ+2]` that fixes `1,…,ℓ` and sends `ℓ+1` to `ℓ+2`. -/
theorem restrTo_vcolor_parent (X : KAryPartStruct Ω C k) (h : X.IsConfiguration)
    (hl1 : l + 1 < k) (y : Str Ω l) (z : Ω) {w w' : Ω}
    (hc : (X.restrTo hl1.le (Str.snoc1 y z)).vcolor w
      = (X.restrTo hl1.le (Str.snoc1 y z)).vcolor w') :
    (X.restrTo (by omega : l ≤ k) y).vcolor w
      = (X.restrTo (by omega : l ≤ k) y).vcolor w' := by
  have hly : l < k := by omega
  simp only [restrTo_vcolor X hl1 (by omega : 0 < l + 1 + 1), Str.snoc1_snoc1] at hc
  simp only [restrTo_vcolor X hly (by omega : 0 < l + 1)]
  set σ : Fin (l + 1) → Fin (l + 2) := fun i =>
    if hi : (i : ℕ) < l then ⟨(i : ℕ), by omega⟩ else ⟨l + 1, by omega⟩ with hσ
  have key : ∀ a : Ω, (fun i => Str.snoc2 y z a (σ i)) = Str.snoc1 y a := by
    intro a
    funext i
    have hi := i.isLt
    by_cases hil : (i : ℕ) < l
    · rw [hσ]
      simp only [dif_pos hil]
      rw [Str.snoc2_val_lt y z a _ ⟨(i : ℕ), hil⟩ rfl,
        Str.snoc1_val_lt y a i ⟨(i : ℕ), hil⟩ rfl]
    · rw [hσ]
      simp only [dif_neg hil]
      rw [Str.snoc2_val_gt y z a _ (by simp), Str.snoc1_val_ge y a i (by omega)]
  have hcomp := skeletonColor_comp X h (Nat.succ_pos l) hly
    (by omega : 0 < l + 2) (by omega : l + 2 ≤ k) σ hc
  rw [key w, key w'] at hcomp
  exact hcomp

/-- Eq. (47), second half: *"`C(x⃗) ∩ supp(x⃗) = ∅`"*.  A vertex of `supp(x⃗)` is alone in
its vertex-color class of `X_x⃗` — by axiom (i) of Def. 5.1.8, the color `c(x⃗w)` records
whether `w` equals a given entry of `x⃗` — so its class is a singleton and cannot be
dominant. -/
theorem notMem_dominantClass_of_mem_supp [Fintype Ω] {α : ℝ}
    (X : KAryPartStruct Ω C k) (h : X.IsConfiguration) (hl : l < k) {x : Str Ω l}
    {z : Ω} (hz : z ∈ Str.supp x) (hn : (1 : ℝ) ≤ α * (Fintype.card Ω : ℝ)) :
    z ∉ dominantClass α (X.restrTo hl.le x) := by
  classical
  intro hmem
  have hdom : IsDominant α ((X.restrTo hl.le x).vclass
    ((X.restrTo hl.le x).vcolor z)) := hmem
  obtain ⟨j, hj⟩ := hz
  have hsing : (X.restrTo hl.le x).vclass ((X.restrTo hl.le x).vcolor z) = {z} := by
    refine Set.Subset.antisymm (fun w hw => ?_) (fun w hw => ?_)
    · have hcol : X.skeletonColor (Nat.succ_pos l) hl (Str.snoc1 x w)
          = X.skeletonColor (Nat.succ_pos l) hl (Str.snoc1 x z) := by
        rw [← restrTo_vcolor X hl (Nat.succ_pos l), ← restrTo_vcolor X hl (Nat.succ_pos l)]
        exact hw
      have hcfg := X.skeleton_isConfiguration h (Nat.succ_pos l) hl
      have hrho := hcfg.rho (Str.snoc1 x w) (Str.snoc1 x z) hcol
        (Fin.castSucc j) (Fin.last l)
      have hz1 : Str.snoc1 x z (Fin.castSucc j) = Str.snoc1 x z (Fin.last l) := by
        rw [Str.snoc1_val_lt x z (Fin.castSucc j) j (by simp),
          Str.snoc1_val_ge x z (Fin.last l) (by simp)]
        exact hj
      have hw1 := hrho.2 hz1
      rw [Str.snoc1_val_lt x w (Fin.castSucc j) j (by simp),
        Str.snoc1_val_ge x w (Fin.last l) (by simp)] at hw1
      exact (hj.symm.trans hw1).symm
    · rw [Set.mem_singleton_iff] at hw
      rw [hw]
      rfl
  rw [hsing] at hdom
  rw [IsDominant, Set.ncard_singleton] at hdom
  exact absurd hdom (by push_neg; exact_mod_cast hn)

/-! ### Items (A) and (B) of the proof of Theorem 8.2.1 -/

variable [Fintype Ω] [DecidableEq Ω]

/-- Item (A) of the proof of Theorem 8.2.1.  *"we have a (unique) dominant vertex-color
class `C(x⃗)` in `X_x⃗` (so `|C(x⃗)| > αn`) (otherwise we succeed on line 05)"*. -/
def AllDominant (α : ℝ) (X : KAryPartStruct Ω C k) : Prop :=
  ∀ (l : ℕ) (hl : l < k) (x : Str Ω l), Str.Distinct x →
    HasDominantClass α (X.restrTo hl.le x)

/-- Item (B) of the proof of Theorem 8.2.1.  *"if `ℓ(x⃗) ≤ k-2` then the `2`-skeleton
`X_x⃗^{(2)}` induces a clique configuration on `C(x⃗)` (otherwise we succeed on
line 08)"*. -/
def AllClique (α : ℝ) (X : KAryPartStruct Ω C k) : Prop :=
  ∀ (l : ℕ) (hl : l < k) (x : Str Ω l), Str.Distinct x → ∀ h2 : l + 2 ≤ k,
    ((X.restrTo hl.le x).skel2 (by omega)).IsCliqueOn
      (dominantClass α (X.restrTo hl.le x))

/-! ### Claims 8.4.1 and 8.4.2 -/

set_option maxHeartbeats 1000000 in
/-- Claim 8.4.1, Eq. (48).  *"Let `x⃗ ∈ Ω^{⟨≤k-1⟩}` be a non-empty string with parent `y⃗`,
so `x⃗ = y⃗z` for some `z ∈ Ω`.  Then `C(x⃗) = C(y⃗) \ {z}`."*

Paper's proof: *"We have `ℓ(y⃗) = ℓ(x⃗) - 1 ≤ k-2`.  Therefore, by item (B) above, `C(y⃗)`
induces a clique in the `2`-skeleton `X_y⃗^{(2)}`.  We have `|C(y⃗)| > αn ≥ n/2`, so by the
'Large clique lemma' (Lemma 3.4.25), `C(y⃗)` is a twin equivalence class in `X_y⃗^{(2)}`.
In particular, for all `u ∈ C(y⃗) \ {z}`, the color `c_y⃗(zu)` is the same (independent of
`u`); call this color `i_z`.  So for all `u ∈ C(y⃗) \ {z}`, we have
`c_x⃗(u) = c_y⃗(zu) = i_z`, independent [of] `u`.  It follows that `i_z` is the dominant
vertex-color in `X_x⃗` and Eq. (48) holds."*

The last step uses Eq. (47): `C(x⃗)` is contained in `C(y⃗)` and misses `supp(x⃗) ∋ z`, so
`C(x⃗) ⊆ C(y⃗) \ {z}`; since `C(y⃗) \ {z}` lies in the single vertex-color class `i_z` of
`X_x⃗` and `C(x⃗)` is a non-empty vertex-color class of `X_x⃗`, the two coincide. -/
theorem claim_8_4_1 {α : ℝ} (hα : 1 / 2 ≤ α) (X : KAryPartStruct Ω C k)
    (h : X.IsCoherent) (hn : (1 : ℝ) ≤ α * (Fintype.card Ω : ℝ))
    (hA : AllDominant α X) (hB : AllClique α X) (hl1 : l + 1 < k) {y : Str Ω l} {z : Ω}
    (hxd : Str.Distinct (Str.snoc1 y z)) :
    dominantClass α (X.restrTo hl1.le (Str.snoc1 y z))
      = dominantClass α (X.restrTo (by omega : l ≤ k) y) \ {z} := by
  classical
  have hly : l < k := by omega
  have hyd : Str.Distinct y := by
    intro s t hst
    have h1 : Str.snoc1 y z (Fin.castSucc s) = Str.snoc1 y z (Fin.castSucc t) := by
      rw [Str.snoc1_val_lt y z (Fin.castSucc s) s (by simp),
        Str.snoc1_val_lt y z (Fin.castSucc t) t (by simp)]
      exact hst
    have h2 := hxd h1
    exact Fin.ext (by simpa using congrArg Fin.val h2)
  set Y := X.restrTo hly.le y with hY
  have hYc : Y.IsCoherent := X.restrTo_isCoherent h hly.le y
  obtain ⟨i₁, hi₁⟩ := hA l hly y hyd
  have hDeq : dominantClass α Y = Y.vclass i₁ := dominantClass_eq hα Y hi₁
  set D := Y.vclass i₁ with hD
  have hDdom : IsDominant α D := hi₁
  -- `D` is large
  have hDpos : 0 < D.ncard := by
    have : (0 : ℝ) < (D.ncard : ℝ) := lt_of_le_of_lt (by positivity) hDdom
    exact_mod_cast this
  have hDbig : Fintype.card Ω < 2 * D.ncard := by
    have h2 : (1 / 2 : ℝ) * (Fintype.card Ω : ℝ) ≤ α * (Fintype.card Ω : ℝ) :=
      mul_le_mul_of_nonneg_right hα (by positivity)
    have h3 : α * (Fintype.card Ω : ℝ) < (D.ncard : ℝ) := hDdom
    have : (Fintype.card Ω : ℝ) < 2 * (D.ncard : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨w₀, hw₀⟩ : D.Nonempty := (Set.ncard_pos (Set.toFinite _)).1 hDpos
  -- the `2`-skeleton of `Y`, a classical coherent configuration
  have hm2 : 2 ≤ k - l := by omega
  set S := Y.skel2 hm2 with hS
  have hSc : S.IsCoherent := Y.skel2_isCoherent hYc hm2
  set i₀ := S.vcolor w₀ with hi₀
  have hSD : S.vertexClass i₀ = D := by
    ext v
    constructor
    · intro hv
      have : Y.vcolor v = Y.vcolor w₀ := (Y.skel2_vcolor_eq_iff hm2 v w₀).1 hv
      show Y.vcolor v = i₁
      rw [this]
      exact hw₀
    · intro hv
      have hvw : Y.vcolor v = Y.vcolor w₀ := (show Y.vcolor v = i₁ from hv).trans hw₀.symm
      exact (Y.skel2_vcolor_eq_iff hm2 v w₀).2 hvw
  have hmax : ∀ i : Fin S.rank, i ≠ i₀ →
      (S.vertexClass i).ncard < (S.vertexClass i₀).ncard := by
    intro i hi
    have hdisj : Disjoint (S.vertexClass i) (S.vertexClass i₀) := by
      rw [Set.disjoint_left]
      rintro v hv hv'
      exact hi ((show S.vcolor v = i from hv).symm.trans (show S.vcolor v = i₀ from hv'))
    have hsum : (S.vertexClass i).ncard + (S.vertexClass i₀).ncard ≤ Fintype.card Ω := by
      rw [← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
      have := Set.ncard_le_ncard
        (Set.subset_univ (S.vertexClass i ∪ S.vertexClass i₀)) (Set.toFinite _)
      rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at this
    rw [hSD] at hsum ⊢
    omega
  have hclique : S.IsCliqueOn (S.vertexClass i₀) := by
    have := hB l hly y hyd (by omega)
    rw [hDeq, ← hSD] at this
    exact this
  have htwin : ∀ w ∈ D, twinClass S.Aut w = S.vertexClass i₀ := by
    intro w hw
    exact PartitionStructure.large_clique_twinClass S hSc i₀ hmax
      ((PartitionStructure.isCliqueOn_iff S (S.vertexClass i₀) _).1 hclique)
      (by rw [hSD]; exact hw)
  -- the color `c_y⃗(zu)` is the same for all `u ∈ D \ {z}`
  have hconst : ∀ u ∈ D, ∀ u' ∈ D, u ≠ z → u' ≠ z → S.color z u = S.color z u' := by
    intro u hu u' hu' huz hu'z
    by_cases huu : u = u'
    · rw [huu]
    · have hmem : u' ∈ twinClass S.Aut u := by rw [htwin u hu, hSD]; exact hu'
      rcases hmem with hc | ⟨-, hswap⟩
      · exact absurd hc huu
      · have haut := (PartitionStructure.mem_aut).1 hswap z u
        rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm huz) (Ne.symm hu'z),
          Equiv.swap_apply_left] at haut
        exact haut.symm
  -- transport to the vertex-coloring of `X_{y⃗z}`
  have hvcol : ∀ u ∈ D, ∀ u' ∈ D, u ≠ z → u' ≠ z →
      (X.restrTo hl1.le (Str.snoc1 y z)).vcolor u
        = (X.restrTo hl1.le (Str.snoc1 y z)).vcolor u' := by
    intro u hu u' hu' huz hu'z
    have h1 := hconst u hu u' hu' huz hu'z
    rw [hS, Y.skel2_color_eq_iff hm2] at h1
    rw [hY, restrTo_skeletonColor2 X hly.le (by omega) (by norm_num) hm2 (by omega) y z u,
      restrTo_skeletonColor2 X hly.le (by omega) (by norm_num) hm2 (by omega) y z u'] at h1
    rw [restrTo_vcolor X hl1 (Nat.succ_pos _), restrTo_vcolor X hl1 (Nat.succ_pos _),
      Str.snoc1_snoc1, Str.snoc1_snoc1]
    exact h1
  -- the dominant class of `X_{y⃗z}`
  obtain ⟨i₂, hi₂⟩ := hA (l + 1) hl1 (Str.snoc1 y z) hxd
  set Z := X.restrTo hl1.le (Str.snoc1 y z) with hZ
  have hCeq : dominantClass α Z = Z.vclass i₂ := dominantClass_eq hα Z hi₂
  have hCpos : 0 < (Z.vclass i₂).ncard := by
    have : (0 : ℝ) < ((Z.vclass i₂).ncard : ℝ) := lt_of_le_of_lt (by positivity) hi₂
    exact_mod_cast this
  obtain ⟨w₁, hw₁⟩ : (Z.vclass i₂).Nonempty := (Set.ncard_pos (Set.toFinite _)).1 hCpos
  -- `z ∉ C(x⃗)`
  have hzC : z ∉ Z.vclass i₂ := by
    have := notMem_dominantClass_of_mem_supp (α := α) X h.toIsConfiguration hl1
      (x := Str.snoc1 y z) (z := z) ⟨Fin.last l, Str.snoc1_val_ge y z (Fin.last l) (by simp)⟩ hn
    rw [hCeq] at this
    exact this
  -- `C(x⃗) ⊆ C(y⃗)`
  have hCD : Z.vclass i₂ ⊆ D := by
    have hsub : Z.vclass i₂ ⊆ Y.vclass (Y.vcolor w₁) := by
      intro w hw
      have hzz : Z.vcolor w = Z.vcolor w₁ :=
        (show Z.vcolor w = i₂ from hw).trans (show Z.vcolor w₁ = i₂ from hw₁).symm
      exact restrTo_vcolor_parent X h.toIsConfiguration hl1 y z hzz
    have hdom : IsDominant α (Y.vclass (Y.vcolor w₁)) := by
      refine lt_of_lt_of_le hi₂ ?_
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      exact_mod_cast this
    have : Y.vcolor w₁ = i₁ := IsDominant.subsingleton hα Y.vcolor hdom hDdom
    rw [this] at hsub
    exact hsub
  refine Set.Subset.antisymm (fun w hw => ?_) (fun w hw => ?_)
  · rw [hCeq] at hw
    exact ⟨by rw [hDeq]; exact hCD hw, fun hc => hzC (hc ▸ hw)⟩
  · obtain ⟨hwD, hwz⟩ := hw
    rw [hDeq] at hwD
    rw [Set.mem_singleton_iff] at hwz
    rw [hCeq]
    have hw₁D : w₁ ∈ D := hCD hw₁
    have hw₁z : w₁ ≠ z := fun hc => hzC (by rw [← hc]; exact hw₁)
    have := hvcol w hwD w₁ hw₁D hwz hw₁z
    show Z.vcolor w = i₂
    rw [this]
    exact hw₁

/-- Claim 8.4.2, Eq. (49).  *"For all `x⃗ ∈ Ω^{⟨≤k-1⟩}` we have `C(x⃗) = C \ supp(x⃗)`.
Proof.  By induction on `ℓ(x⃗)`.  True by definition for `ℓ(x⃗) = 0`.  Assume now
`ℓ(x⃗) ≥ 1`.  The inductive step is provided by Claim 8.4.1."* -/
theorem claim_8_4_2 {α : ℝ} (hα : 1 / 2 ≤ α) (X : KAryPartStruct Ω C k)
    (h : X.IsCoherent) (hn : (1 : ℝ) ≤ α * (Fintype.card Ω : ℝ))
    (hA : AllDominant α X) (hB : AllClique α X) :
    ∀ (l : ℕ) (hl : l < k) (x : Str Ω l), Str.Distinct x →
      dominantClass α (X.restrTo hl.le x) = dominantClass α X \ Str.supp x := by
  intro l
  induction l with
  | zero =>
    intro hl x hxd
    have hx : x = Str.empty := Str.empty_unique x
    subst hx
    have hsupp : Str.supp (Str.empty : Str Ω 0) = (∅ : Set Ω) := by
      ext w
      exact ⟨fun ⟨i, _⟩ => absurd i.2 (Nat.not_lt_zero _), fun hc => absurd hc (Set.notMem_empty w)⟩
    rw [hsupp, Set.diff_empty, restrTo_empty]
  | succ p ih =>
    intro hl x hxd
    have hp : p < k := by omega
    set y : Str Ω p := fun i => x (Fin.castSucc i) with hy
    set z : Ω := x (Fin.last p) with hz
    have hxeq : Str.snoc1 y z = x := by
      funext j
      have hj := j.isLt
      by_cases hjl : (j : ℕ) < p
      · have h1 : Str.snoc1 y z j = y ⟨(j : ℕ), hjl⟩ := Str.snoc1_val_lt y z j _ rfl
        have h2 : y ⟨(j : ℕ), hjl⟩ = x j :=
          congrArg x (Fin.ext (rfl : ((Fin.castSucc ⟨(j : ℕ), hjl⟩ : Fin (p + 1)) : ℕ)
            = (j : ℕ)))
        rw [h1, h2]
      · have h1 : Str.snoc1 y z j = z := Str.snoc1_val_ge y z j (by omega)
        have h2 : z = x j :=
          congrArg x (Fin.ext (by simp; omega : ((Fin.last p : Fin (p + 1)) : ℕ) = (j : ℕ)))
        rw [h1, h2]
    have hyd : Str.Distinct y := by
      intro s t hst
      have h1 : x (Fin.castSucc s) = x (Fin.castSucc t) := hst
      have h2 := hxd h1
      exact Fin.ext (by simpa using congrArg Fin.val h2)
    have hxd' : Str.Distinct (Str.snoc1 y z) := by rw [hxeq]; exact hxd
    have hstep := claim_8_4_1 hα X h hn hA hB hl hxd'
    rw [hxeq] at hstep
    rw [hstep, ih hp y hyd]
    have hsupp : Str.supp x = insert z (Str.supp y) := by
      rw [← hxeq, Str.supp_snoc1]
    rw [hsupp]
    ext w
    simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    tauto

/-! ### Theorem 8.2.1 -/

/-- Remark 8.2.2.  *"DO WE NEED THIS?  Observe that this result immediately proves
Theorem 8.2.1 for `k = 2`.  However, we shall not exclude the case `k = 2` from the
general proof below."*

The remark is bracketed by `****` in version 2.5 and refers to a result that the
surrounding text does not name; the proof of Thm 8.2.1 below does not use it and does not
exclude `k = 2`.  See the corrected paper. -/
theorem remark_8_2_2 : True := trivial

set_option maxHeartbeats 1000000 in
/-- Theorem 8.2.1.  *"Under the conditions of Theorem 8.1.5, Procedure 'Design Lemma'
terminates, achieving goal (i) or (ii) of Theorem 8.1.5."*

Paper's proof: *"After line 01 we assume that `X` is a `k`-ary coherent configuration.
Assume for a contradiction that the algorithm fails.  It follows that for all
`x⃗ ∈ Ω^{⟨≤k-1⟩}` (A) … and (B) …  But Claim 8.4.2 creates a contradiction between the
'Non-clique lemma' (Lemma 8.3.1) and our items (A) and (B) above.  Indeed, let
`x⃗ ∈ Ω^{⟨≤k-1⟩}` be a string of which the existence is guaranteed by Lemma 8.3.1.  Now
option (a) of Lemma 8.3.1 says `C \ supp(x⃗)` is not homogeneous under `c_x⃗`, but this is
contradicted by item (A), given Claim 8.4.2.  But then option (b) of Lemma 8.3.1
contradicts item (B), given Claim 8.4.2.  So no such `x⃗` can exist, a contradiction."* -/
theorem theorem_8_2_1 {α : ℝ} (hα : 1 / 2 ≤ α) (hα1 : α < 1) (X : KAryPartStruct Ω C k)
    (h : X.IsCoherent) (hk2 : 2 ≤ k) (hkn : 2 * k ≤ Fintype.card Ω)
    (hdef : (1 : ℝ) - α ≤ (defect X.Aut : ℝ)) : ∃ l, ReturnsAt α X l := by
  classical
  have hn : (1 : ℝ) ≤ α * (Fintype.card Ω : ℝ) := by
    have h4 : (4 : ℝ) ≤ (Fintype.card Ω : ℝ) := by
      have : (4 : ℕ) ≤ Fintype.card Ω := by omega
      exact_mod_cast this
    nlinarith
  by_contra hcon
  push_neg at hcon
  -- items (A) and (B)
  have hAB : ∀ (l : ℕ) (hl : l < k) (x : Str Ω l), Str.Distinct x →
      ¬ Returns α X hl.le x := by
    intro l hl x hxd hret
    exact hcon l ⟨hl, x, hret⟩
  have hA : AllDominant α X := by
    intro l hl x hxd
    rw [← not_noDominantColor_iff]
    intro hno
    exact hAB l hl x hxd ⟨hxd, Or.inl hno⟩
  have hB : AllClique α X := by
    intro l hl x hxd h2
    by_contra hnc
    exact hAB l hl x hxd ⟨hxd, Or.inr ⟨h2, hA l hl x hxd, hnc⟩⟩
  -- the dominant class `C = C(Λ)` of `X`
  have hA0 := hA 0 (by omega) Str.empty (fun s t _ => absurd s.2 (Nat.not_lt_zero _))
  rw [restrTo_empty] at hA0
  obtain ⟨i₀, hi₀⟩ := hA0
  -- Lemma 8.3.1
  obtain ⟨l, hl, x, hxd, hcase⟩ :=
    non_clique_lemma hα (le_of_lt hα1) X h hk2 hkn hdef hi₀
  have hCx : dominantClass α (X.restrTo hl.le x) = X.vclass i₀ \ Str.supp x := by
    rw [claim_8_4_2 hα X h hn hA hB l hl x hxd, dominantClass_eq hα X hi₀]
  obtain ⟨i₂, hi₂⟩ := hA l hl x hxd
  have hCx' : (X.restrTo hl.le x).vclass i₂ = X.vclass i₀ \ Str.supp x := by
    rw [← dominantClass_eq hα _ hi₂, hCx]
  rcases hcase with ⟨u, hu, v, hv, huv⟩ | ⟨h2, hnc⟩
  · -- option (a) contradicts item (A)
    rw [← hCx'] at hu hv
    exact huv ((show (X.restrTo hl.le x).vcolor u = i₂ from hu).trans
      (show (X.restrTo hl.le x).vcolor v = i₂ from hv).symm)
  · -- option (b) contradicts item (B)
    refine hnc ?_
    have := hB l hl x hxd h2
    rw [hCx] at this
    exact this

end KAryPartStruct

end Babai
