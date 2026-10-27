/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 5.2 (the functor `F3`) and Section 5.4.1 (`k`-ary WL refinement).
-/
import Workspace.Higher.Coherent
import Workspace.Refinement.WL

/-!
# §5.4.1 `k`-ary WL refinement, and the functor `F3`

§5.4.1: *"The refinement step is defined as follows.  Let `X = (Ω; R₁,…,R_r)` be a `k`-ary
configuration.  For `x⃗ = (x₁,…,x_k) ∈ Ω^k` we encode in the new color `c'(x⃗)` the
following information: the old color `c(x⃗)`, and for all `i₁,…,i_k ≤ r`, the number
`|{y ∈ Ω | (∀j ≤ k)(c(x⃗ʲ(y)) = i_j)}|`.  As before, these data form a list, naturally
ordered.  To each list we assign a new color; these colors are sorted lexicographically.
This gives a refined coloring that defines a new configuration `X'`.  We stop when we
reach a stable configuration (`X = X'`).  Observation 4.3.1 remains valid, as is the
canonicity of the stable configuration stated in Eq. (26)."*

§5.2, after Def. 5.2.2: *"There is a functor `F3`, computable in time `n^{O(k)}`, that
converts `k`-ary configurations into `k`-ary coherent configurations without changing
their underlying sets, such that `Iso(X, Y) = Iso(F3(X), F3(Y))` for all pairs `X, Y` of
`k`-ary configurations.  `F3` assigns to each configuration its unique coarsest refinement
that is a coherent configuration (with an appropriate assignment of colors)."*  The paper
then has `****** ADD DETAILS HERE ******`; the details are supplied here from §5.4.1,
which is where the paper constructs `F3`: `F3` is the `k`-ary WL refinement run to
stability.  See the corrected paper, §5.2 (`F3`).

## Numbering map

| Paper | Lean |
|---|---|
| §5.4.1, `c'`, one round | `Babai.KAryPartStruct.wlStep` |
| §5.4.1, "defines a new configuration `X'`" | `.wlStep_isConfiguration` |
| §5.4.1, "we stop when we reach a stable configuration" | `.IsWLStable`, `.wlStable` |
| §5.4.1, "Observation 4.3.1 remains valid" | `.isWLStable_iff_isCoherent` |
| §5.2, `F3` | `Babai.KAryPartStruct.F3`, `.F3_isCoherent`, `.iso_F3` |
| §5.4.1, "the canonicity … stated in Eq. (26)" | `.iso_wlStep`, `.iso_wlIter`, `.iso_F3` |
-/

namespace Babai

namespace Str

/-- The index identity behind `KAryPartStruct.wlStep_isConfiguration`: substituting a
vertex `z` in the `j`-th coordinate of `τ(x⃗)` is the *same* as applying a suitable index
transformation `σ ∈ 𝔐_k` to a substitution of `z` in a single coordinate `m` of `x⃗`, where
`m` and `σ` depend only on `τ` and `j`, not on `x⃗` or on `z`.

Two cases.  If `τ` is injective, take `m = τ(j)` and `σ = τ`: the `i`-th letter of
`σ(x⃗ ᵐ(z))` is `z` when `τ(i) = τ(j)`, i.e. when `i = j`, and `x_{τ(i)}` otherwise.  If `τ`
is not injective then, `[k]` being finite, it is not surjective, so some `m ∈ [k]` is
outside the image of `τ`; take that `m` and `σ = τ` with the value at `j` changed to `m`.
Then the `i`-th letter of `σ(x⃗ ᵐ(z))` for `i ≠ j` is `x_{τ(i)}` (as `τ(i) ≠ m`), and the
`j`-th letter is `z`. -/
theorem exists_subst_idx {Ω : Type*} {k : ℕ} (τ : Mon k) (j : Fin k) :
    ∃ (m : Fin k) (σ : Mon k), ∀ (x : Str Ω k) (z : Ω),
      Str.subst (Str.idx τ x) j z = Str.idx σ (Str.subst x m z) := by
  classical
  by_cases hinj : Function.Injective τ
  · refine ⟨τ j, τ, fun x z => ?_⟩
    funext i
    rcases eq_or_ne i j with rfl | hij
    · rw [Str.subst_same, Str.idx_apply, Str.subst_same]
    · rw [Str.subst_of_ne _ hij, Str.idx_apply, Str.idx_apply,
        Str.subst_of_ne _ (fun hc => hij (hinj hc))]
  · have hns : ¬ Function.Surjective τ := fun hs => hinj (Finite.injective_iff_surjective.2 hs)
    obtain ⟨m, hm⟩ : ∃ m : Fin k, ∀ i : Fin k, τ i ≠ m := by
      simp only [Function.Surjective, not_forall] at hns
      obtain ⟨m, hmn⟩ := hns
      exact ⟨m, fun i hc => hmn ⟨i, hc⟩⟩
    refine ⟨m, Function.update τ j m, fun x z => ?_⟩
    funext i
    rcases eq_or_ne i j with rfl | hij
    · rw [Str.subst_same, Str.idx_apply, Function.update_self, Str.subst_same]
    · rw [Str.subst_of_ne _ hij, Str.idx_apply, Str.idx_apply, Function.update_of_ne hij,
        Str.subst_of_ne _ (hm i)]

end Str

namespace KAryPartStruct

variable {Ω Ω' : Type*} {C C' : Type*} {k : ℕ}

/-! ### §5.4.1 The refinement round -/

/-- §5.4.1.  One round of `k`-ary WL refinement: *"we encode in the new color `c'(x⃗)` …
the old color `c(x⃗)`, and for all `i₁,…,i_k ≤ r`, the number
`|{y ∈ Ω | (∀j ≤ k)(c(x⃗ʲ(y)) = i_j)}|`."* -/
noncomputable def wlStep (X : KAryPartStruct Ω C k) :
    KAryPartStruct Ω (C × (Str C k → ℕ)) k :=
  ⟨fun x => (X.color x, fun i => {z : Ω | ∀ t : Fin k, X.color (Str.subst x t z) = i t}.ncard)⟩

@[simp] theorem wlStep_color (X : KAryPartStruct Ω C k) (x : Str Ω k) :
    X.wlStep.color x =
      (X.color x, fun i => {z : Ω | ∀ t : Fin k, X.color (Str.subst x t z) = i t}.ncard) :=
  rfl

theorem wlStep_color_eq_iff (X : KAryPartStruct Ω C k) (x y : Str Ω k) :
    X.wlStep.color x = X.wlStep.color y ↔ X.color x = X.color y ∧
      ∀ i : Str C k, {z : Ω | ∀ t : Fin k, X.color (Str.subst x t z) = i t}.ncard
        = {z : Ω | ∀ t : Fin k, X.color (Str.subst y t z) = i t}.ncard := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, fun i => congrFun (congrArg Prod.snd h) i⟩
  · rintro ⟨h1, h2⟩
    exact Prod.ext h1 (funext h2)

/-- §5.4.1.  The refined coloring refines the old one. -/
theorem wlStep_refines (X : KAryPartStruct Ω C k) {x y : Str Ω k}
    (h : X.wlStep.color x = X.wlStep.color y) : X.color x = X.color y :=
  congrArg Prod.fst h

/-- §5.4.1.  *"This gives a refined coloring that defines a new configuration `X'`."*

Axiom (i) of Def. 5.1.8 for `c'` holds because `c'` refines `c` and `ρ(x⃗)` is already
determined by `c(x⃗)`.  For axiom (ii), let `c'(x⃗) = c'(y⃗)` and `τ ∈ 𝔐_k`.  The first
component of `c'(τ(x⃗))` is `c(τ(x⃗))`, which equals `c(τ(y⃗))` by axiom (ii) for `c`.  For
the counting component, write `D_{x⃗}(z) = (c(x⃗ ᵗ(z)) | t ∈ [k])`; the hypothesis says that
the fibers of `D_{x⃗}` and of `D_{y⃗}` have equal sizes.  By `Str.exists_subst_idx` there
are, for each `j ∈ [k]`, an index `m_j` and a `σ_j ∈ 𝔐_k` depending only on `τ` and `j`
with `(τ(w⃗)) ʲ(z) = σ_j(w⃗ ^{m_j}(z))` for all `w⃗` and `z`; hence, by Remark 5.1.9,
`D_{τ(w⃗)}(z)_j = η(σ_j)(D_{w⃗}(z)_{m_j})`.  So `D_{τ(w⃗)} = F ∘ D_{w⃗}` for a map `F` of
color tuples that does not depend on `w⃗`, and the fibers of `F ∘ D_{x⃗}` and `F ∘ D_{y⃗}`
again have equal sizes (`Babai.ncard_fiber_comp_congr`).

The counting is by `Set.ncard`, so `Ω` is assumed finite here, as it is in the paper. -/
theorem wlStep_isConfiguration [Finite Ω] {X : KAryPartStruct Ω C k}
    (h : X.IsConfiguration) : X.wlStep.IsConfiguration where
  rho x y hxy := h.rho x y (X.wlStep_refines hxy)
  idx x y τ hxy := by
    classical
    obtain ⟨h1, h2⟩ := (X.wlStep_color_eq_iff x y).1 hxy
    refine (X.wlStep_color_eq_iff _ _).2 ⟨h.idx x y τ h1, fun i => ?_⟩
    -- the counting data around `τ(w⃗)` is a fixed function of the counting data around `w⃗`
    choose M S hMS using fun j : Fin k => Str.exists_subst_idx (Ω := Ω) τ j
    obtain ⟨F, hDF⟩ : ∃ F : Str C k → Str C k, ∀ (w : Str Ω k) (z : Ω),
        (fun t => X.color (Str.subst (Str.idx τ w) t z))
          = F (fun t => X.color (Str.subst w t z)) := by
      refine ⟨fun i' j => X.eta (S j) (i' (M j)), fun w z => ?_⟩
      funext j
      rw [hMS j w z, color_idx_eq_eta X h]
    have hfib : ∀ i' : Str C k,
        {z : Ω | (fun t => X.color (Str.subst x t z)) = i'}.ncard
          = {z : Ω | (fun t => X.color (Str.subst y t z)) = i'}.ncard := by
      intro i'
      have e1 : ∀ w : Str Ω k, {z : Ω | (fun t => X.color (Str.subst w t z)) = i'}
          = {z : Ω | ∀ t : Fin k, X.color (Str.subst w t z) = i' t} := by
        intro w; ext z; exact funext_iff
      rw [e1 x, e1 y]
      exact h2 i'
    have hset : ∀ w : Str Ω k,
        {z : Ω | ∀ t : Fin k, X.color (Str.subst (Str.idx τ w) t z) = i t}
          = {z : Ω | F (fun t => X.color (Str.subst w t z)) = i} := by
      intro w
      ext z
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, ← hDF w z]
      exact funext_iff.symm
    rw [hset x, hset y]
    exact ncard_fiber_comp_congr _ _ F hfib i

/-! ### Observation 4.3.1 for `k`-ary WL -/

/-- §5.4.1.  *"We stop when we reach a stable configuration (`X = X'`)."* -/
def IsWLStable (X : KAryPartStruct Ω C k) : Prop :=
  ∀ x y : Str Ω k, X.color x = X.color y → X.wlStep.color x = X.wlStep.color y

/-- Observation 4.3.1 for `k`-ary WL refinement (§5.4.1: "Observation 4.3.1 remains
valid"): a `k`-ary configuration is stable under `k`-ary WL refinement exactly if it is a
`k`-ary coherent configuration (Def. 5.2.2). -/
theorem isWLStable_iff_isCoherent {X : KAryPartStruct Ω C k} (h : X.IsConfiguration) :
    X.IsWLStable ↔ X.IsCoherent := by
  classical
  constructor
  · intro hst
    refine isCoherent_of_count_eq h (fun i x y hxy => ?_)
    exact ((X.wlStep_color_eq_iff x y).1 (hst x y hxy)).2 i
  · intro hcoh x y hxy
    refine (X.wlStep_color_eq_iff x y).2 ⟨hxy, fun i => ?_⟩
    rw [gamma_eq hcoh i (X.color x) x rfl, gamma_eq hcoh i (X.color x) y hxy.symm]

/-! ### The process -/

/-- Kernel-only dependence of the counting data of a round. -/
theorem wlStep_count_congr_mp {Ω : Type*} {D D' : Type*} {k : ℕ} {d : KAryPartStruct Ω D k}
    {e : KAryPartStruct Ω D' k}
    (hk : ∀ u v : Str Ω k, d.color u = d.color v ↔ e.color u = e.color v) {x y : Str Ω k}
    (h : ∀ i : Str D k, {z : Ω | ∀ t : Fin k, d.color (Str.subst x t z) = i t}.ncard
      = {z : Ω | ∀ t : Fin k, d.color (Str.subst y t z) = i t}.ncard) (i : Str D' k) :
    {z : Ω | ∀ t : Fin k, e.color (Str.subst x t z) = i t}.ncard
      = {z : Ω | ∀ t : Fin k, e.color (Str.subst y t z) = i t}.ncard := by
  classical
  by_cases h1 : ∃ z₀ : Ω, ∀ t : Fin k, e.color (Str.subst x t z₀) = i t
  · obtain ⟨z₀, hz⟩ := h1
    have hA : {z : Ω | ∀ t : Fin k, e.color (Str.subst x t z) = i t}
        = {z : Ω | ∀ t : Fin k, d.color (Str.subst x t z)
            = d.color (Str.subst x t z₀)} := by
      ext z
      exact ⟨fun hzz t => (hk _ _).2 ((hzz t).trans (hz t).symm),
        fun hzz t => ((hk _ _).1 (hzz t)).trans (hz t)⟩
    have hB : {z : Ω | ∀ t : Fin k, e.color (Str.subst y t z) = i t}
        = {z : Ω | ∀ t : Fin k, d.color (Str.subst y t z)
            = d.color (Str.subst x t z₀)} := by
      ext z
      exact ⟨fun hzz t => (hk _ _).2 ((hzz t).trans (hz t).symm),
        fun hzz t => ((hk _ _).1 (hzz t)).trans (hz t)⟩
    rw [hA, hB]
    exact h (fun t => d.color (Str.subst x t z₀))
  · by_cases h2 : ∃ z₀ : Ω, ∀ t : Fin k, e.color (Str.subst y t z₀) = i t
    · obtain ⟨z₀, hz⟩ := h2
      have hA : {z : Ω | ∀ t : Fin k, e.color (Str.subst x t z) = i t}
          = {z : Ω | ∀ t : Fin k, d.color (Str.subst x t z)
              = d.color (Str.subst y t z₀)} := by
        ext z
        exact ⟨fun hzz t => (hk _ _).2 ((hzz t).trans (hz t).symm),
          fun hzz t => ((hk _ _).1 (hzz t)).trans (hz t)⟩
      have hB : {z : Ω | ∀ t : Fin k, e.color (Str.subst y t z) = i t}
          = {z : Ω | ∀ t : Fin k, d.color (Str.subst y t z)
              = d.color (Str.subst y t z₀)} := by
        ext z
        exact ⟨fun hzz t => (hk _ _).2 ((hzz t).trans (hz t).symm),
          fun hzz t => ((hk _ _).1 (hzz t)).trans (hz t)⟩
      rw [hA, hB]
      exact h (fun t => d.color (Str.subst y t z₀))
    · push_neg at h1 h2
      have e1 : {z : Ω | ∀ t : Fin k, e.color (Str.subst x t z) = i t} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro z hz
        obtain ⟨t, ht⟩ := h1 z
        exact ht (hz t)
      have e2 : {z : Ω | ∀ t : Fin k, e.color (Str.subst y t z) = i t} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro z hz
        obtain ⟨t, ht⟩ := h2 z
        exact ht (hz t)
      rw [e1, e2]

/-- A round of `k`-ary WL refinement depends on the input only through its partition. -/
theorem wlStep_congr {Ω : Type*} {D D' : Type*} {k : ℕ} {d : KAryPartStruct Ω D k}
    {e : KAryPartStruct Ω D' k}
    (hk : ∀ u v : Str Ω k, d.color u = d.color v ↔ e.color u = e.color v) (x y : Str Ω k) :
    d.wlStep.color x = d.wlStep.color y ↔ e.wlStep.color x = e.wlStep.color y := by
  rw [wlStep_color_eq_iff, wlStep_color_eq_iff]
  exact and_congr (hk x y)
    ⟨fun h => fun i => wlStep_count_congr_mp hk h i,
      fun h => fun i => wlStep_count_congr_mp (fun u v => (hk u v).symm) h i⟩

/-- §5.4.1.  The color set after `n` rounds. -/
def wlColorType (C : Type) (k : ℕ) : ℕ → Type
  | 0 => C
  | n + 1 => wlColorType C k n × (Str (wlColorType C k n) k → ℕ)

/-- §5.4.1.  The `k`-ary WL refinement process. -/
noncomputable def wlIter {C : Type} (X : KAryPartStruct Ω C k) :
    ∀ n : ℕ, KAryPartStruct Ω (wlColorType C k n) k
  | 0 => X
  | n + 1 => (X.wlIter n).wlStep

@[simp] theorem wlIter_zero {C : Type} (X : KAryPartStruct Ω C k) : X.wlIter 0 = X := rfl

@[simp] theorem wlIter_succ {C : Type} (X : KAryPartStruct Ω C k) (n : ℕ) :
    X.wlIter (n + 1) = (X.wlIter n).wlStep := rfl

/-- §5.4.1.  Every stage of the process is a `k`-ary configuration. -/
theorem wlIter_isConfiguration [Finite Ω] {C : Type} (X : KAryPartStruct Ω C k)
    (h : X.IsConfiguration) : ∀ n : ℕ, (X.wlIter n).IsConfiguration
  | 0 => h
  | n + 1 => wlStep_isConfiguration (X.wlIter_isConfiguration h n)

theorem wlIter_refines_le {C : Type} (X : KAryPartStruct Ω C k) {m n : ℕ} (h : m ≤ n)
    {x y : Str Ω k} (hxy : (X.wlIter n).color x = (X.wlIter n).color y) :
    (X.wlIter m).color x = (X.wlIter m).color y := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := Nat.le_zero.1 h
    exact hxy
  | succ p ih =>
    rcases Nat.lt_or_ge m (p + 1) with hlt | hge
    · exact ih (by omega) ((X.wlIter p).wlStep_refines hxy)
    · obtain rfl : m = p + 1 := le_antisymm h hge
      exact hxy

/-- §5.4.1.  The output of the process: the rounds are run `|Ω^k × Ω^k|` times, a bound
valid for every input on the vertex set `Ω`, so the number of rounds does not depend on
the input and the process stays canonical. -/
noncomputable def wlStable {C : Type} [Fintype Ω] (X : KAryPartStruct Ω C k) :
    KAryPartStruct Ω (wlColorType C k (Fintype.card (Str Ω k × Str Ω k))) k :=
  X.wlIter (Fintype.card (Str Ω k × Str Ω k))

/-- §5.4.1.  The output of the process is stable. -/
theorem wlStable_isWLStable {C : Type} [Fintype Ω] (X : KAryPartStruct Ω C k) :
    X.wlStable.IsWLStable := by
  classical
  set S : ℕ → Set (Str Ω k × Str Ω k) :=
    fun n => kernelSet (X.wlIter n).color with hS
  have hmono : ∀ n, S (n + 1) ⊆ S n := by
    intro n p hp
    exact X.wlIter_refines_le (Nat.le_succ n) hp
  have hstep : ∀ n, S (n + 1) = S n → S (n + 2) = S (n + 1) := by
    intro n hn
    have hk : ∀ u v : Str Ω k, (X.wlIter n).color u = (X.wlIter n).color v
        ↔ (X.wlIter (n + 1)).color u = (X.wlIter (n + 1)).color v := by
      intro u v
      refine ⟨fun huv => ?_, fun huv => hmono n (show (u, v) ∈ S (n + 1) from huv)⟩
      have : (u, v) ∈ S (n + 1) := by rw [hn]; exact huv
      exact this
    ext p
    obtain ⟨u, v⟩ := p
    exact (wlStep_congr hk u v).symm
  have hfix := eq_of_antitone_sets S hmono hstep
  intro x y hxy
  have hmem : (x, y) ∈ S (Fintype.card (Str Ω k × Str Ω k) + 1) := by
    rw [hfix]; exact hxy
  exact hmem

/-- §5.2.  The functor `F3`: the `k`-ary WL refinement of `X` run to stability. -/
noncomputable def F3 {C : Type} [Fintype Ω] (X : KAryPartStruct Ω C k) :
    KAryPartStruct Ω (wlColorType C k (Fintype.card (Str Ω k × Str Ω k))) k :=
  X.wlStable

/-- §5.2.  *"`F3` … converts `k`-ary configurations into `k`-ary coherent
configurations without changing their underlying sets."* -/
theorem F3_isCoherent {C : Type} [Fintype Ω] (X : KAryPartStruct Ω C k)
    (h : X.IsConfiguration) : X.F3.IsCoherent :=
  (isWLStable_iff_isCoherent (X.wlIter_isConfiguration h _)).1 X.wlStable_isWLStable

/-- §5.2.  *"`F3` assigns to each configuration its unique coarsest refinement that is a
coherent configuration."*  Every coherent refinement of `X` refines `F3(X)`; together with
`F3_isCoherent` and the fact that `F3(X)` refines `X` (`wlIter_refines_le` at `m = 0`),
this is the quoted sentence.

Proof by induction on the round.  A coherent configuration is stable under `k`-ary WL
refinement (`isWLStable_iff_isCoherent`, i.e. axiom (iii) of Def. 5.2.2), and that is what
makes the induction step go through: if `Y` refines the `n`-th round then it also refines
the `(n+1)`-st.  Indeed the color of the `n`-th round is a function `G` of the color of
`Y` (this is the induction hypothesis), hence the tuple of colors `(c_n(u⃗ ᵗ(z)) | t ∈ [k])`
of the `n`-th round around `u⃗` is the image under `i⃗ ↦ G ∘ i⃗` of the corresponding tuple
for `Y`, and equal fiber sizes for the `Y`-tuples — which is axiom (iii) for `Y` — give
equal fiber sizes after that map (`Babai.ncard_fiber_comp_congr`). -/
theorem F3_coarsest {C : Type} [Fintype Ω] (X : KAryPartStruct Ω C k)
    (Y : KAryPartStruct Ω C' k) (hY : Y.IsCoherent)
    (href : ∀ u v : Str Ω k, Y.color u = Y.color v → X.color u = X.color v)
    {x y : Str Ω k} (h : Y.color x = Y.color y) : X.F3.color x = X.F3.color y := by
  classical
  have key : ∀ n : ℕ, ∀ u v : Str Ω k, Y.color u = Y.color v →
      (X.wlIter n).color u = (X.wlIter n).color v := by
    intro n
    induction n with
    | zero => exact href
    | succ n ih =>
      intro u v huv
      -- the color of the `n`-th round is a function `G` of the color of `Y`
      obtain ⟨G, hG⟩ : ∃ G : C' → wlColorType C k n,
          ∀ w : Str Ω k, G (Y.color w) = (X.wlIter n).color w := by
        refine ⟨fun c' => if hc : ∃ w : Str Ω k, Y.color w = c' then
          (X.wlIter n).color hc.choose else (X.wlIter n).color u, fun w => ?_⟩
        have hc : ∃ w' : Str Ω k, Y.color w' = Y.color w := ⟨w, rfl⟩
        show (if hc' : ∃ w' : Str Ω k, Y.color w' = Y.color w then
          (X.wlIter n).color hc'.choose else (X.wlIter n).color u) = (X.wlIter n).color w
        rw [dif_pos hc]
        exact ih _ _ hc.choose_spec
      refine ((X.wlIter n).wlStep_color_eq_iff u v).2 ⟨ih u v huv, fun i => ?_⟩
      have hset : ∀ w : Str Ω k,
          {z : Ω | ∀ t : Fin k, (X.wlIter n).color (Str.subst w t z) = i t}
            = {z : Ω | (fun t => G (Y.color (Str.subst w t z))) = i} := by
        intro w
        ext z
        rw [Set.mem_setOf_eq, Set.mem_setOf_eq, funext_iff]
        exact forall_congr' fun t => by rw [hG]
      rw [hset u, hset v]
      exact ncard_fiber_comp_congr _ _ (fun i' t => G (i' t))
        (fun i' => hY.ncard_colorVec_eq i' huv) i
  exact key (Fintype.card (Str Ω k × Str Ω k)) x y h

/-! ### Canonicity, Eq. (26) -/

/-- §5.4.1, Eq. (26).  One round of `k`-ary WL refinement is canonical. -/
theorem iso_wlStep (X : KAryPartStruct Ω C k) (Y : KAryPartStruct Ω' C k) :
    Iso X.wlStep Y.wlStep = Iso X Y := by
  classical
  ext f
  constructor
  · intro h x
    exact congrArg Prod.fst (h x)
  · intro h x
    refine Prod.ext (h x) ?_
    funext i
    have himg : ∀ (w : Str Ω k),
        {z' : Ω' | ∀ t : Fin k, Y.color (Str.subst (Babai.tupleMap f w) t z') = i t}
          = f '' {z : Ω | ∀ t : Fin k, X.color (Str.subst w t z) = i t} := by
      intro w
      ext z'
      constructor
      · intro hz
        refine ⟨f.symm z', fun t => ?_, f.apply_symm_apply z'⟩
        have ht := hz t
        rw [← f.apply_symm_apply z', ← Str.subst_tupleMap,
          h (Str.subst w t (f.symm z'))] at ht
        exact ht
      · rintro ⟨z, hz, rfl⟩
        intro t
        rw [← Str.subst_tupleMap, h (Str.subst w t z)]
        exact hz t
    show {z' : Ω' | ∀ t : Fin k, Y.color (Str.subst (Babai.tupleMap f x) t z') = i t}.ncard = _
    rw [himg x, Set.ncard_image_of_injective _ f.injective]
    rfl

/-- §5.4.1, Eq. (26).  Every round of the process is canonical. -/
theorem iso_wlIter {C : Type} (X : KAryPartStruct Ω C k) (Y : KAryPartStruct Ω' C k) :
    ∀ n : ℕ, Iso (X.wlIter n) (Y.wlIter n) = Iso X Y
  | 0 => rfl
  | n + 1 => (iso_wlStep (X.wlIter n) (Y.wlIter n)).trans (iso_wlIter X Y n)

/-- §5.2, §5.4.1, Eq. (26).  `Iso(X, Y) = Iso(F3(X), F3(Y))`.  ("Simultaneously executing
the rounds" is the same number of rounds on both sides, which here follows from
`|Ω| = |Ω'|`.) -/
theorem iso_F3 {C : Type} [Fintype Ω] [Fintype Ω'] (X : KAryPartStruct Ω C k)
    (Y : KAryPartStruct Ω' C k) :
    Iso X.F3 (Y.wlIter (Fintype.card (Str Ω k × Str Ω k))) = Iso X Y :=
  iso_wlIter X Y _

end KAryPartStruct

end Babai
