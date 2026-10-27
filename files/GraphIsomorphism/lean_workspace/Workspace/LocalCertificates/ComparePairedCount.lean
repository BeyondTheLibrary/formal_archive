/-
Section 13.1 of Babai, version 2.5: the printed call bound `t!·n²` of Proposition 13.1.11.
-/
import Workspace.LocalCertificates.ComparePaired
import Workspace.Prelim.AlternatingIndex

/-!
# Proposition 13.1.11 with the printed constant

Procedure "Recompute `H(W)` and `Q`" makes, in each round of the while loop, at most `t!`
calls per kernel orbit for the automorphisms (line 04e1) and as many for the comparisons
(line 04e2), so at most `2·t!·n` calls per round. The printed bound `t!·n²` follows because
there are at most `n/t` rounds, not only `n`: while the loop runs, `H(W)^T ≥ A(T)`, and the
window gains a whole `H(W)`-orbit of an affected point. Such an orbit has length at least
`t`, since the image of its stabilizer on `T` does not contain `A(T)` and so has index at least
`t` (`Babai.card_le_relIndex_of_not_alternating_le`, the fact the paper uses for
Cor. 10.3.7). Hence `rounds · t ≤ n`, and `rounds · 2·t!·n ≤ 2·(t−1)!·n² ≤ t!·n²`.
-/

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise Classical

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Equiv.Perm Ω)} {ϕ : G →* Equiv.Perm Γ}
  {x : Ω → Λ} {T : Set Γ}

namespace Stage

/-- An affected point has an orbit of length at least `t` under the current group, while
`H(W)^T ≥ A(T)`. -/
theorem card_le_ncard_orbit_of_affected (s : Stage ϕ x T) (h5 : 5 ≤ T.ncard)
    (hgiant : alternatingGroup T ≤ imgOn ϕ T s.le) {u : Ω} (hu : u ∈ s.aff) :
    T.ncard ≤ (orbit s.H u).ncard := by
  set ψ := psiOn ϕ T s.le
  set S := stabilizer s.H u
  have hT : Fintype.card ↥T = T.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hK : alternatingGroup T ≤ ψ.range := by
    rw [← imgOn_eq_range]; exact hgiant
  have hSK : S.map ψ ≤ ψ.range := by
    rw [MonoidHom.range_eq_map]; exact Subgroup.map_mono le_top
  have h1 := card_le_relIndex_of_not_alternating_le (by rw [hT]; exact h5) hK hSK hu
  have h2 : (S.map ψ).relIndex ψ.range ≤ S.index := by
    rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq,
      Subgroup.relIndex_top_right]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le le_sup_left)
  rw [← index_stabilizer]
  have h3 := h1.trans h2
  rw [hT] at h3
  exact h3

/-- While the loop runs, the window grows by at least `t` points. -/
theorem ncard_add_le_ncard_step (s : Stage ϕ x T) (h5 : 5 ≤ T.ncard) (h : s.LoopCond) :
    s.W.ncard + T.ncard ≤ s.step.W.ncard := by
  obtain ⟨u, hu, huW⟩ := Set.not_subset.1 h.2
  have hO : (orbit s.H u) ⊆ s.aff := by
    rintro v ⟨g, rfl⟩
    exact ((isInvariant_iff_mem _ _).1 s.isInvariant_aff (g : Equiv.Perm Ω) g.2 u).1 hu
  have hdisj : Disjoint s.W (orbit s.H u) := by
    rw [Set.disjoint_left]
    rintro v hvW ⟨g, rfl⟩
    apply huW
    have := ((isInvariant_iff_mem _ _).1 s.inv (g⁻¹ : s.H) (g⁻¹ : s.H).2 (g • u)).1 hvW
    simpa [Subgroup.smul_def] using this
  have hsub : s.W ∪ orbit s.H u ⊆ s.step.W := by
    rw [step_W]; exact Set.union_subset s.sub_aff hO
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)] at hcard
  have := s.card_le_ncard_orbit_of_affected h5 h.1 hu
  omega

end Stage

/-- The window after `i` rounds of the running loop has at least `i·t` points. -/
theorem mul_le_ncard_stages_W (h5 : 5 ≤ T.ncard) (i : ℕ)
    (h : ∀ j < i, (stages ϕ x T j).LoopCond) : i * T.ncard ≤ (stages ϕ x T i).W.ncard := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hi := ih fun j hj => h j (by omega)
    have := (stages ϕ x T i).ncard_add_le_ncard_step h5 (h i (by omega))
    rw [stages_succ, Nat.succ_mul]
    omega

/-- "The while loop is executed at most `n` times", sharpened: at most `n/t` times. -/
theorem haltIndex_mul_le_card (h5 : 5 ≤ T.ncard) :
    haltIndex ϕ x T * T.ncard ≤ Nat.card Ω := by
  have h := mul_le_ncard_stages_W (ϕ := ϕ) (x := x) h5 (haltIndex ϕ x T)
    fun j hj => loopCond_of_lt_haltIndex ϕ x T hj
  have hle : (stages ϕ x T (haltIndex ϕ x T)).W.ncard ≤ Nat.card Ω := by
    have := Set.ncard_le_ncard (Set.subset_univ (stages ϕ x T (haltIndex ϕ x T)).W)
      (Set.toFinite _)
    rwa [Set.ncard_univ] at this
  omega

/-- `r·t ≤ n` and `2 ≤ t` give `r · (2·(t!·n)) ≤ t!·n²`. -/
theorem rounds_calls_le {r t n : ℕ} (h : r * t ≤ n) (ht : 2 ≤ t) :
    r * (2 * (Nat.factorial t * n)) ≤ Nat.factorial t * n ^ 2 := by
  obtain ⟨p, rfl⟩ : ∃ p, t = p + 1 := ⟨t - 1, by omega⟩
  rw [Nat.factorial_succ]
  have hp : 2 ≤ p + 1 := ht
  have key : r * (p + 1) * (2 * Nat.factorial p * n) ≤ n * ((p + 1) * Nat.factorial p * n) := by
    have := Nat.mul_le_mul_right (2 * Nat.factorial p * n) h
    refine this.trans ?_
    have : 2 * Nat.factorial p * n ≤ (p + 1) * Nat.factorial p * n :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hp)
    exact Nat.mul_le_mul_left _ this
  calc r * (2 * ((p + 1) * Nat.factorial p * n))
      = r * (p + 1) * (2 * Nat.factorial p * n) := by ring
    _ ≤ n * ((p + 1) * Nat.factorial p * n) := key
    _ = (p + 1) * Nat.factorial p * n ^ 2 := by ring

/-- **Proposition 13.1.11**, §13.1, with the printed constant: the paired comparison
reduction with a chosen initial transporter makes at most `t!·n²` calls, each on a window of
size at most `n/t`. -/
theorem proposition_13_1_11_paired_calls_sharp (y : Ω → Λ) (h5 : 5 ≤ T.ncard)
    (σ₀ : Equiv.Perm Ω) :
    (pairedComparisonReduction ϕ x T y σ₀).calls.length ≤
        Nat.factorial T.ncard * (Nat.card Ω) ^ 2 ∧
      ∀ I ∈ (pairedComparisonReduction ϕ x T y σ₀).calls,
        T.ncard * I.Δ.ncard ≤ Nat.card Ω := by
  have hc : (pairedComparisonReduction ϕ x T y σ₀).calls =
      (pairedLoopReduction ϕ x T y σ₀ (haltIndex ϕ x T)).calls := by
    simp [pairedComparisonReduction]
  refine ⟨?_, (proposition_13_1_11_paired_calls y h5 σ₀).2⟩
  rw [hc]
  exact (length_calls_pairedLoopReduction y σ₀ _).trans
    (rounds_calls_le (haltIndex_mul_le_card h5) (by omega))

/-- **Proposition 13.1.11**, §13.1: the comparison reduction computes
`Iso_G(x^{W(T)}_T, (x')^{W(T')}_{T'})` with at most `t!·n²` calls to String Isomorphism on
windows of size at most `n/t`, as printed. -/
theorem proposition_13_1_11_reduction_sharp (y : Ω → Λ) (T' : Set Γ)
    (hset : LocalCertSetting G ϕ) (ht : LargeK T.ncard (Nat.card Ω))
    (htm : 10 * T.ncard ≤ Nat.card Γ) (hT' : T'.ncard = T.ncard) [Nonempty Ω] :
    (compareReduction ϕ x T y T').run = compareIso ϕ x y T T' ∧
      (compareReduction ϕ x T y T').calls.length ≤
        Nat.factorial T.ncard * (Nat.card Ω) ^ 2 ∧
      ∀ I ∈ (compareReduction ϕ x T y T').calls,
        T.ncard * I.Δ.ncard ≤ Nat.card Ω := by
  refine ⟨run_compareReduction y T' hset ht htm hT', ?_⟩
  have h5 : 5 ≤ T.ncard := by have := ht.eight_lt; omega
  unfold compareReduction
  split
  · exact proposition_13_1_11_paired_calls_sharp y h5 _
  · simp

end Babai
