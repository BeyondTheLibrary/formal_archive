import Workspace.Algo.AggregateTable
import Workspace.Algo.WFTests

/-! # Explicit individualizations for Section 9.4

A numbering is a permutation of the positions of the supplied domain list.
Enumerate tuples and keep those without repetitions. The original domain
supplies the arity guard, so a logarithmic second part can be individualized
in quasipolynomial time as prescribed in Section 9.4, step 2.
-/

namespace Algo
open RAM RAM.Targets

/-- Original-domain witness and the domain to be individualized. -/
def sbipNumberings (c : ℕ) (p : List ℕ × List ℕ) : List RawPerm :=
  ((aggTable c (p.2, p.1, List.range p.2.length)).2.map Prod.fst).filter wftNodup

theorem quasiFun_sbipNumberings (c : ℕ) : QuasiFun (sbipNumberings c) :=
  (((polyFun_snd.pair (polyFun_fst.pair (polyFun_snd.comp polyFun_rangeLength))).comp_quasiFun
    (aggQuasiFun_table c)).comp_poly
      (polyFun_snd.comp (PolyFun.map polyFun_fst))).comp_poly (PolyFun.filter wftPolyFun_nodup)

theorem mem_sbipNumberings {c : ℕ} {base dom row : List ℕ}
    (hg : dom.length ≤ guardBound c base.length) :
    row ∈ sbipNumberings c (base, dom) ↔ RawPerm.WF dom.length row := by
  rw [sbipNumberings, aggTable_of_guard (a := (dom, base, List.range dom.length)) hg,
    keys_tupleTable, List.mem_filter, mem_tuplesOf, wftNodup_eq_true_iff]
  simp only [List.mem_range, RawPerm.WF, and_assoc]

theorem sbipNumberings_complete {c : ℕ} {base dom : List ℕ}
    (hg : dom.length ≤ guardBound c base.length) (σ : Equiv.Perm (Fin dom.length)) :
    encPerm dom.length σ ∈ sbipNumberings c (base, dom) :=
  (mem_sbipNumberings hg).2 (wf_encPerm _ σ)

theorem sbipNumberings_nonempty {c : ℕ} {base dom : List ℕ}
    (hg : dom.length ≤ guardBound c base.length) : ∃ row, row ∈ sbipNumberings c (base, dom) :=
  ⟨_, sbipNumberings_complete hg 1⟩

/-- Every injective numbering by the domain positions occurs in the family. -/
theorem sbipNumberings_realizes {c : ℕ} {base dom : List ℕ} {A : Type*}
    (e : A ≃ Fin dom.length) (σ : A → ℕ) (hσ : Function.Injective σ)
    (hlt : ∀ a, σ a < dom.length) (hg : dom.length ≤ guardBound c base.length) :
    ∃ row ∈ sbipNumberings c (base, dom),
      ∀ a, (decPerm dom.length row (e a)).val = σ a := by
  let f : Fin dom.length → Fin dom.length := fun i => ⟨σ (e.symm i), hlt _⟩
  have hf : Function.Injective f := fun i j hij =>
    e.symm.injective (hσ (congrArg Fin.val hij))
  let p : Equiv.Perm (Fin dom.length) :=
    Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  refine ⟨encPerm dom.length p, sbipNumberings_complete hg p, ?_⟩
  intro a
  simp [p, f]

/-- The tuple enumeration gives the `n₂^n₂` bound used by `step_9_4_2`. -/
theorem length_sbipNumberings_le {c : ℕ} {base dom : List ℕ}
    (hg : dom.length ≤ guardBound c base.length) :
    (sbipNumberings c (base, dom)).length ≤ dom.length ^ dom.length := by
  rw [sbipNumberings, aggTable_of_guard (a := (dom, base, List.range dom.length)) hg,
    keys_tupleTable]
  simpa only [length_tuplesOf, List.length_range] using
    List.length_filter_le wftNodup (tuplesOf (List.range dom.length) dom.length)

/-- Every fixed-size step-1 domain satisfies an arity guard with a fixed exponent. -/
theorem sbip_small_guard {n C : ℕ} (hn : n ≤ C) : n ≤ guardBound C n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact Nat.zero_le _
  by_cases hn1 : n = 1
  · subst n
    simp [guardBound]
  have hlog : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by omega)
  calc n ≤ 2 ^ n := Nat.le_of_lt (Nat.lt_two_pow_self)
    _ ≤ 2 ^ C := Nat.pow_le_pow_right (by norm_num) hn
    _ ≤ guardBound C n := Nat.pow_le_pow_left (by omega) C

/-- The explicit linear-logarithmic test in step 2 implies a fixed-power guard. -/
theorem sbip_log_guard {m n C : ℕ} (hm : m ≤ C * Nat.log 2 n) :
    m ≤ guardBound (C + 1) n := by
  by_cases hz : Nat.log 2 n = 0
  · simp only [hz, Nat.mul_zero] at hm
    exact hm.trans (Nat.zero_le _)
  have hC : C ≤ (Nat.log 2 n + 1) ^ C :=
    (Nat.le_of_lt Nat.lt_two_pow_self).trans (Nat.pow_le_pow_left (by omega) C)
  calc m ≤ C * Nat.log 2 n := hm
    _ ≤ (Nat.log 2 n + 1) ^ C * (Nat.log 2 n + 1) :=
      Nat.mul_le_mul hC (Nat.le_succ _)
    _ = guardBound (C + 1) n := by rw [guardBound, pow_succ]

end Algo

#print axioms Algo.quasiFun_sbipNumberings
#print axioms Algo.mem_sbipNumberings
