/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): bounds at an external degree,
and the guarded tuple table. Not part of the faithful formalization.
-/
import Workspace.Explicit.NodeTN
import Workspace.Algo.AggregateTable
import Workspace.Algo.WLVertex

/-!
# Bounds at an external degree

`Explicit.TN.Bounded c Pre k`: `c n a ≤ 2^{A (log₂ n + 2)^k}·(size a + 1)^b` for constants `A`,
`b`. The closure rules (sums, products, constants, the size, powers of the logarithm), and
`Explicit.TN.aggTable`: the guarded tuple table of `Algo.aggTable` (Sec. 5.4.2) is bounded at
the degree with exponent `c + 1`, when the ambient domain and the tuple domain have at most `n`
elements. The cost is quasipolynomial in `n` and polynomial in the size of the input: this is
the two-scale form of `Algo.aggQuasiFun_table`.
-/

namespace Explicit

open RAM Algo

variable {α β γ σ : Type*}

namespace TN

namespace Bounded

variable [Enc α] {Pre : ℕ → α → Prop} {k : ℕ}

theorem mono {c c' : ℕ → α → ℕ} (h : Bounded c Pre k) (hc : ∀ n a, Pre n a → c' n a ≤ c n a) :
    Bounded c' Pre k := by
  obtain ⟨A, b, h⟩ := h
  exact ⟨A, b, fun n a ha => (hc n a ha).trans (h n a ha)⟩

theorem restrict {c : ℕ → α → ℕ} {Pre' : ℕ → α → Prop} (h : Bounded c Pre k)
    (hP : ∀ n a, Pre' n a → Pre n a) : Bounded c Pre' k := by
  obtain ⟨A, b, h⟩ := h
  exact ⟨A, b, fun n a ha => h n a (hP n a ha)⟩

theorem mono_k {c : ℕ → α → ℕ} {k' : ℕ} (h : Bounded c Pre k) (hk : k ≤ k') :
    Bounded c Pre k' := by
  obtain ⟨A, b, h⟩ := h
  exact ⟨A, b, fun n a ha => (h n a ha).trans (tsB_mono le_rfl hk le_rfl le_rfl le_rfl)⟩

theorem const (m : ℕ) : Bounded (fun _ _ => m) Pre k :=
  ⟨m, 0, fun n a _ => const_le_tsB m k n _⟩

theorem size : Bounded (fun _ a => Enc.size a) Pre k :=
  ⟨0, 1, fun n a _ => self_le_tsB k n _⟩

theorem add {c c' : ℕ → α → ℕ} (h : Bounded c Pre k) (h' : Bounded c' Pre k) :
    Bounded (fun n a => c n a + c' n a) Pre k := by
  obtain ⟨A, b, h⟩ := h
  obtain ⟨A', b', h'⟩ := h'
  exact ⟨A + A' + 2, b + b', fun n a ha =>
    (Nat.add_le_add (h n a ha) (h' n a ha)).trans (tsB_add_le _ _ _ _ _ _ _)⟩

theorem mul {c c' : ℕ → α → ℕ} (h : Bounded c Pre k) (h' : Bounded c' Pre k) :
    Bounded (fun n a => c n a * c' n a) Pre k := by
  obtain ⟨A, b, h⟩ := h
  obtain ⟨A', b', h'⟩ := h'
  exact ⟨A + A', b + b', fun n a ha =>
    (Nat.mul_le_mul (h n a ha) (h' n a ha)).trans (tsB_mul _ _ _ _ _ _ _).le⟩

/-- `2^{m (log₂ n + 2)^c}` for `c ≤ k`. -/
theorem two_pow_lg (m c : ℕ) (hc : c ≤ k) : Bounded (fun n _ => 2 ^ (m * lg n ^ c)) Pre k :=
  ⟨m, 0, fun n a _ => by
    unfold tsB
    simp only [pow_zero, mul_one]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _
      (lg_pow_mono le_rfl hc))⟩

/-- `(log₂ n + 2)^c` for `c ≤ k`. -/
theorem lg_pow (c : ℕ) (hc : c ≤ k) : Bounded (fun n _ => lg n ^ c) Pre k :=
  (two_pow_lg 1 c hc).mono fun n _ _ => by
    rw [one_mul]; exact Nat.lt_two_pow_self.le

/-- The degree itself, for `1 ≤ k`. -/
theorem deg (hk : 1 ≤ k) : Bounded (fun n _ => n) Pre k :=
  (two_pow_lg 1 1 hk).mono fun n _ _ => by
    rw [one_mul, pow_one]
    unfold lg
    exact (le_two_pow_log n).trans (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- `m^j ≤ 2^{(log₂ n + 2)^{c+1}}` when `m ≤ n` and `j ≤ (log₂ n + 1)^c`. -/
theorem pow_le {m j : ℕ → α → ℕ} (c : ℕ) (hck : c + 1 ≤ k)
    (hm : ∀ n a, Pre n a → m n a ≤ n)
    (hj : ∀ n a, Pre n a → j n a ≤ (Nat.log 2 n + 1) ^ c) :
    Bounded (fun n a => m n a ^ j n a) Pre k :=
  (two_pow_lg 1 (c + 1) hck).restrict (fun _ _ h => h) |>.mono fun n a ha => by
    rw [one_mul]
    exact pow_le_quasi (hm n a ha) (hj n a ha)

end Bounded

/-- **A routine with a bounded time and a bounded answer.** -/
theorem of_bounds [Enc α] [Enc β] {f : α → β} {Pre : ℕ → α → Prop} {k : ℕ} {P : Program}
    {T : ℕ → α → ℕ} (hw : Wf P)
    (hP : ∀ n a, Pre n a → RunsTo P (fun m => m = initMemAt 16 (Enc.encode a))
      (fun m' => m' = initMemAt 16 (Enc.encode (f a))) (T n a))
    (hT : Bounded T Pre k) (hs : Bounded (fun _ a => Enc.size (f a)) Pre k) : TN f Pre k := by
  obtain ⟨A, b, hT⟩ := hT
  obtain ⟨A', b', hs⟩ := hs
  exact ⟨A + A', b + b', ⟨P, hw, fun n a ha => (hP n a ha).mono ((hT n a ha).trans
      (tsB_mono (by omega) le_rfl (by omega) le_rfl le_rfl))⟩,
    fun n a ha => (hs n a ha).trans (tsB_mono (by omega) le_rfl (by omega) le_rfl le_rfl)⟩

/-- The size of the answer of a routine bounded at the degree is bounded at the degree. -/
theorem size_bounded [Enc α] [Enc β] {f : α → β} {Pre : ℕ → α → Prop} {k : ℕ}
    (h : TN f Pre k) : Bounded (fun _ a => Enc.size (f a)) Pre k := by
  obtain ⟨A, b, -, hs⟩ := h
  exact ⟨A, b, hs⟩

/-! ## The guarded tuple table -/

/-- The precondition of the tuple table at degree `n`: the ambient domain has at most `n`
elements, and so has the tuple domain when the arity passes the guard. -/
def AggTablePre (c n : ℕ) (a : RawAggTestInput) : Prop :=
  a.2.1.length ≤ n ∧ (a.1.length ≤ guardBound c a.2.1.length → a.2.2.length ≤ n)

/-- Every state of the tuple table, at a degree bounding both domains. -/
theorem aggTab_state_size (c : ℕ) (a : RawAggTestInput) (n : ℕ) (ha : AggTablePre c n a) (j : ℕ)
    (hj : j ≤ (aggTabSetUp c a).1) :
    Enc.size (tabStep^[j] (aggTabSetUp c a).2) ≤
      2 * Enc.size a + 2 * (1 + 2 ^ (1 * lg n ^ (c + 1)) *
        (2 * (1 + lg n ^ c * (2 * Enc.size a + 1)) + 1)) := by
  obtain ⟨ks, base, dom⟩ := a
  obtain ⟨hbase, hdom⟩ := ha
  have hdomN : Enc.size dom ≤ Enc.size ((ks, base, dom) : RawAggTestInput) :=
    (size_snd_le' (base, dom)).trans (size_snd_le' (ks, base, dom))
  set N := Enc.size ((ks, base, dom) : RawAggTestInput)
  by_cases hg : ks.length ≤ guardBound c base.length
  · have hdom := hdom hg
    have hset : aggTabSetUp c (ks, base, dom) = (ks.length, (dom, [[]])) := if_pos hg
    have hj' : j ≤ ks.length := by rw [hset] at hj; exact hj
    have hstate : tabStep^[j] (aggTabSetUp c (ks, base, dom)).2 = (dom, tuplesOf dom j) := by
      rw [hset]; exact tabStep_iterate dom j
    rw [hstate]
    have hB' : j ≤ (Nat.log 2 n + 1) ^ c := by
      refine le_trans (le_trans hj' hg) ?_
      rw [guardBound]
      exact Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.log_mono_right hbase) 1) c
    have hB : j ≤ lg n ^ c := le_trans hB' (Nat.pow_le_pow_left (by unfold lg; omega) c)
    have hA : dom.length ^ j ≤ 2 ^ (1 * lg n ^ (c + 1)) := by
      rw [one_mul]; exact pow_le_quasi hdom hB'
    have hent : ∀ t ∈ tuplesOf dom j, Enc.size t ≤ 1 + j * (2 * N + 1) := by
      intro t ht
      obtain ⟨hlen, hmem⟩ := (mem_tuplesOf dom j t).1 ht
      have h := size_list_le_of_entries t N
        (fun x hx => le_trans (size_mem_le (hmem x hx)) hdomN)
      rw [hlen] at h
      exact h
    have hlist : Enc.size (tuplesOf dom j)
        ≤ 1 + dom.length ^ j * (2 * (1 + j * (2 * N + 1)) + 1) := by
      have h := size_list_le_of_entries (tuplesOf dom j) (1 + j * (2 * N + 1)) hent
      rwa [length_tuplesOf] at h
    have hstep3 : dom.length ^ j * (2 * (1 + j * (2 * N + 1)) + 1)
        ≤ 2 ^ (1 * lg n ^ (c + 1)) * (2 * (1 + lg n ^ c * (2 * N + 1)) + 1) := by
      refine Nat.mul_le_mul hA ?_
      have h := Nat.mul_le_mul_right (2 * N + 1) hB
      omega
    calc Enc.size ((dom, tuplesOf dom j) : List ℕ × List (List ℕ))
        ≤ 2 * Enc.size dom + 2 * Enc.size (tuplesOf dom j) := size_pair_le' _
      _ ≤ _ := by omega
  · have hset : aggTabSetUp c (ks, base, dom) = (0, (dom, [])) := if_neg hg
    have hj0 : j = 0 := by rw [hset] at hj; exact Nat.le_zero.1 hj
    subst hj0
    have hstate : tabStep^[0] (aggTabSetUp c (ks, base, dom)).2
        = ((dom, []) : List ℕ × List (List ℕ)) := by rw [hset]; rfl
    rw [hstate]
    have h1 : Enc.size ((dom, ([] : List (List ℕ))) : List ℕ × List (List ℕ))
        ≤ 2 * Enc.size dom + 2 * Enc.size ([] : List (List ℕ)) := size_pair_le' _
    have h2 : Enc.size ([] : List (List ℕ)) = 1 := rfl
    omega

/-- **The guarded tuple table, bounded at the degree** with exponent `c + 1`. -/
theorem aggTable (c : ℕ) : TN (Algo.aggTable c) (AggTablePre c) (c + 1) := by
  have hstep : TN (fun x : ℕ × (List ℕ × List (List ℕ)) => (x.1 - 1, tabStep x.2))
      (fun _ _ => True) (c + 1) :=
    ofPoly ((polyFun_fst.sub (polyFun_const 1)).pair (polyFun_snd.comp polyFun_tabStep)) _ _
  refine (iterateSetup (ofPoly (aggPolyFun_tabSetUp c) (AggTablePre c) (c + 1)) hstep
    (ofPoly (polyFun_snd.comp polyFun_tabRead) (fun _ _ => True) (c + 1)) ?_ ?_
    (fun _ _ _ _ _ => trivial) (fun _ _ _ => trivial)).of_eq (fun _ => rfl)
  · refine Bounded.size.mono fun n a _ => ?_
    by_cases hg : a.1.length ≤ guardBound c a.2.1.length
    · have hs : aggTabSetUp c a = (a.1.length, (a.2.2, [[]])) := if_pos hg
      rw [hs]
      exact (length_le_size a.1).trans (size_fst_le' a)
    · have hs : aggTabSetUp c a = (0, (a.2.2, [])) := if_neg hg
      rw [hs]
      exact Nat.zero_le _
  · -- the counter and the state
    have hb : Bounded (fun n a => 2 * (Enc.size a + 2) + 2 * (2 * Enc.size a + 2 * (1 +
        2 ^ (1 * lg n ^ (c + 1)) * (2 * (1 + lg n ^ c * (2 * Enc.size a + 1)) + 1))))
        (AggTablePre c) (c + 1) := by
      have hs := (Bounded.size (Pre := AggTablePre c) (k := c + 1))
      have e1 := (Bounded.lg_pow (Pre := AggTablePre c) c (by omega)).mul
        (((Bounded.const 2).mul hs).add (Bounded.const 1))
      have e2 := ((Bounded.const 2).mul ((Bounded.const 1).add e1)).add (Bounded.const 1)
      have e3 := (Bounded.const 1).add ((Bounded.two_pow_lg 1 (c + 1) le_rfl).mul e2)
      have e4 := ((Bounded.const 2).mul hs).add ((Bounded.const 2).mul e3)
      exact ((Bounded.const 2).mul (hs.add (Bounded.const 2))).add ((Bounded.const 2).mul e4)
    obtain ⟨A, b, hb⟩ := hb
    refine ⟨A, b, fun n a ha j hj => le_trans ?_ (hb n a ha)⟩
    have h1 := size_pair_le' (((aggTabSetUp c a).1 - j,
      tabStep^[j] (aggTabSetUp c a).2) : ℕ × (List ℕ × List (List ℕ)))
    have h2 := aggTab_state_size c a n ha j hj
    have h3 : Enc.size ((aggTabSetUp c a).1 - j) ≤ Enc.size a + 2 := by
      have hc : (aggTabSetUp c a).1 ≤ Enc.size a := by
        by_cases hg : a.1.length ≤ guardBound c a.2.1.length
        · have hs : aggTabSetUp c a = (a.1.length, (a.2.2, [[]])) := if_pos hg
          rw [hs]
          exact (length_le_size a.1).trans (size_fst_le' a)
        · have hs : aggTabSetUp c a = (0, (a.2.2, [])) := if_neg hg
          rw [hs]
          exact Nat.zero_le _
      rw [Small.size_nat]
      have := size_le_self ((aggTabSetUp c a).1 - j)
      omega
    dsimp only at h1 ⊢
    omega

end TN

end Explicit
