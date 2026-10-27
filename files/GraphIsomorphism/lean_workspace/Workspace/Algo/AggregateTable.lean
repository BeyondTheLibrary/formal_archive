import Workspace.Algo.WLGuarded

/-! # Tuple tables with an independent ambient size witness

The tuple domain is `[m]`, while the arity guard can use the ambient size `n`.
This enumerates `m^t` tuples and keeps the same quasipolynomial bound.
-/
namespace Algo
open RAM RAM.Targets

/-- Arity witness, ambient domain witness, and tuple-domain witness. -/
abbrev RawAggTestInput := List ℕ × List ℕ × List ℕ

def aggTabSetUp (c : ℕ) (a : RawAggTestInput) : ℕ × (List ℕ × List (List ℕ)) :=
  if a.1.length ≤ guardBound c a.2.1.length then (a.1.length, (a.2.2, [[]]))
  else (0, (a.2.2, []))

/-- Build tuples on the third component, with the guard on the second component. -/
def aggTable (c : ℕ) (a : RawAggTestInput) : RawWL :=
  tabRead (tabStep^[(aggTabSetUp c a).1] (aggTabSetUp c a).2)

theorem aggTable_of_guard {c : ℕ} {a : RawAggTestInput}
    (hg : a.1.length ≤ guardBound c a.2.1.length) :
    aggTable c a = tupleTable a.2.2 a.1.length := by
  have hs : aggTabSetUp c a = (a.1.length, (a.2.2, [[]])) := if_pos hg
  rw [aggTable, hs, tabStep_iterate]
  rfl

theorem aggSize_tabState (c₀ : ℕ) (a : RawAggTestInput) (j : ℕ)
    (hj : j ≤ (aggTabSetUp c₀ a).1) :
    Enc.size (tabStep^[j] (aggTabSetUp c₀ a).2) ≤ tabSizeBound c₀ (Enc.size a) := by
  obtain ⟨ks, base, dom⟩ := a
  set N := Enc.size ((ks, base, dom) : RawAggTestInput) with hN
  have hdomN : Enc.size dom ≤ N :=
    (size_snd_le' (base, dom)).trans (size_snd_le' (ks, base, dom))
  have hnN : dom.length ≤ N := (length_le_size dom).trans hdomN
  have hbaseN : base.length ≤ N :=
    ((length_le_size base).trans (size_fst_le' (base, dom))).trans
      (size_snd_le' (ks, base, dom))
  by_cases hg : ks.length ≤ guardBound c₀ base.length
  · have hset : aggTabSetUp c₀ (ks, base, dom) = (ks.length, (dom, [[]])) := if_pos hg
    have hj' : j ≤ ks.length := by rw [hset] at hj; exact hj
    have hstate : tabStep^[j] (aggTabSetUp c₀ (ks, base, dom)).2 = (dom, tuplesOf dom j) := by
      rw [hset]; exact tabStep_iterate dom j
    rw [hstate]
    -- the arity is below the guard
    have hlogmono : Nat.log 2 base.length ≤ Nat.log 2 N := Nat.log_mono_right hbaseN
    have hB' : j ≤ (Nat.log 2 N + 1) ^ c₀ := by
      refine le_trans (le_trans hj' hg) ?_
      rw [guardBound]
      exact Nat.pow_le_pow_left (by omega) c₀
    have hB : j ≤ (Nat.log 2 N + 2) ^ c₀ :=
      le_trans hB' (Nat.pow_le_pow_left (by omega) c₀)
    -- the number of tuples is quasipolynomially bounded
    have hdom2 : dom.length ≤ 2 ^ (Nat.log 2 N + 1) := le_trans hnN (le_two_pow_log N)
    have hA : dom.length ^ j ≤ 2 ^ ((Nat.log 2 N + 2) ^ (c₀ + 1)) := by
      calc dom.length ^ j ≤ (2 ^ (Nat.log 2 N + 1)) ^ j := Nat.pow_le_pow_left hdom2 j
        _ = 2 ^ ((Nat.log 2 N + 1) * j) := by rw [← pow_mul]
        _ ≤ 2 ^ ((Nat.log 2 N + 1) ^ (c₀ + 1)) := by
            refine Nat.pow_le_pow_right (by norm_num) ?_
            calc (Nat.log 2 N + 1) * j
                ≤ (Nat.log 2 N + 1) * (Nat.log 2 N + 1) ^ c₀ := Nat.mul_le_mul_left _ hB'
              _ = (Nat.log 2 N + 1) ^ (c₀ + 1) := by rw [pow_succ]; ring
        _ ≤ 2 ^ ((Nat.log 2 N + 2) ^ (c₀ + 1)) :=
            Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left (by omega) _)
    -- each tuple has `j` entries, each an entry of the vertex list
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
        ≤ 2 ^ ((Nat.log 2 N + 2) ^ (c₀ + 1))
          * (2 * (1 + (Nat.log 2 N + 2) ^ c₀ * (2 * N + 1)) + 1) := by
      refine Nat.mul_le_mul hA ?_
      have h := Nat.mul_le_mul_right (2 * N + 1) hB
      omega
    calc Enc.size ((dom, tuplesOf dom j) : List ℕ × List (List ℕ))
        ≤ 2 * Enc.size dom + 2 * Enc.size (tuplesOf dom j) := size_pair_le' _
      _ ≤ 2 * N + 2 * (1 + dom.length ^ j * (2 * (1 + j * (2 * N + 1)) + 1)) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hdomN) (Nat.mul_le_mul_left _ hlist)
      _ ≤ tabSizeBound c₀ N :=
          Nat.add_le_add_left (Nat.mul_le_mul_left 2 (Nat.add_le_add_left hstep3 1)) (2 * N)
  · have hset : aggTabSetUp c₀ (ks, base, dom) = (0, (dom, [])) := if_neg hg
    have hj0 : j = 0 := by rw [hset] at hj; exact Nat.le_zero.1 hj
    subst hj0
    have hstate : tabStep^[0] (aggTabSetUp c₀ (ks, base, dom)).2
        = ((dom, []) : List ℕ × List (List ℕ)) := by rw [hset]; rfl
    rw [hstate]
    have h1 : Enc.size ((dom, ([] : List (List ℕ))) : List ℕ × List (List ℕ))
        ≤ 2 * Enc.size dom + 2 * Enc.size ([] : List (List ℕ)) := size_pair_le' _
    have h2 : Enc.size ([] : List (List ℕ)) = 1 := rfl
    have h3 := le_tabSizeBound c₀ N
    omega


theorem aggPolyFun_tabSetUp (c : ℕ) : PolyFun (aggTabSetUp c) := by
  have hk : PolyFun (fun a : RawAggTestInput => a.1.length) :=
    polyFun_fst.comp polyFun_length
  have hd : PolyFun (fun a : RawAggTestInput => a.2.2) := polyFun_snd.comp polyFun_snd
  have hb : PolyFun (fun a : RawAggTestInput => guardBound c a.2.1.length) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp (polyFun_guardBound c)
  refine (PolyFun.ite (hk.le hb) (hk.pair (hd.pair (polyFun_const [[]])))
    ((polyFun_const 0).pair (hd.pair (polyFun_const [])))).of_eq (fun a => ?_)
  by_cases h : a.1.length ≤ guardBound c a.2.1.length <;> simp [aggTabSetUp, h]

/-- The guard allows the intermediate tuple table to have quasipolynomial size. -/
theorem aggQuasiFun_table (c : ℕ) : QuasiFun (aggTable c) := by
  have hstep : QuasiFun (fun x : ℕ × (List ℕ × List (List ℕ)) => (x.1 - 1, tabStep x.2)) :=
    ((polyFun_fst.sub (polyFun_const 1)).pair (polyFun_snd.comp polyFun_tabStep)).quasiFun
  refine (QuasiFun.iterateSetup (q := fun n => n) (p := tabSizeBound c)
    (aggPolyFun_tabSetUp c).quasiFun hstep polyFun_tabRead.quasiFun ?_ polyBound_id.quasiPoly
    (aggSize_tabState c) (quasiPolyBound_tabSizeBound c)).of_eq (fun _ => rfl)
  intro a
  by_cases hg : a.1.length ≤ guardBound c a.2.1.length
  · have hs : aggTabSetUp c a = (a.1.length, (a.2.2, [[]])) := if_pos hg
    rw [hs]
    exact (length_le_size a.1).trans (size_fst_le' a)
  · have hs : aggTabSetUp c a = (0, (a.2.2, [])) := if_neg hg
    rw [hs]
    exact Nat.zero_le _

end Algo
