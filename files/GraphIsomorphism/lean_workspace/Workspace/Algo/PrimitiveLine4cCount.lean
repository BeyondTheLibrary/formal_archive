/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, line 4c on the RAM: the number of versions, counted in the size of the window.
-/
import Workspace.Algo.PrimitiveLine4c

/-!
# Section 15, line 4c: the number of versions in the size of the window

Theorem 9.2.3 bounds the family by `q(m)·m^{O(t)}`; the Master counts it in the window size
`n` (`Babai.Line4cdDataAt`, `Babai.line4cdCost`).  The RAM's family is the output of the
Extended Design Lemma on the input `line4cAmbient`, so its length is bounded by a
quasipolynomial of the size of that input.  This file bounds that size by a quasipolynomial
of `n` alone (`Algo.size_line4cAmbient_le`): the input holds the arity list, `[0, n)`,
`[0, m)` with `m ≤ n`, and one relation per letter of the palette (`2n + 1` of them), each a
set of `t`-tuples over `[0, m)` with `t ≤ log₂ n + 1` by the arity guard.  Nothing in it
depends on the generators of the group or on the labels of `Ω`.

`Algo.line4cVersions_length_le_window` is the resulting count: one quasipolynomial `R` with
both lists of line 4c at most `R(n)` long.
-/

namespace Algo
open RAM RAM.Targets

/-! ## The bound -/

/-- The size of a row: `t ≤ log₂ n + 1` entries, each below `n`. -/
def l4cRow (D : ℕ) : ℕ := 1 + (Nat.log 2 D + 1) * (2 * (D + 2) + 1)

/-- The number of rows of a relation: `m^t ≤ (n+1)^{log₂ n + 1}`. -/
def l4cCount (D : ℕ) : ℕ := (D + 1) ^ (Nat.log 2 D + 1)

/-- The size of one relation. -/
def l4cRel (D : ℕ) : ℕ := 1 + l4cCount D * (2 * l4cRow D + 1)

/-- The size of the relations, one per letter of the palette. -/
def l4cRels (D : ℕ) : ℕ := 1 + (2 * D + 1) * (2 * l4cRel D + 1)

/-- The size of a list of at most `n` entries below `n`. -/
def l4cList (D : ℕ) : ℕ := 1 + D * (2 * (D + 2) + 1)

/-- **The size of the input of the Extended Design Lemma at line 4c**, in the window size. -/
def line4cSizeBound (D : ℕ) : ℕ :=
  2 * (2 * (2 * l4cList D + 2 * (2 * l4cList D + 2 * l4cList D)) + 2 * l4cRels D) +
    2 * Enc.size ((3, 4) : ℕ × ℕ)

theorem mono_l4cCount : Monotone l4cCount := fun a b h =>
  (Nat.pow_le_pow_left (by omega) _).trans
    (Nat.pow_le_pow_right (by omega) (by have := Nat.log_mono_right (b := 2) h; omega))

theorem mono_l4cRow : Monotone l4cRow := fun a b h => by
  have := Nat.log_mono_right (b := 2) h
  unfold l4cRow
  exact Nat.add_le_add_left (Nat.mul_le_mul (by omega) (by omega)) 1

theorem mono_l4cRel : Monotone l4cRel := fun a b h => by
  unfold l4cRel
  exact Nat.add_le_add_left (Nat.mul_le_mul (mono_l4cCount h)
    (by have := mono_l4cRow h; omega)) 1

theorem mono_l4cRels : Monotone l4cRels := fun a b h => by
  unfold l4cRels
  exact Nat.add_le_add_left (Nat.mul_le_mul (by omega)
    (by have := mono_l4cRel h; omega)) 1

theorem mono_l4cList : Monotone l4cList := fun a b h => by
  unfold l4cList
  exact Nat.add_le_add_left (Nat.mul_le_mul h (by omega)) 1

theorem mono_line4cSizeBound : Monotone line4cSizeBound := fun a b h => by
  have h1 := mono_l4cList h
  have h2 := mono_l4cRels h
  unfold line4cSizeBound
  omega

theorem quasiPolyBound_l4cCount : QuasiPolyBound l4cCount := by
  refine ⟨2, fun D => ?_⟩
  have hD : D + 1 ≤ 2 ^ (Nat.log 2 D + 1) := Nat.lt_pow_succ_log_self (by norm_num) D
  calc l4cCount D ≤ (2 ^ (Nat.log 2 D + 1)) ^ (Nat.log 2 D + 1) :=
        Nat.pow_le_pow_left hD _
    _ = 2 ^ ((Nat.log 2 D + 1) * (Nat.log 2 D + 1)) := by rw [← pow_mul]
    _ ≤ 2 ^ ((Nat.log 2 D + 2) ^ 2) :=
        Nat.pow_le_pow_right (by norm_num) (by rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega))

theorem polyBound_l4cRow : PolyBound l4cRow := by
  have hL : PolyBound (fun D => Nat.log 2 D + 1) :=
    (polyBound_id.add (polyBound_const 1)).mono (fun D => by
      have := Nat.log_le_self 2 D; omega)
  exact ((polyBound_const 1).add (hL.mul (((polyBound_const 2).mul
    (polyBound_id.add (polyBound_const 2))).add (polyBound_const 1)))).mono
    (fun _ => le_of_eq rfl)

theorem polyBound_l4cList : PolyBound l4cList :=
  ((polyBound_const 1).add (polyBound_id.mul (((polyBound_const 2).mul
    (polyBound_id.add (polyBound_const 2))).add (polyBound_const 1)))).mono
    (fun _ => le_of_eq rfl)

theorem quasiPolyBound_line4cSizeBound : QuasiPolyBound line4cSizeBound := by
  have hRel : QuasiPolyBound l4cRel :=
    ((polyBound_const 1).quasiPoly.add (quasiPolyBound_l4cCount.mul
      (((polyBound_const 2).mul polyBound_l4cRow).add (polyBound_const 1)).quasiPoly)).mono
      (fun _ => le_of_eq rfl)
  have hRels : QuasiPolyBound l4cRels :=
    ((polyBound_const 1).quasiPoly.add
      ((((polyBound_const 2).mul polyBound_id).add (polyBound_const 1)).quasiPoly.mul
        (((polyBound_const 2).quasiPoly.mul hRel).add (polyBound_const 1).quasiPoly))).mono
      (fun _ => le_of_eq rfl)
  have hL := polyBound_l4cList
  have hT : PolyBound (fun D => 2 * l4cList D + 2 * (2 * l4cList D + 2 * l4cList D)) :=
    (((polyBound_const 2).mul hL).add ((polyBound_const 2).mul
      (((polyBound_const 2).mul hL).add ((polyBound_const 2).mul hL)))).mono
      (fun _ => le_of_eq rfl)
  exact (((polyBound_const 2).quasiPoly.mul (((polyBound_const 2).mul hT).quasiPoly.add
    ((polyBound_const 2).quasiPoly.mul hRels))).add
    (polyBound_const (2 * Enc.size ((3, 4) : ℕ × ℕ))).quasiPoly).mono
    (fun _ => le_of_eq rfl)

/-! ## The size of the input -/

/-- The keys of the tuple table: tuples of the arity's length over the domain list, below
the guard, and at most `(|dom|+1)^{guard}` of them. -/
theorem aggTable_keys (a : RawAggTestInput) :
    (∀ k ∈ (aggTable 1 a).2.map Prod.fst, k.length ≤ guardBound 1 a.2.1.length ∧
      ∀ x ∈ k, x ∈ a.2.2) ∧
    ((aggTable 1 a).2.map Prod.fst).length ≤
      (a.2.2.length + 1) ^ guardBound 1 a.2.1.length := by
  by_cases hg : a.1.length ≤ guardBound 1 a.2.1.length
  · rw [aggTable_of_guard hg, keys_tupleTable]
    refine ⟨fun k hk => ?_, ?_⟩
    · obtain ⟨hl, hm⟩ := (mem_tuplesOf _ _ k).1 hk
      exact ⟨hl ▸ hg, hm⟩
    · rw [length_tuplesOf]
      exact (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) hg)
  · have hs : aggTable 1 a = tabRead (a.2.2, []) := by
      rw [aggTable, aggTabSetUp, if_neg hg]
      rfl
    rw [hs]
    exact ⟨fun k hk => by simp [tabRead] at hk, by simp [tabRead]⟩

theorem size_nat_le_add_two (D : ℕ) : Enc.size D ≤ D + 2 := by
  have h1 : Enc.size D = Nat.size D + 2 := Small.size_nat D
  have h2 : Nat.size D ≤ D := size_le_self D
  omega

/-- A list of at most `D` numbers, each at most `D`, fits `l4cList D`. -/
theorem size_list_le_l4cList {D : ℕ} (l : List ℕ) (hl : l.length ≤ D) (he : ∀ x ∈ l, x ≤ D) :
    Enc.size l ≤ l4cList D := by
  have h := size_list_le_of_entries l (D + 2) (fun x hx =>
    (size_nat_le_of_le (he x hx)).trans (size_nat_le_add_two D))
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hl) 1)

/-- **The input of the Extended Design Lemma at line 4c is quasipolynomially large in the
window size `n`**, when `m ≤ n` and both strings have at most `n` letters. -/
theorem size_line4cAmbient_le (z : RawLine4cIn × RawStr)
    (hm : z.1.1.1.2.1.length ≤ z.1.1.1.1.1.length)
    (hx : z.1.1.2.1.length ≤ z.1.1.1.1.1.length) (hy : z.1.1.2.2.length ≤ z.1.1.1.1.1.length) :
    Enc.size (line4cAmbient z) ≤ line4cSizeBound z.1.1.1.1.1.length := by
  set D := z.1.1.1.1.1.length with hD
  set m := z.1.1.1.2.1.length with hmdef
  -- the three lists
  have har : Enc.size (line4cArity z.1) ≤ l4cList D := by
    refine size_list_le_l4cList _ ?_ ?_
    · simp only [line4cArity, List.length_range]; omega
    · intro x hx'
      simp only [line4cArity, List.mem_range] at hx'
      omega
  have hrD : Enc.size (List.range D) ≤ l4cList D :=
    size_list_le_l4cList _ (by simp) (fun x hx' => by simp at hx'; omega)
  have hrm : Enc.size (List.range m) ≤ l4cList D :=
    size_list_le_l4cList _ (by simp; omega) (fun x hx' => by simp at hx'; omega)
  -- the relations
  set keys := (aggTable 1 (line4cArity z.1, z.1.1.1.1.1, List.range m)).2.map Prod.fst
    with hkeys
  obtain ⟨hk, hkl⟩ := aggTable_keys (line4cArity z.1, z.1.1.1.1.1, List.range m)
  have hG : guardBound 1 D = Nat.log 2 D + 1 := by rw [guardBound, pow_one]
  have hrow : ∀ k ∈ keys, Enc.size k ≤ l4cRow D := by
    intro k hkm
    obtain ⟨hlen, hmem⟩ := hk k hkm
    have h := size_list_le_of_entries k (D + 2) (fun x hx' => by
      have := hmem x hx'
      simp only [List.mem_range] at this
      exact (size_nat_le_of_le (by omega : x ≤ D)).trans (size_nat_le_add_two D))
    change k.length ≤ guardBound 1 D at hlen
    rw [hG] at hlen
    exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hlen) 1)
  have hcount : keys.length ≤ l4cCount D := by
    change keys.length ≤ ((List.range m).length + 1) ^ guardBound 1 D at hkl
    rw [List.length_range, hG] at hkl
    exact hkl.trans (Nat.pow_le_pow_left (by omega) _)
  have hrel : ∀ a : ℕ, Enc.size (primitiveRelRows (((z.1.1.1, z.2), keys), a)) ≤ l4cRel D := by
    intro a
    have h := size_list_le_of_entries (primitiveRelRows (((z.1.1.1, z.2), keys), a)) (l4cRow D)
      (fun r hr => hrow r (List.mem_filter.1 hr).1)
    have hlen : (primitiveRelRows (((z.1.1.1, z.2), keys), a)).length ≤ keys.length :=
      List.length_filter_le _ _
    exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (hlen.trans hcount)) 1)
  have hpal : (line4cPalette z.1.1).length ≤ 2 * D + 1 := by
    simp only [line4cPalette, List.length_cons, List.length_append]
    omega
  have hrels : Enc.size (primitiveRelations 1 (((z.1.1.1, z.2), line4cArity z.1),
      line4cPalette z.1.1)) ≤ l4cRels D := by
    have h := size_list_le_of_entries (primitiveRelations 1 (((z.1.1.1, z.2), line4cArity z.1),
      line4cPalette z.1.1)) (l4cRel D) (fun r hr => by
        obtain ⟨a, -, rfl⟩ := List.mem_map.1 hr
        exact hrel a)
    have hlen : (primitiveRelations 1 (((z.1.1.1, z.2), line4cArity z.1),
        line4cPalette z.1.1)).length ≤ 2 * D + 1 := by
      rw [primitiveRelations, List.length_map]; exact hpal
    exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hlen) 1)
  -- the pairs
  have h3 := size_pair_le' ((List.range D, List.range m) : List ℕ × List ℕ)
  have h2 := size_pair_le' ((line4cArity z.1, List.range D, List.range m) :
    List ℕ × List ℕ × List ℕ)
  have h1 := size_pair_le' (((line4cArity z.1, List.range D, List.range m),
    primitiveRelations 1 (((z.1.1.1, z.2), line4cArity z.1), line4cPalette z.1.1)) :
      (List ℕ × List ℕ × List ℕ) × RawRelStruct)
  have h0 := size_pair_le' (line4cAmbient z)
  change Enc.size (line4cAmbient z) ≤ _
  have e0 : (line4cAmbient z).1 = ((line4cArity z.1, List.range D, List.range m),
      primitiveRelations 1 (((z.1.1.1, z.2), line4cArity z.1), line4cPalette z.1.1)) := rfl
  have e1 : (line4cAmbient z).2 = ((3, 4) : ℕ × ℕ) := rfl
  rw [e0, e1] at h0
  dsimp only at h1 h2 h3
  unfold line4cSizeBound
  omega

/-! ## The count -/

/-- **Section 15, line 4c: the number of versions is quasipolynomial in the window size.**
There is one quasipolynomial `R` such that, whenever `m ≤ n` and both strings have at most
`n` letters (`n` the size of `Ω`), both lists of line 4c have at most `R(n)` entries. -/
theorem line4cVersions_length_le_window (c tt dd : ℕ) :
    ∃ R : ℕ → ℕ, QuasiPolyBound R ∧ Monotone R ∧ ∀ z : RawLine4cIn,
      z.1.1.2.1.length ≤ z.1.1.1.1.length → z.1.2.1.length ≤ z.1.1.1.1.length →
      z.1.2.2.length ≤ z.1.1.1.1.length →
      (line4cVersions c tt dd z).1.length ≤ R z.1.1.1.1.length ∧
        (line4cVersions c tt dd z).2.length ≤ R z.1.1.1.1.length := by
  obtain ⟨E, hEq, hEm, hEs⟩ := (quasiFun_extendedSplitFamily 1 c tt dd).size.exists_quasiPolyBound
  refine ⟨fun D => E (line4cSizeBound D), hEq.comp quasiPolyBound_line4cSizeBound,
    fun a b h => hEm _ _ (mono_line4cSizeBound h), fun z hm hx hy => ⟨?_, ?_⟩⟩
  · exact (length_le_size _).trans ((hEs _).trans
      (hEm _ _ (size_line4cAmbient_le (z, z.1.2.1) hm hx hy)))
  · exact (length_le_size _).trans ((hEs _).trans
      (hEm _ _ (size_line4cAmbient_le (z, z.1.2.2) hm hx hy)))

end Algo

#print axioms Algo.size_line4cAmbient_le
#print axioms Algo.line4cVersions_length_le_window
