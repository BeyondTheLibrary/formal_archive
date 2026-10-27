/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: primitive groups of degree 9 of order divisible
by `64`.
-/
import Workspace.AltQuotients.DM52.OrbitTools

/-!
# A primitive group of degree 9 containing a Sylow `2`-subgroup of `A_9`

A primitive group `G ≤ A_9` with `64 ∣ |G|` contains `A_9`.  Indeed a Sylow `2`-subgroup of
`G` is a Sylow `2`-subgroup of `A_9` (`|A_9| = 2⁶ · 2835`), so after relabeling it is the
explicit group `P0` (the even automorphisms of the binary tree on `{0, …, 7}`, fixing `8`).
Take `g ∈ G` with `g 8 = 0`.  Among the double transpositions `u0 = (0 3)(1 2)`,
`u1 = (0 1)(6 7)`, `u2 = (4 6)(5 7)`, `u7 = (2 3)(4 5)` of `P0` there is one, `b`, whose
support meets the support of `u0` after moving it by `g` in exactly one point; then the
commutator of `u0` and `g b g⁻¹` is a `3`-cycle (Exercise 1.6.7 of [DiM]), and Jordan's
theorem ([DiM, Thm. 3.3A]) gives `A_9 ≤ G`.  The last step is checked for every `g` with
`g 8 = 0` by evaluation.
-/

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Nat Subgroup

/-! ### The Sylow `2`-subgroup `P0` -/

/-- `(0 3)(1 2)`. -/
def q0 : Perm (Fin 9) := ofVec ![3, 2, 1, 0, 4, 5, 6, 7, 8] ![3, 2, 1, 0, 4, 5, 6, 7, 8] (by decide)
/-- `(0 1)(6 7)`. -/
def q1 : Perm (Fin 9) := ofVec ![1, 0, 2, 3, 4, 5, 7, 6, 8] ![1, 0, 2, 3, 4, 5, 7, 6, 8] (by decide)
/-- `(4 6)(5 7)`. -/
def q2 : Perm (Fin 9) := ofVec ![0, 1, 2, 3, 6, 7, 4, 5, 8] ![0, 1, 2, 3, 6, 7, 4, 5, 8] (by decide)
/-- `(0 6 1 7)(2 4 3 5)`. -/
def q3 : Perm (Fin 9) := ofVec ![6, 7, 4, 5, 3, 2, 1, 0, 8] ![7, 6, 5, 4, 2, 3, 0, 1, 8] (by decide)

/-- The generators of `P0`. -/
def gensP0 : List (Perm (Fin 9)) := [q0, q1, q2, q3]

/-- `P0 := ⟨q0, q1, q2, q3⟩`, a Sylow `2`-subgroup of `A_9`. -/
def P0 : Subgroup (Perm (Fin 9)) := closure {q0, q1, q2, q3}

/-- Words for the `64` elements of `P0`. -/
def wordsP0 : List (List ℕ) :=
  [[], [3, 2, 3, 0], [2], [1, 2, 1], [0, 1, 0], [3, 3, 1], [2, 0, 1, 0], [0, 1, 2, 0], [1],
    [2, 1, 2], [2, 1], [1, 2], [1, 0, 1, 0], [3, 3], [3, 0, 3], [3, 3, 2], [1, 0, 1],
    [3, 3, 0], [3, 0, 3, 0], [3, 3, 2, 0], [0, 1], [3, 3, 1, 0], [2, 0, 1], [0, 1, 2], [1, 0],
    [2, 1, 2, 0], [2, 1, 0], [1, 2, 0], [0], [3, 2, 3], [2, 0], [1, 2, 1, 0], [2, 0, 3],
    [2, 3, 2], [3, 3, 3, 0], [2, 3], [0, 3, 0, 1], [3, 2, 0, 1], [3, 3, 3, 1, 0], [3, 0, 1],
    [0, 3, 1, 0], [3, 2, 1, 0], [0, 3, 2, 1, 0], [3, 1, 0], [0, 3, 0], [3, 2, 0],
    [0, 3, 2, 0], [3, 0], [0, 3], [3, 2], [0, 3, 2], [3], [0, 3, 0, 1, 0], [3, 2, 0, 1, 0],
    [3, 3, 3, 1], [3, 0, 1, 0], [0, 3, 1], [3, 2, 1], [0, 3, 2, 1], [3, 1], [2, 0, 3, 0],
    [2, 3, 2, 0], [3, 3, 3], [2, 3, 0]]

/-- The `64` elements of `P0`. -/
def listP0 : List (Perm (Fin 9)) := wordsP0.map (evalWord gensP0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem card_listP0 : listP0.toFinset.card = 64 := by decide +kernel

/-! #### The elements of `P0` as a table

The upper bound `|P0| ≤ 64` is checked on an explicit table: `tblP0` lists the images of
`0, …, 8` under the `64` elements, and `succP0` gives, for each of `q0, q1, q2, q3, q3⁻¹` and
each row, the row of the product. -/

/-- The table of the `64` elements of `P0` (images of `0, …, 8`). -/
def tblP0 : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8],
    [3, 2, 1, 0, 4, 5, 6, 7, 8],
    [1, 0, 2, 3, 4, 5, 7, 6, 8],
    [0, 1, 2, 3, 6, 7, 4, 5, 8],
    [6, 7, 4, 5, 3, 2, 1, 0, 8],
    [7, 6, 5, 4, 2, 3, 0, 1, 8],
    [3, 2, 0, 1, 4, 5, 7, 6, 8],
    [3, 2, 1, 0, 6, 7, 4, 5, 8],
    [5, 4, 7, 6, 3, 2, 1, 0, 8],
    [4, 5, 6, 7, 2, 3, 0, 1, 8],
    [2, 3, 1, 0, 4, 5, 7, 6, 8],
    [1, 0, 2, 3, 6, 7, 5, 4, 8],
    [7, 6, 4, 5, 3, 2, 0, 1, 8],
    [6, 7, 5, 4, 2, 3, 1, 0, 8],
    [1, 0, 2, 3, 7, 6, 4, 5, 8],
    [6, 7, 4, 5, 1, 0, 3, 2, 8],
    [7, 6, 5, 4, 0, 1, 2, 3, 8],
    [6, 7, 4, 5, 0, 1, 2, 3, 8],
    [4, 5, 6, 7, 3, 2, 1, 0, 8],
    [1, 0, 3, 2, 5, 4, 7, 6, 8],
    [7, 6, 5, 4, 1, 0, 3, 2, 8],
    [5, 4, 7, 6, 2, 3, 0, 1, 8],
    [0, 1, 3, 2, 4, 5, 7, 6, 8],
    [3, 2, 0, 1, 6, 7, 5, 4, 8],
    [5, 4, 6, 7, 3, 2, 0, 1, 8],
    [4, 5, 7, 6, 2, 3, 1, 0, 8],
    [3, 2, 0, 1, 7, 6, 4, 5, 8],
    [5, 4, 7, 6, 1, 0, 3, 2, 8],
    [4, 5, 6, 7, 0, 1, 2, 3, 8],
    [5, 4, 7, 6, 0, 1, 2, 3, 8],
    [7, 6, 5, 4, 3, 2, 1, 0, 8],
    [2, 3, 0, 1, 5, 4, 7, 6, 8],
    [4, 5, 6, 7, 1, 0, 3, 2, 8],
    [6, 7, 4, 5, 2, 3, 0, 1, 8],
    [2, 3, 0, 1, 4, 5, 6, 7, 8],
    [2, 3, 1, 0, 6, 7, 5, 4, 8],
    [4, 5, 7, 6, 3, 2, 0, 1, 8],
    [5, 4, 6, 7, 2, 3, 1, 0, 8],
    [0, 1, 2, 3, 7, 6, 5, 4, 8],
    [7, 6, 4, 5, 1, 0, 2, 3, 8],
    [6, 7, 5, 4, 0, 1, 3, 2, 8],
    [7, 6, 4, 5, 0, 1, 3, 2, 8],
    [0, 1, 3, 2, 5, 4, 6, 7, 8],
    [6, 7, 5, 4, 1, 0, 2, 3, 8],
    [2, 3, 1, 0, 7, 6, 4, 5, 8],
    [1, 0, 2, 3, 5, 4, 6, 7, 8],
    [1, 0, 3, 2, 7, 6, 5, 4, 8],
    [1, 0, 3, 2, 6, 7, 4, 5, 8],
    [3, 2, 1, 0, 5, 4, 7, 6, 8],
    [1, 0, 3, 2, 4, 5, 6, 7, 8],
    [0, 1, 3, 2, 6, 7, 5, 4, 8],
    [6, 7, 5, 4, 3, 2, 0, 1, 8],
    [7, 6, 4, 5, 2, 3, 1, 0, 8],
    [3, 2, 1, 0, 7, 6, 5, 4, 8],
    [5, 4, 6, 7, 1, 0, 2, 3, 8],
    [4, 5, 7, 6, 0, 1, 3, 2, 8],
    [5, 4, 6, 7, 0, 1, 3, 2, 8],
    [2, 3, 1, 0, 5, 4, 6, 7, 8],
    [4, 5, 7, 6, 1, 0, 2, 3, 8],
    [0, 1, 3, 2, 7, 6, 4, 5, 8],
    [3, 2, 0, 1, 5, 4, 6, 7, 8],
    [2, 3, 0, 1, 7, 6, 5, 4, 8],
    [2, 3, 0, 1, 6, 7, 4, 5, 8],
    [0, 1, 2, 3, 5, 4, 7, 6, 8]]

/-- Left multiplication by `q0, q1, q2, q3, q3⁻¹` on the rows of `tblP0`. -/
def succP0 : List (List ℕ) :=
  [[1, 0, 10, 7, 17, 20, 22, 3, 29, 32, 2, 35, 41, 43, 44, 33, 30, 4, 28, 31, 5, 27, 6, 50, 56, 58, 59, 21, 18, 8, 16, 19, 9, 15, 49, 11, 55, 54, 53, 52, 51, 12, 60, 13, 14, 57, 61, 62, 63, 34, 23, 40, 39, 38, 37, 36, 24, 45, 25, 26, 42, 46, 47, 48],
    [2, 6, 0, 14, 12, 13, 1, 26, 24, 25, 34, 38, 4, 5, 3, 41, 43, 39, 36, 42, 40, 37, 49, 53, 8, 9, 7, 56, 58, 54, 51, 57, 55, 52, 10, 61, 18, 21, 11, 17, 20, 15, 19, 16, 62, 63, 50, 59, 60, 22, 46, 30, 33, 23, 29, 32, 27, 31, 28, 47, 48, 35, 44, 45],
    [3, 7, 11, 0, 18, 21, 23, 1, 30, 33, 35, 2, 24, 25, 45, 32, 29, 28, 4, 46, 27, 5, 50, 6, 12, 13, 60, 20, 17, 16, 8, 61, 15, 9, 62, 10, 51, 52, 63, 54, 55, 56, 59, 58, 57, 14, 19, 49, 53, 47, 22, 36, 37, 48, 39, 40, 41, 44, 43, 42, 26, 31, 34, 38],
    [4, 8, 12, 15, 19, 0, 24, 27, 31, 1, 36, 39, 42, 2, 41, 46, 3, 47, 48, 5, 38, 34, 51, 54, 57, 6, 56, 61, 7, 62, 63, 9, 53, 49, 18, 58, 60, 10, 17, 59, 11, 50, 13, 14, 55, 52, 16, 20, 21, 30, 43, 45, 22, 29, 44, 23, 35, 25, 26, 40, 37, 28, 32, 33],
    [5, 9, 13, 16, 0, 19, 25, 28, 1, 31, 37, 40, 2, 42, 43, 3, 46, 38, 34, 4, 47, 48, 52, 55, 6, 57, 58, 7, 61, 53, 49, 8, 62, 63, 21, 56, 10, 60, 20, 11, 59, 14, 12, 50, 54, 51, 15, 17, 18, 33, 41, 22, 45, 32, 23, 44, 26, 24, 35, 39, 36, 27, 29, 30]]

/-- The permutation-like map given by a row of the table. -/
def img (l : List ℕ) (i : Fin 9) : Fin 9 := ⟨l.getD i 0 % 9, Nat.mod_lt _ (by norm_num)⟩

/-- `q0, q1, q2, q3, q3⁻¹`. -/
def genP0 (a : ℕ) : Perm (Fin 9) := [q0, q1, q2, q3, q3⁻¹].getD a 1

/-- The row index of the product of the generator `a` and row `j`. -/
def succIdx (a j : ℕ) : ℕ := (succP0.getD a []).getD j 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem succIdx_lt : ∀ a : Fin 5, ∀ j : Fin 64, succIdx a j < 64 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The table is closed under left multiplication by the generators. -/
theorem succP0_spec : ∀ a : Fin 5, ∀ j : Fin 64, ∀ i : Fin 9,
    img (tblP0.getD (succIdx a j) []) i = genP0 a (img (tblP0.getD j []) i) := by
  decide +kernel

/-- `x` is one of the rows of the table. -/
def InP0 (x : Perm (Fin 9)) : Prop := ∃ j : Fin 64, ∀ i, x i = img (tblP0.getD j []) i

theorem inP0_mul {x : Perm (Fin 9)} (hx : InP0 x) (a : Fin 5) : InP0 (genP0 a * x) := by
  obtain ⟨j, hj⟩ := hx
  refine ⟨⟨succIdx a j, succIdx_lt a j⟩, fun i => ?_⟩
  rw [Perm.mul_apply, hj, succP0_spec]

theorem inP0_of_mem {x : Perm (Fin 9)} (hx : x ∈ P0) : InP0 x := by
  have hx' : x ∈ (P0.toSubmonoid) := hx
  rw [P0, Subgroup.closure_toSubmonoid] at hx'
  clear hx
  induction hx' using Submonoid.closure_induction_left with
  | one => exact ⟨0, by decide⟩
  | mul_left s hs y _ hy =>
    rcases hs with hs | hs
    · rcases hs with rfl | rfl | rfl | rfl
      · exact inP0_mul hy 0
      · exact inP0_mul hy 1
      · exact inP0_mul hy 2
      · exact inP0_mul hy 3
    · have : s⁻¹ ∈ ({q0, q1, q2, q3} : Set (Perm (Fin 9))) := hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with h | h | h | h
      all_goals rw [inv_eq_iff_eq_inv] at h
      all_goals subst h
      · rw [show q0⁻¹ = q0 by decide]; exact inP0_mul hy 0
      · rw [show q1⁻¹ = q1 by decide]; exact inP0_mul hy 1
      · rw [show q2⁻¹ = q2 by decide]; exact inP0_mul hy 2
      · exact inP0_mul hy 4

open Classical in
/-- The permutation given by a row of the table (the identity if the row is not a
bijection). -/
noncomputable def permOf (l : List ℕ) : Perm (Fin 9) :=
  if h : Function.Bijective (img l) then Equiv.ofBijective _ h else 1

theorem card_P0 : Nat.card P0 = 64 := by
  apply le_antisymm
  · have hsub : ∀ x ∈ P0, x ∈ (Finset.univ : Finset (Fin 64)).image
        (fun j : Fin 64 => permOf (tblP0.getD (j : ℕ) [])) := by
      intro x hx
      obtain ⟨j, hj⟩ := inP0_of_mem hx
      have hf : img (tblP0.getD j []) = x := funext fun i => (hj i).symm
      have hb : Function.Bijective (img (tblP0.getD j [])) := hf ▸ x.bijective
      refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
      ext i
      rw [permOf, dif_pos hb, Equiv.ofBijective_apply, hf]
    calc Nat.card P0 ≤ _ := card_le_of_subset_finset _ hsub
      _ ≤ (Finset.univ : Finset (Fin 64)).card := Finset.card_image_le
      _ = 64 := by simp
  · rw [← card_listP0]
    apply le_card_of_finset
    intro x hx
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    apply evalWord_mem
    intro y hy
    simp only [gensP0, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> exact subset_closure (by simp)

theorem P0_le_alternatingGroup : P0 ≤ alternatingGroup (Fin 9) := by
  rw [P0, closure_le]
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp [mem_alternatingGroup] <;> decide

/-! ### Conjugating a Sylow `2`-subgroup onto `P0` -/

theorem nat_card_alternatingGroup_nine : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 9)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 9), Fintype.card_fin] at h
  have : Nat.factorial 9 = 362880 := by decide
  rw [this] at h
  omega

/-- A subgroup of `A_9` of order `64` is a Sylow `2`-subgroup of `A_9`. -/
noncomputable def sylowOfCard64 (H : Subgroup (Perm (Fin 9))) (hHA : H ≤ alternatingGroup (Fin 9))
    (hH : Nat.card H = 64) : Sylow 2 (alternatingGroup (Fin 9)) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nat.card (H.subgroupOf (alternatingGroup (Fin 9))) = 64 := by
    rw [card_subgroupOf, inf_of_le_left hHA, hH]
  (IsPGroup.of_card (n := 6) (by rw [hc]; norm_num)).toSylow (by
    have := (H.subgroupOf (alternatingGroup (Fin 9))).card_mul_index
    rw [hc, nat_card_alternatingGroup_nine] at this
    omega)

/-- Every subgroup of `A_9` of order `64` is conjugate to `P0`. -/
theorem exists_conj_P0 (H : Subgroup (Perm (Fin 9))) (hHA : H ≤ alternatingGroup (Fin 9))
    (hH : Nat.card H = 64) : ∃ a : Perm (Fin 9), ∀ x ∈ P0, a * x * a⁻¹ ∈ H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 9))
    (sylowOfCard64 P0 P0_le_alternatingGroup card_P0) (sylowOfCard64 H hHA hH)
  refine ⟨a, fun x hx => ?_⟩
  have hx' : (⟨x, P0_le_alternatingGroup hx⟩ : alternatingGroup (Fin 9)) ∈
      ((sylowOfCard64 P0 P0_le_alternatingGroup card_P0 : Sylow 2 _) :
        Subgroup (alternatingGroup (Fin 9))) := by
    show _ ∈ P0.subgroupOf _
    simpa [Subgroup.mem_subgroupOf] using hx
  have := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj a) _ hx'
  rw [← Sylow.coe_subgroup_smul, ha] at this
  have h2 : (MulAut.conj a • (⟨x, P0_le_alternatingGroup hx⟩ : alternatingGroup (Fin 9))) ∈
      H.subgroupOf (alternatingGroup (Fin 9)) := this
  rw [Subgroup.mem_subgroupOf] at h2
  simpa [MulAut.smul_def, MulAut.conj_apply] using h2

/-! ### The final check -/

/-- The supports of `a` and `g b g⁻¹` meet in exactly one point. -/
def Meet1 (a b g : Perm (Fin 9)) : Prop :=
  ((Finset.univ : Finset (Fin 9)).filter (fun j => b j ≠ j ∧ a (g j) ≠ g j)).card = 1

/-- The support of `b` meets `S` in exactly one point. -/
def MeetSet (b : Perm (Fin 9)) (S : Finset (Fin 9)) : Prop :=
  (S.filter (fun j => b j ≠ j)).card = 1

instance (b : Perm (Fin 9)) (S : Finset (Fin 9)) : Decidable (MeetSet b S) := by
  unfold MeetSet; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- For every `4`-set `S ∋ 8`, one of four double transpositions `b` of `P0` has support
meeting `S` in exactly one point. -/
theorem meetSet_cases : ∀ S : Finset (Fin 9), S.card = 4 → 8 ∈ S →
    MeetSet q0 S ∨ MeetSet q2 S ∨ MeetSet q1 S ∨ MeetSet (q3 * q3 * q1) S := by
  decide +kernel

/-- `Meet1 a b g` only depends on the set `g⁻¹ (supp a)`. -/
theorem meet1_iff (a b g : Perm (Fin 9)) :
    Meet1 a b g ↔ MeetSet b (a.support.map (g⁻¹ : Perm (Fin 9)).toEmbedding) := by
  unfold Meet1 MeetSet
  congr! 2
  ext j
  have hs : (Equiv.symm g⁻¹ : Perm (Fin 9)) j = g j := rfl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv,
    Perm.mem_support, hs]
  exact and_comm

/-- For every `g` with `g 8 = 0`, one of four double transpositions `b` of `P0` has
`g b g⁻¹` meeting `q0 = (0 3)(1 2)` in exactly one point. -/
theorem meet1_cases {g : Perm (Fin 9)} (hg : g 8 = 0) :
    Meet1 q0 q0 g ∨ Meet1 q0 q2 g ∨ Meet1 q0 q1 g ∨ Meet1 q0 (q3 * q3 * q1) g := by
  simp only [meet1_iff]
  apply meetSet_cases
  · rw [Finset.card_map]; decide
  · rw [Finset.mem_map_equiv, Perm.mem_support, show (Equiv.symm g⁻¹ : Perm (Fin 9)) 8 = g 8 from rfl,
      hg]
    decide

theorem isThreeCycle_of_meet1 {a b g : Perm (Fin 9)} (h : Meet1 a b g) :
    IsThreeCycle (a⁻¹ * (g * b * g⁻¹)⁻¹ * a * (g * b * g⁻¹)) := by
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h
  have hjmem : j ∈ (Finset.univ : Finset (Fin 9)).filter
      (fun j => b j ≠ j ∧ a (g j) ≠ g j) := by rw [hj]; simp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjmem
  have hy : ∀ w, (g * b * g⁻¹) w ≠ w ↔ b (g⁻¹ w) ≠ g⁻¹ w := by
    intro w
    simp only [Perm.mul_apply]
    constructor
    · intro h1 h2; apply h1; rw [h2]; simp
    · intro h1 h2; apply h1
      have := congrArg (⇑g⁻¹) h2
      simpa using this
  apply isThreeCycle_commutator (a := g j) hjmem.2
  · rw [hy]; simpa using hjmem.1
  · intro w hxw hyw
    rw [hy] at hyw
    have : g⁻¹ w ∈ (Finset.univ : Finset (Fin 9)).filter
        (fun j => b j ≠ j ∧ a (g j) ≠ g j) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hyw, by simpa using hxw⟩
    rw [hj, Finset.mem_singleton] at this
    rw [← this]; simp

/-- **A primitive group of degree `9` of order divisible by `64` contains `A_9`.** -/
theorem alternatingGroup_le_of_sixtyfour_dvd {G : Subgroup (Perm (Fin 9))}
    (hGA : G ≤ alternatingGroup (Fin 9)) (hG : IsPreprimitive G (Fin 9))
    (h64 : 64 ∣ Nat.card G) : alternatingGroup (Fin 9) ≤ G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- a subgroup of order `64`, conjugate to `P0`
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := G) 2 (n := 6)
    (by norm_num; exact h64)
  set H := K.map G.subtype
  have hH : Nat.card H = 64 := by
    rw [Subgroup.card_map_of_injective G.subtype_injective, hK]; norm_num
  have hHG : H ≤ G := by rintro _ ⟨x, -, rfl⟩; exact x.2
  obtain ⟨a, ha⟩ := exists_conj_P0 H (hHG.trans hGA) hH
  -- relabel so that `P0 ≤ G'`
  set G' := relabel a⁻¹ G with hG'
  have hP0 : ∀ x ∈ P0, x ∈ G' := by
    intro x hx
    rw [mem_relabel_perm, inv_inv]
    exact hHG (ha x hx)
  have hG'p : IsPreprimitive G' (Fin 9) := (isPreprimitive_relabel_iff _ G).mpr hG
  suffices hs : alternatingGroup (Fin 9) ≤ G' from alternatingGroup_le_of_relabel _ hs
  -- an element `g ∈ G'` with `g 8 = 0`
  haveI := hG'p.toIsPretransitive
  obtain ⟨⟨g, hg⟩, hg8⟩ := MulAction.exists_smul_eq G' (8 : Fin 9) 0
  replace hg8 : g 8 = 0 := hg8
  have hq : ∀ x ∈ [q0, q1, q2, q3], x ∈ G' := by
    intro x hx
    apply hP0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact subset_closure (by simp)
  have hq0 := hq q0 (by simp)
  have hmem : ∀ b ∈ G', Meet1 q0 b g → alternatingGroup (Fin 9) ≤ G' := by
    intro b hb h
    exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hG'p
      (isThreeCycle_of_meet1 h)
      (mul_mem (mul_mem (mul_mem (inv_mem hq0) (inv_mem (mul_mem (mul_mem hg hb)
        (inv_mem hg)))) hq0) (mul_mem (mul_mem hg hb) (inv_mem hg)))
  rcases meet1_cases hg8 with h | h | h | h
  · exact hmem q0 hq0 h
  · exact hmem q2 (hq q2 (by simp)) h
  · exact hmem q1 (hq q1 (by simp)) h
  · exact hmem _ (mul_mem (mul_mem (hq q3 (by simp)) (hq q3 (by simp))) (hq q1 (by simp))) h

end Babai.DM52
