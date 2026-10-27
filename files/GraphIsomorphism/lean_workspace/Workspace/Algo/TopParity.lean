import Workspace.Algo.TopStab
import Workspace.TopAction.TopAction2

/-!
# Sec. 12: deciding the parity of the top action

Count the inversions of each image generator. All generators are even
exactly when the image lies in the alternating group. The lists supply
the loop bounds, so the test runs in polynomial time on the RAM.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)
open scoped BigOperators

/-- An inversion of the permutation table. -/
def topInversion (p : RawPerm × (ℕ × ℕ)) : Bool :=
  if p.2.1 < p.2.2 then decide (rawGet (p.1, p.2.2) < rawGet (p.1, p.2.1)) else false

def topInversions (p : RawPerm) : List (ℕ × ℕ) :=
  (topPairs (rawOne p)).filter (fun q => topInversion (p, q))

/-- The parity test used in Corollary 12.0.6. -/
def topEven (p : RawPerm) : Bool := decide ((topInversions p).length % 2 = 0)

theorem polyFun_topInversion : PolyFun topInversion := by
  have hi : PolyFun (fun p : RawPerm × (ℕ × ℕ) => p.2.1) := polyFun_snd.comp polyFun_fst
  have hj : PolyFun (fun p : RawPerm × (ℕ × ℕ) => p.2.2) := polyFun_snd.comp polyFun_snd
  have hai := (polyFun_fst.pair hi).comp polyFun_rawGet
  have haj := (polyFun_fst.pair hj).comp polyFun_rawGet
  exact (PolyFun.ite ((hi.add (polyFun_const 1)).le hj)
    ((haj.add (polyFun_const 1)).le hai) (polyFun_const false)).of_eq
      (fun p => by simp [topInversion])

theorem polyFun_topInversions : PolyFun topInversions :=
  (polyFun_id.pair (polyFun_rawOne.comp polyFun_topPairs)).comp
    (PolyFun.filterParam polyFun_topInversion)

theorem polyFun_topEven : PolyFun topEven :=
  (((polyFun_topInversions.comp polyFun_length).mod (polyFun_const 2)).pair
    (polyFun_const 0)).comp polyFun_natEq

private theorem neg_one_pow_filter_length {α : Type*} (p : α → Bool) (l : List α) :
    (-1 : ℤˣ) ^ (l.filter p).length = (l.map (fun a => if p a then -1 else 1)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases hp : p a
    · simpa only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.prod_cons, one_mul] using ih
    · simp only [List.filter_cons, hp, ↓reduceIte, List.length_cons,
        List.map_cons, List.prod_cons]
      calc
        _ = (-1 : ℤˣ) ^ (l.filter p).length * (-1) := pow_succ _ _
        _ = _ := by rw [ih, mul_comm]

theorem sign_eq_topInversions {m : ℕ} (σ : Perm (Fin m)) :
    σ.sign = (-1 : ℤˣ) ^ (topInversions (encPerm m σ)).length := by
  rw [topInversions, neg_one_pow_filter_length]
  have he : rawOne (encPerm m σ) = List.ofFn (fun i : Fin m => i.val) := by
    rw [rawOne_eq, length_encPerm]
    rfl
  rw [topPairs, he]
  simp only [List.map_ofFn, List.map_flatten, Function.comp_apply,
    List.prod_flatten, List.prod_ofFn]
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
  apply Finset.prod_congr rfl
  intro i _
  have hIoi : Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by ext j; simp
  rw [hIoi, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j _
  simp only [topInversion, rawGet, List.getD_eq_getElem
    (encPerm m σ) 0 (n := i.val) (by simpa using i.isLt), List.getD_eq_getElem
    (encPerm m σ) 0 (n := j.val) (by simpa using j.isLt), getElem_encPerm]
  by_cases hij : i < j
  · have hne : σ i ≠ σ j := fun h => hij.ne (σ.injective h)
    by_cases hs : σ i < σ j
    · simp [hij, Fin.lt_def, hs, not_lt_of_gt hs]
    · have hs' : σ j < σ i := lt_of_le_of_ne (le_of_not_gt hs) (Ne.symm hne)
      simp [hij, Fin.lt_def, hs, hs']
  · simp [hij, Fin.lt_def]

/-- The RAM parity test agrees with the sign homomorphism. -/
theorem topEven_encPerm {m : ℕ} (σ : Perm (Fin m)) :
    topEven (encPerm m σ) = true ↔ σ ∈ alternatingGroup (Fin m) := by
  rw [Equiv.Perm.mem_alternatingGroup, sign_eq_topInversions]
  simp only [topEven, decide_eq_true_eq]
  exact Nat.even_iff.symm.trans
    (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)).symm

/-- Inspect only the images of the generators. -/
def topAllEven (p : RawAction) : Bool := (p.2.2.filter (fun r => !topEven r)).isEmpty

theorem polyFun_topAllEven : PolyFun topAllEven := by
  have hnot : PolyFun (fun r => !topEven r) :=
    (PolyFun.ite polyFun_topEven (polyFun_const false) (polyFun_const true)).of_eq
      (fun r => by cases topEven r <;> rfl)
  exact ((polyFun_snd.comp polyFun_snd).comp (PolyFun.filter hnot)).comp polyFun_isEmpty

/-- Corollary 12.0.6: the Boolean selects the alternating-image branch
exactly when all elements of the image are even. -/
theorem topAllEven_spec {n m : ℕ} (dom gdom : List ℕ)
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {ϕ : genGroup gens →* Perm (Fin m)} (hI : ImgsOf gens imgs ϕ) :
    topAllEven ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))) = true ↔
      ϕ.range ≤ alternatingGroup (Fin m) := by
  rw [hI.range_eq_genGroup, genGroup, Subgroup.closure_le]
  simp [topAllEven, List.filter_eq_nil_iff, topEven_encPerm, Set.subset_def]

/-- The first odd image generator, when one exists. -/
def topOddImage (p : RawAction) : Option RawPerm :=
  (p.2.2.filter (fun r => !topEven r)).head?

theorem polyFun_topOddImage : PolyFun topOddImage := by
  have hnot : PolyFun (fun r => !topEven r) :=
    (PolyFun.ite polyFun_topEven (polyFun_const false) (polyFun_const true)).of_eq
      (fun r => by cases topEven r <;> rfl)
  exact ((polyFun_snd.comp polyFun_snd).comp (PolyFun.filter hnot)).comp polyFun_headOption

/-- An odd representative for the Luks descent in Corollary 12.0.6. -/
def topOddLift (p : RawAction) : Option RawPerm :=
  (topOddImage p).bind (fun r => actPreimage (p, r))

theorem polyFun_topOddLift : PolyFun topOddLift := by
  exact ((polyFun_topOddImage.pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const none)
      ((polyFun_snd.pair polyFun_fst).comp polyFun_actPreimage))).of_eq
        (fun p => by unfold topOddLift; cases topOddImage p <;> rfl)

/-- Corollary 12.0.6: a negative parity test supplies a representative
of the other coset of the alternating preimage. -/
theorem topOddLift_spec {n m : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {ϕ : genGroup gens →* Perm (Fin m)} (hd : dom.length = n) (hm : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hodd : ¬ϕ.range ≤ alternatingGroup (Fin m)) :
    ∃ (σ : Perm (Fin n)) (hσ : σ ∈ genGroup gens),
      topOddLift ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))) =
        some (encPerm n σ) ∧ ϕ ⟨σ, hσ⟩ ∉ alternatingGroup (Fin m) := by
  let p : RawAction := ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m)))
  have hne : topOddImage p ≠ none := by
    intro he
    have hempty : (p.2.2.filter (fun r => !topEven r)) = [] :=
      List.head?_eq_none_iff.1 he
    have heven : topAllEven p = true := by simp [topAllEven, hempty]
    exact hodd ((topAllEven_spec dom gdom hI).1 heven)
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hne
  have hmem : r ∈ p.2.2.filter (fun r => !topEven r) := List.mem_of_mem_head? hr
  obtain ⟨hmem, htest⟩ := List.mem_filter.1 hmem
  obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 hmem
  have hτodd : τ ∉ alternatingGroup (Fin m) := by
    intro h
    have ht := (topEven_encPerm τ).2 h
    simp [ht] at htest
  have hτrange : τ ∈ ϕ.range := by
    rw [hI.range_eq_genGroup]
    exact Subgroup.subset_closure hτ
  have hlift : actPreimage (p, encPerm m τ) ≠ none := by
    intro h
    exact ((actPreimage_eq_none_iff hd hm hI τ).1 h) hτrange
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 hlift
  obtain ⟨σ, hσ, he, himg⟩ := actPreimage_eq_some hd hm hI τ hs
  refine ⟨σ, hσ, ?_, ?_⟩
  · change (topOddImage p).bind _ = _
    rw [hr, Option.bind_some, hs, he]
  · rwa [himg]

open scoped Pointwise in
/-- The computed odd lift gives the two cosets used by Luks descent. -/
theorem topOddLift_cover {n m : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {ϕ : genGroup gens →* Perm (Fin m)} (hd : dom.length = n) (hm : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hodd : ¬ϕ.range ≤ alternatingGroup (Fin m)) :
    ∃ σ : Perm (Fin n),
      topOddLift ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))) =
        some (encPerm n σ) ∧
      (genGroup gens : Set (Perm (Fin n))) =
        ⋃ τ ∈ ({1, σ} : Set (Perm (Fin n))),
          τ • (Babai.preimageAlt ϕ : Set (Perm (Fin n))) := by
  obtain ⟨σ, hσ, he, ho⟩ := topOddLift_spec hd hm hI hodd
  exact ⟨σ, he, Babai.coe_eq_biUnion_preimageAlt ϕ hσ ho⟩

end Algo
