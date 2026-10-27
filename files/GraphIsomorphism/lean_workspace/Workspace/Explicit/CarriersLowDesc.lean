/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the descent carrier of line 2
and of line 1, step 5, bounded at the degree. Not part of the faithful formalization.
-/
import Workspace.Explicit.CarriersLowBase

/-!
# The descent carrier bounded at the degree

The descent carrier `masterShiftOps (masterDescOpenOps 3 sel)` (Sec. 11.1: the Luks descent
over the coset representatives of the kernel) recomputes its lists `masterDescLists 3 (sel P)`
in every local routine. The only quasipolynomial part of the lists is the index scan: the
guarded tuple tables `aggTable 3` (image domain) and `aggTable 2` (ground set, arity
`log₂ n + 2`), which part 1 bounds at the degree (`Explicit.TN.aggTable`, exponents 4 and 3).
Everything else is polynomial (the proofs of `Algo.quasiFun_masterDescLists` and of the
routines of `Algo.masterDescOpen_runCostQ`).

* `Explicit.tn_masterDescLists`: the lists, bounded at the size of the input, exponent 4;
* `Explicit.carrierTN_desc`: the four routines of the descent carrier, exponent 5;
* `Explicit.stateBoundsX_desc`: its fold states and answers, with an explicit exponent 5.
-/

set_option synthInstance.maxSize 2048

namespace Explicit

open RAM Algo

theorem descInput_x_length_le (p : MasterDescInput) : p.1.2.2.2.1.length ≤ Enc.size p :=
  (length_le_size _).trans ((size_fst_le' _).trans ((size_snd_le' _).trans
    ((size_snd_le' _).trans ((size_snd_le' _).trans (size_fst_le' p)))))

theorem descInput_dom_length_le (p : MasterDescInput) : p.2.1.length ≤ Enc.size p :=
  (length_le_size _).trans ((size_fst_le' _).trans (size_snd_le' p))

/-- **The index keys of the descent**, bounded at the size of the input, exponent 4. -/
theorem tn_masterDescKeys :
    TN (masterDescKeys 3) (fun n (p : MasterDescInput) => Enc.size p ≤ n) 4 := by
  have ht : PolyFun (fun p : MasterDescInput => p.2.1) := polyFun_snd.comp polyFun_fst
  have hx : PolyFun (fun p : MasterDescInput => p.1.2.2.2.1) :=
    (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have h1 := ((TN.poly_comp (ht.pair (hx.pair ht)) (TN.aggTable 3)).comp_poly
    polyFun_snd).restrict (Pre' := fun n (p : MasterDescInput) => Enc.size p ≤ n)
    (fun n p hp => ⟨(descInput_x_length_le p).trans hp,
      fun _ => (descInput_dom_length_le p).trans hp⟩)
  have h2 := (((TN.poly_comp ((hx.comp polyFun_masterDescArity).pair
    (hx.pair (hx.comp polyFun_rawOne))) (TN.aggTable 2)).comp_poly polyFun_snd).mono_k
    (by norm_num : 2 + 1 ≤ 4)).restrict (Pre' := fun n (p : MasterDescInput) => Enc.size p ≤ n)
    (fun n p hp => ⟨(descInput_x_length_le p).trans hp, fun _ => by
      show (rawOne p.1.2.2.2.1).length ≤ n
      rw [rawOne, List.length_range]
      exact (descInput_x_length_le p).trans hp⟩)
  exact ((h1.pair h2).comp_poly polyFun_append).of_eq (fun _ => rfl)

/-- **The lists of the descent**, bounded at the size of the input, exponent 4. -/
theorem tn_masterDescLists :
    TN (masterDescLists 3) (fun n (p : MasterDescInput) => Enc.size p ≤ n) 4 := by
  have hfuel := ((tn_masterDescKeys.comp_poly polyFun_rangeLength).pair
    (TN.ofPoly polyFun_masterDescWidth _ 4)).comp_poly polyFun_take
  have hreps := ((TN.ofPoly polyFun_id _ 4).pair hfuel).comp_poly
    (PolyFun.mapParam polyFun_masterDescRep)
  have hk := polyFun_masterDescAction.comp polyFun_topKernel
  exact ((TN.ofPoly polyFun_fst _ 4).pair ((TN.ofPoly hk _ 4).pair (hreps.pair
    (TN.ofPoly ((hk.pair (polyFun_fst.comp polyFun_fst)).comp polyFun_winOrbits) _ 4)))).of_eq
    (fun _ => rfl)

section Desc

variable (a b : ℕ) {sel : RawMasterSI → MasterDescInput} (hsel : PolyFun sel)

include hsel in
/-- The lists at an admitted node, bounded at its degree. -/
theorem tn_masterDescLists_sel :
    TN (fun P => masterDescLists 3 (sel P))
      (fun n P => MasterInputWF a b P ∧ masterDegree P ≤ n) 5 :=
  TN.ofMaster hsel (tn_masterDescLists.mono_k (by norm_num)) a b

include hsel in
/-- **The descent carrier, bounded at the degree.** -/
theorem carrierTN_desc (R : RawMasterSI → Prop) :
    CarrierTN a b (masterShiftOps (masterDescOpenOps 3 sel)) R := by
  have hL := tn_masterDescLists_sel a b hsel
  have hLc := TN.poly_comp (polyFun_fst (α := RawMasterSI) (β := ℕ × AggnRecomputeState)) hL
  have hLu := TN.poly_comp
    (polyFun_fst (α := RawMasterSI) (β := ℕ × AggnRecomputeState × RawCoset)) hL
  have hLf := TN.poly_comp (polyFun_fst (α := RawMasterSI) (β := AggnRecomputeState)) hL
  have hx : PolyFun (fun z : RawMasterSI × AggnRecomputeState => z.1.1.2.2.2.1) :=
    (((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp
      polyFun_snd).comp polyFun_fst)
  have hr : PolyFun (fun z : RawMasterSI × AggnRecomputeState => z.1.1.2.2.1) :=
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst)
  have hfin := (hLf.pair (TN.ofPoly polyFun_snd _ 5)).comp_poly polyFun_masterDescFoldFinish
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (((hLc.pair (TN.ofPoly polyFun_snd _ 5)).comp_poly
      polyFun_masterDescFoldChild).of_eq (fun _ => rfl)).restrict
      (fun n z h => ⟨h.1, h.2.1⟩)
  · exact ((hL.comp_poly polyFun_masterDescFoldInit).of_eq (fun _ => rfl)).restrict
      (fun n P h => ⟨h.1, h.2.1⟩)
  · exact (((hLu.pair (TN.ofPoly polyFun_snd _ 5)).comp_poly
      polyFun_masterDescFoldCombine).of_eq (fun _ => rfl)).restrict
      (fun n z h => ⟨h.1.1, h.1.2.1⟩)
  · exact ((((TN.ofPoly hx _ 5).pair ((TN.ofPoly hr _ 5).pair hfin)).comp_poly
      polyFun_top3Shift).of_eq (fun _ => rfl)).restrict (fun n z h => ⟨h.1, h.2.1⟩)

include hsel in
/-- **The fold states and answers of the descent carrier**, with an explicit exponent 5,
when the selector keeps the source string of the node. -/
theorem stateBoundsX_desc (hsource : ∀ P, (sel P).1.2.2.2.1 = P.1.2.2.2.1) :
    ∃ K, StateBoundsX a b K (masterShiftOps (masterDescOpenOps 3 sel)) := by
  obtain ⟨A, e, -, hs⟩ := tn_masterDescLists_sel a b hsel
  have hq : Q5 (fun N => 16 * (2 ^ (A * lg N ^ 5) * (masterInputCap a b N + 1) ^ e +
      chainBound N + 1)) :=
    ((q5_const 16).mul ((((q5_two_pow_lg A 5 le_rfl).mul
      (((q5_masterInputCap a b).add (q5_const 1)).pow e)).add
      (q5_of_polyBound polyBound_chainBound)).add (q5_const 1))).mono (fun _ => le_rfl)
  obtain ⟨K, hK⟩ := hq
  have hlist : ∀ P, MasterInputWF a b P →
      Enc.size (masterDescLists 3 (sel P)) ≤
        2 ^ (A * lg (masterDegree P) ^ 5) * (masterInputCap a b (masterDegree P) + 1) ^ e :=
    fun P hP => (hs _ P ⟨hP, le_rfl⟩).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := hP.1; omega) _))
  have hx : ∀ P, (masterDescLists 3 (sel P)).1.2.2.2.1.length = masterDegree P :=
    fun P => congrArg List.length (hsource P)
  refine StateBoundsX.of_three K (fun P hP => ?_) (fun P j s A' hP _ => ?_) (fun P s _ => ?_)
  · have h := masterDescFoldInit_size (masterDescLists 3 (sel P))
    rw [hx] at h
    have h2 := hlist P hP
    have h3 := hK (masterDegree P)
    change Enc.size (masterDescFoldInit (masterDescLists 3 (sel P))) ≤ _
    dsimp only at h3
    omega
  · have h := masterDescFoldCombine_size (masterDescLists 3 (sel P)) j s A'
    rw [hx] at h
    have h2 := hlist P hP
    have h3 := hK (masterDegree P)
    change Enc.size (masterDescFoldCombine (masterDescLists 3 (sel P), j, s, A')) ≤ _
    dsimp only at h3
    omega
  · exact (masterShiftOps_finish_size _ P s).trans (by unfold masterInputCap; omega)

end Desc

end Explicit
