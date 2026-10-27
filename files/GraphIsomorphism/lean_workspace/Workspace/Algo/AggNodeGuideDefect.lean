import Workspace.Algo.AggNodeGuideSuccess

/-! The local-guide twin-set argument transfers to the actual relation
tables. The only numerical premise is the large fixed set of Case 3. -/
set_option quotPrecheck false
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

section
variable {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState} {tbl : RawAggCompareTable}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1)
    (htbl : AggnCompareTableFor c ϕ tbl)
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10*C.2.2.2.length ≤ m)
    [Nonempty (Fin n)]
local notation "X" => (fun b : Bool => cond b (decStrN n C.2.2.1) (decStrN n C.2.1))
local notation "D" => localGuideData ϕ C.2.2.2.length X hset ht ((Nat.card_fin m).symm ▸ htm)
local notation "name" => (fun b : Bool => (Subtype.val : ↥(fixedGamma ϕ (X b) C.2.2.2.length) → Fin m))
local notation "names" => (fun b : Bool => (aggnAggregateData ((C,s),b)).2.2)
local notation "rows" => (fun b : Bool => aggnGuideRows c (C.2.2.2,C.2.1,names b))
local notation "reps" => aggnGuideReps ((C.1,tbl),rows false)
local notation "side" => (fun b : Bool => aggnGuideSideRows c ((C.2.2.2,C.2.1),names b))
local notation "relctx" => (fun b : Bool => ((C.1,tbl),b,side b))
include hC hs htbl hset ht htm

/-- Changing vertex or relation numbering does not change the guide's symmetricity. -/
theorem aggnGuideNumbered_symmetricity (b : Bool)
    (hcov : aggnGuideCovered (aggnGuideAt (aggnGuidePrepare c ((C,s),tbl),true)) = true) :
    symmetricity (aggnGuideNumberedStruct (c := c) (C := C) (s := s) (tbl := tbl) b).Aut =
      symmetricity ((D).guideStruct b).Aut := by
  classical
  rw [← aggnGuideClassStruct_aut hC hs htbl hset ht htm b hcov,
    ← aggnGuideNumberedStruct_map hC hs htbl hset ht htm b,
    RelStructure.aut_map_equiv,symmetricity_map_permCongrHom]

/-- The local-guide proof excludes a twin set of the tested arity. -/
theorem aggnGuideNumbered_symmetricity_lt (b : Bool)
    (hcov : aggnGuideCovered (aggnGuideAt (aggnGuidePrepare c ((C,s),tbl),true)) = true) :
    symmetricity (aggnGuideNumberedStruct (c := c) (C := C) (s := s) (tbl := tbl) b).Aut < C.2.2.2.length := by
  classical
  rw [aggnGuideNumbered_symmetricity hC hs htbl hset ht htm b hcov]
  apply (D).symmetricity_guideStruct_lt (by have hh := ht.eight_lt; omega)
  intro L hL
  exact not_isFullAt_guideMorL ϕ C.2.2.2.length X hset ht ((Nat.card_fin m).symm ▸ htm) b L hL

/-- The paper's absolute defect bound holds for the computed numbered guide. -/
theorem aggnGuideNumbered_absolute_defect (b : Bool)
    (hcov : aggnGuideCovered (aggnGuideAt (aggnGuidePrepare c ((C,s),tbl),true)) = true)
    (hlarge : 4*m < 5*(names b).length) :
    (names b).length - C.2.2.2.length + 1 ≤
        symDefect (aggnGuideNumberedStruct (c := c) (C := C) (s := s) (tbl := tbl) b).Aut ∧
      m < 2 * symDefect (aggnGuideNumberedStruct (c := c) (C := C) (s := s) (tbl := tbl) b).Aut := by
  have hh := aggnGuideNumbered_symmetricity_lt hC hs htbl hset ht htm b hcov
  simp only [symDefect,Fintype.card_fin]
  dsimp only at hlarge ⊢
  omega

/-- The actual numbered guide meets the Design Lemma's arity and defect assumptions. -/
theorem aggnGuideNumbered_admissible (b : Bool)
    (hcov : aggnGuideCovered (aggnGuideAt (aggnGuidePrepare c ((C,s),tbl),true)) = true)
    (hlarge : 4*m < 5*(names b).length) :
    2 ≤ C.2.2.2.length ∧ 4*C.2.2.2.length ≤ (names b).length ∧
      (1/2 : ℚ) < defect (aggnGuideNumberedStruct (c := c) (C := C) (s := s) (tbl := tbl) b).Aut := by
  dsimp only at hlarge ⊢
  have ht8 := ht.eight_lt
  have hh := aggnGuideNumbered_symmetricity_lt hC hs htbl hset ht htm b hcov
  refine ⟨by omega,by omega,?_⟩
  have hp : (0 : ℚ) < (names b).length := by exact_mod_cast (show 0 < (names b).length by dsimp only; omega)
  have hs2 : 2 * symmetricity (aggnGuideNumberedStruct (c := c) (C := C) (s := s) (tbl := tbl) b).Aut <
      (names b).length := by dsimp only; omega
  have hr : (symmetricity (aggnGuideNumberedStruct (c := c) (C := C) (s := s) (tbl := tbl) b).Aut : ℚ) /
      (names b).length < 1/2 := by
    apply (div_lt_iff₀ hp).mpr
    have hh' : (2 : ℚ) * symmetricity
        (aggnGuideNumberedStruct (c := c) (C := C) (s := s) (tbl := tbl) b).Aut < (names b).length := by
      exact_mod_cast hs2
    linarith
  unfold defect relSymmetricity
  simp only [Fintype.card_fin]
  linarith

end
end Algo
