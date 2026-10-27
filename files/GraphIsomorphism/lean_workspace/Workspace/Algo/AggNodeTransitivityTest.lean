import Workspace.Algo.AggNodeTransitivityOrder

/-! # Polynomial RAM tests for multiple transitivity

The tuple length is bounded by the explicit domain. A failed length test
returns false. The order equality avoids enumerating tuples, and both
factorials have arguments at most the domain length on every raw input.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

def aggnTransitivityStab (p : (List ℕ × RawGens) × ℕ) : RawGens :=
  tidyGens (p.1.1, rawPointStab (p.1, List.range (min p.2 p.1.1.length)))

def aggnTransitivityTest (p : (List ℕ × RawGens) × ℕ) : Bool :=
  decide (p.2 ≤ p.1.1.length) &&
    decide (rawOrder p.1 * Nat.factorial (p.1.1.length - p.2) =
      Nat.factorial p.1.1.length * rawOrder (p.1.1, aggnTransitivityStab p))

theorem aggnPolyFun_transitivityStab : PolyFun aggnTransitivityStab := by
  have hd : PolyFun (fun p : (List ℕ × RawGens) × ℕ => p.1.1) := polyFun_fst.comp polyFun_fst
  have hr := (hd.pair polyFun_snd).comp polyFun_rangeTake
  exact (hd.pair ((polyFun_fst.pair hr).comp polyFun_rawPointStab)).comp polyFun_tidyGens

theorem aggnPolyFun_transitivityTest : PolyFun aggnTransitivityTest := by
  have hd : PolyFun (fun p : (List ℕ × RawGens) × ℕ => p.1.1) := polyFun_fst.comp polyFun_fst
  have hm := hd.comp polyFun_length
  have hbound : ∀ p : (List ℕ × RawGens) × ℕ, p.1.1.length ≤ Enc.size p := fun p =>
    (length_le_size p.1.1).trans ((size_fst_le' p.1).trans (size_fst_le' p))
  have hfac := hm.factorial hbound polyBound_id
  have hsub := (hm.pair polyFun_snd).comp polyFun_sub
  have hfacsub := hsub.factorial (fun p => (Nat.sub_le _ _).trans (hbound p)) polyBound_id
  have ho : PolyFun (fun p : (List ℕ × RawGens) × ℕ => rawOrder p.1) :=
    polyFun_fst.comp polyFun_rawOrder
  have hs := (hd.pair aggnPolyFun_transitivityStab).comp polyFun_rawOrder
  exact wftPolyFun_and (polyFun_snd.le hm) ((ho.mul hfacsub).natEq (hfac.mul hs))

theorem aggnOrder_of_wf {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) : rawOrder (dom, gs) = Nat.card (decGroup m gs) := by
  have h := rawOrder_spec dom hd (gs.map (decPerm m))
  simpa only [map_encPerm_decPerm hw] using h

theorem aggnTransitivityStab_spec {m d : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) (hdm : d ≤ m) :
    decGroup m (aggnTransitivityStab ((dom, gs), d)) =
      pointwiseStabilizer (decGroup m gs) {u : Fin m | u.val < d} := by
  rw [aggnTransitivityStab, decGroup_tidyGens hd, hd, Nat.min_eq_left hdm]
  have h := decGroup_rawPointStab dom hd (gs.map (decPerm m)) (List.range d) List.nodup_range
    (fun u hu => (List.mem_range.mp hu).trans_le hdm)
  simpa only [map_encPerm_decPerm hw, List.mem_range] using h

/-- The test is exact, including tuple lengths too large to exist. -/
theorem aggnTransitivityTest_spec {m d : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) :
    aggnTransitivityTest ((dom, gs), d) = true ↔ IsMultiplyTransitive (decGroup m gs) d := by
  simp only [aggnTransitivityTest, Bool.and_eq_true, decide_eq_true_eq, hd]
  by_cases hdm : d ≤ m
  · rw [and_iff_right hdm, aggnOrder_of_wf hd hw,
      aggnOrder_of_wf hd (show RawGens.WF m (aggnTransitivityStab ((dom, gs), d)) from wf_tidyGens hd _),
      aggnTransitivityStab_spec hd hw hdm, aggnMultipleTransitive_card hdm]
    have hfac := Nat.factorial_mul_descFactorial hdm
    constructor
    · intro h
      apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos (m - d))
      calc Nat.factorial (m - d) * Nat.card (decGroup m gs)
          = Nat.factorial m * Nat.card (pointwiseStabilizer (decGroup m gs) {u : Fin m | u.val < d}) := by
              simpa only [Nat.mul_comm] using h
        _ = Nat.factorial (m - d) *
            (m.descFactorial d * Nat.card (pointwiseStabilizer (decGroup m gs) {u : Fin m | u.val < d})) := by
              rw [← hfac, Nat.mul_assoc]
    · intro h
      rw [h, Nat.mul_right_comm, Nat.mul_comm (m.descFactorial d), hfac]
  · simp only [hdm, false_and, false_iff]
    intro h
    exact hdm (by simpa only [Fintype.card_fin] using le_card_of_multiplyTransitive h)

end Algo
