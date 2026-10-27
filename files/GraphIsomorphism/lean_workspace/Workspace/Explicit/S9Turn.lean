/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): one turn of the Split-or-Johnson
recursion of Sec. 9, bounded at an external degree. Not part of the faithful formalization.
-/
import Workspace.Explicit.S9Design
import Workspace.Algo.SplitBipTurnRaw

/-!
# One turn of Sec. 9, bounded at the degree

`Explicit.TN.sbipTurn`: the local turn `Algo.sbipTurn` (Steps 1, 2, 4, 6 and 9 of Sec. 9.4–9.7)
with exponent `max (c+2) 4`, whenever the first part has at most `n` points and, when Steps 3–5
succeed, the Step 9 case input has size at most `n`. The loops are the individualizations of
Steps 1 and 2 (`Algo.sbipNumberings`, tuples of length `O(log n)` over the small part) and the
Design Lemma of case 3 (`Explicit.TN.designCase3Graphs`).
-/

namespace Explicit

open RAM Algo

namespace TN

/-- **The numberings of Step 2**: the ambient domain has at most `n` points. -/
theorem sbipNumberings (c : ℕ) :
    TN (Algo.sbipNumberings c) (fun n (p : List ℕ × List ℕ) => p.1.length ≤ n) (c + 1) := by
  have ht := (aggTable c).scale 1 (c + 1) (Pre' := fun n (x : RawAggTestInput) =>
      x.2.1.length ≤ n ∧ x.2.2 = List.range x.1.length) (fun n x hx => by
    refine ⟨n + (n + 1) ^ c, ?_, ?_, fun hg => ?_⟩
    · have h1 : n ≤ (n + 1) ^ (c + 1) :=
        (Nat.le_succ n).trans (Nat.le_self_pow (by omega) _)
      have h2 : (n + 1) ^ c ≤ (n + 1) ^ (c + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      rw [pow_one]
      omega
    · exact hx.1.trans (Nat.le_add_right _ _)
    · rw [hx.2, List.length_range]
      refine (hg.trans ?_).trans (Nat.le_add_left _ _)
      rw [guardBound]
      exact Nat.pow_le_pow_left ((Nat.add_le_add_right ((Nat.log_mono_right hx.1).trans
        (Nat.log_le_self 2 n)) 1)) c)
  exact (((ofPoly (polyFun_snd.pair (polyFun_fst.pair (polyFun_snd.comp polyFun_rangeLength)))
    _ _).comp ht (fun n p hp => ⟨hp, rfl⟩)).comp_poly
      (polyFun_snd.comp (PolyFun.map polyFun_fst))).comp_poly (PolyFun.filter wftPolyFun_nodup)

theorem sbipStep1Versions (C : ℕ) :
    TN (Algo.sbipStep1Versions C) (fun n p => p.1.length ≤ n) (C + 1) :=
  ((id' _ _).pair ((ofPoly (polyFun_fst.pair polyFun_fst) _ _).comp (sbipNumberings C)
    (fun _ _ h => h))).comp_poly (PolyFun.mapParam polyFun_sbipStep1)

theorem sbipStep2Versions (c : ℕ) :
    TN (Algo.sbipStep2Versions c) (fun n p => p.1.1.length ≤ n) (c + 1) :=
  ((id' _ _).pair ((ofPoly ((polyFun_fst.comp polyFun_fst).pair
    ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)) _ _).comp (sbipNumberings c)
      (fun _ _ h => h))).comp_poly (PolyFun.mapParam polyFun_sbipStep2)

/-! ## Step 9 -/

theorem sbipTurnDesign3 :
    TN Algo.sbipTurnDesign3 (fun n z => Enc.size z ≤ n) 4 := by
  have hfst : PolyFun (fun z : RawSbipTurnCase × (List ℕ × RawDesignGraph) => z.1) :=
    polyFun_fst
  have hsnd : PolyFun (fun z : RawSbipTurnCase × (List ℕ × RawDesignGraph) => z.2) :=
    polyFun_snd
  have hgraph : PolyFun (fun z : List ℕ × RawDesignGraph => z.2) := polyFun_snd
  have he : PolyFun (fun z : RawSbipTurnCase × (List ℕ × RawDesignGraph) =>
      sbipTurnDesignGraph (z.1, z.2.2)) :=
    (hfst.pair (hsnd.comp hgraph)).comp polyFun_sbipTurnDesignGraph
  have hm : PolyFun (fun z : RawSbipTurnCase × List (List ℕ × RawDesignGraph) =>
      z.2.map (fun q => sbipTurnDesignGraph (z.1, q.2))) := PolyFun.mapParam he
  have hd : TN (fun z : RawSbipTurnCase => Algo.designCase3Graphs z.2.1)
      (fun n z => Enc.size z ≤ n) 4 :=
    (poly_comp (polyFun_snd.comp polyFun_fst) designCase3Graphs).restrict
      (fun n z hz => ((size_fst_le' z.2).trans (size_snd_le' z)).trans hz)
  have hp : TN (fun z : RawSbipTurnCase => (z, Algo.designCase3Graphs z.2.1))
      (fun n z => Enc.size z ≤ n) 4 := (id' _ _).pair hd
  exact (hp.comp_poly hm).of_eq (fun z => by unfold Algo.sbipTurnDesign3; rfl)

theorem sbipTurnDesign :
    TN Algo.sbipTurnDesign (fun n z => Enc.size z ≤ n) 4 := by
  have hs : PolyFun (fun z : RawDesignCaseOut × RawSbipTurnCase =>
      [sbipTurnDesign12 (z.2, z.1)]) :=
    (((polyFun_snd.pair polyFun_fst).comp polyFun_sbipTurnDesign12).pair
      (polyFun_const [])).comp polyFun_cons
  exact (ofPoly ((polyFun_snd.comp polyFun_designCase12).pair polyFun_id) _ _).comp
    (optionElim sbipTurnDesign3 (ofPoly hs (fun _ _ => True) 4)
      (Pre := fun n p => Enc.size p.2 ≤ n)
      (fun _ _ h => h) (fun _ _ _ _ => (trivial : True))) (fun _ _ h => h)

/-- **The versions of Step 9**, on a case input of size at most `n`. -/
theorem sbipTurnCases :
    TN Algo.sbipTurnCases (fun n z => Enc.size z ≤ n) 4 := by
  have ht : PolyFun (fun z : RawSbipTurnCase => sbipStep9Case z.2.1) :=
    (polyFun_snd.comp polyFun_fst).comp sbipPoly_step9Case
  exact (ite (ht.natEq (polyFun_const 0)) (ofPoly polyFun_sbipTurnImp _ _)
    (ite (ht.natEq (polyFun_const 1)) sbipTurnDesign (ofPoly polyFun_sbipTurnUpccFamily _ _)
      (fun _ _ h _ => h) (fun _ _ _ _ => trivial))
    (fun _ _ _ _ => trivial) (fun _ _ h _ => h)).of_eq (fun z => by simp [Algo.sbipTurnCases])

/-! ## The whole turn -/

/-- The precondition of a turn at degree `n`: the first part has at most `n` points, and the
Step 9 case input has size at most `n` when Steps 3–5 succeed. -/
def TurnPre (n : ℕ) (z : RawSbipTurnInput) : Prop :=
  z.2.1.1.1.1.length ≤ n ∧
    ((sbipGraphSteps35 (sbipTurnGraphInput z)).2 ≠ none → Enc.size (sbipTurnCase z) ≤ n)

theorem sbipTurnAfter35 :
    TN Algo.sbipTurnAfter35 (fun n z => Enc.size (sbipTurnCase z) ≤ n) 4 := by
  have ht := (polyFun_sbipTurnGraphInput.comp polyFun_sbipGraphComponentTable).comp
    sbipPoly_imprimitive
  have hp := ((polyFun_sbipTurnGraphInput.comp polyFun_sbipGraphComponentPartition).comp
    polyFun_sbipTurnPartition |>.pair (polyFun_const [])).comp polyFun_cons
  exact ite ht (ofPoly hp _ _) (poly_comp polyFun_sbipTurnCase sbipTurnCases)
    (fun _ _ _ _ => trivial) (fun _ _ h _ => h)

theorem sbipTurnLarge : TN Algo.sbipTurnLarge TurnPre 4 := by
  have hp := ((polyFun_sbipTurnGraphInput.comp polyFun_sbipGraphEarly4).comp
    polyFun_sbipTurnPartition |>.pair (polyFun_const [])).comp polyFun_cons
  have ho := ((polyFun_sbipTurnGraphInput.comp polyFun_sbipGraphSteps35).comp polyFun_snd).pair
    polyFun_id
  exact (ofPoly ho _ _).comp (optionElim (ofPoly hp _ _)
      ((ofPoly polyFun_snd _ _).comp sbipTurnAfter35 (fun _ _ h => h))
      (Pre := fun n p => (p.1 ≠ none → Enc.size (sbipTurnCase p.2) ≤ n))
      (fun _ _ _ => trivial) (fun n x s h => h (by simp)))
    (fun n z hz => hz.2)

/-- **One turn of Sec. 9**, with exponent `max (c + 2) 4`. -/
theorem sbipTurn (c : ℕ) : TN (Algo.sbipTurn c) TurnPre (max (c + 2) 4) := by
  have hg : PolyFun (fun z : RawSbipTurnInput => z.2.1.1) :=
    (polyFun_snd.comp polyFun_fst).comp polyFun_fst
  have e1 : TN (fun y : RawSbipGraph × (ℕ × ℕ) => sbipGraphEarly1 c y)
      (fun n y => y.1.1.1.length ≤ n) (c + 1) :=
    (poly_comp (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair polyFun_snd)
      (sbipStep1Versions c)).of_eq (fun _ => rfl)
  have h1 : TN (fun z : RawSbipTurnInput =>
      (sbipGraphEarly1 c (sbipTurnGraphInput z)).map sbipTurnPartition) TurnPre
      (max (c + 2) 4) :=
    ((poly_comp polyFun_sbipTurnGraphInput (e1.mono_k (by omega))).restrict
      (fun n z hz => hz.1)).comp_poly (PolyFun.map polyFun_sbipTurnPartition)
  have e2 : TN (fun r : RawSbipGraph => sbipGraphEarly2 (c + 1) r)
      (fun n r => r.1.1.length ≤ n) (c + 2) :=
    (poly_comp polyFun_sbipGraphEarly2Input (sbipStep2Versions (c + 1))).of_eq (fun _ => rfl)
  have h2 : TN (fun z : RawSbipTurnInput =>
      (sbipGraphEarly2 (c + 1) z.2.1.1).map sbipTurnPartition) TurnPre (max (c + 2) 4) :=
    ((poly_comp hg (e2.mono_k (by omega))).restrict
      (fun n z hz => hz.1)).comp_poly (PolyFun.map polyFun_sbipTurnPartition)
  exact ite (hg.comp (polyFun_sbipGraphSmall1 c)) h1
    (ite (hg.comp (polyFun_sbipGraphSmall2 c)) h2 (sbipTurnLarge.mono_k (by omega))
      (fun _ _ h _ => h) (fun _ _ h _ => h)) (fun _ _ h _ => h) (fun _ _ h _ => h)

end TN

end Explicit
