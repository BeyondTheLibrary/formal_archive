import Workspace.Algo.SplitUpccCaseRaw

/-!
# Section 9.8: one version of Reduce-by-UPCC

A version is indexed by the name of the individualized second-part vertex.
The output keeps the first part, its colors, and an optional bipartite
matrix. The graph branch marks the local constituent. This is the form
used by `Babai.case_9_8`; restriction and the threshold update belong to
its caller. All loops use lists in the input.
-/

namespace Algo
open Babai RAM

/-- Section 9.8: named first part, ambient colors, and an optional marked graph. -/
abbrev RawUpccCaseOutcome := List ℕ × RawLab × Option (ℕ × RawUpccBip)

/-- Section 9.8, step 2: the local coloring, indexed by ambient name. -/
def upccCaseLocalColors (z : RawUpccCase × ℕ) : RawLab := upccCellsRaw (z.1.1,z.2)

/-- Section 9.8, step 3: mark the dominant local cell. -/
def upccCaseMarks (z : RawUpccCase × ℕ) : RawLab :=
  (upccCaseLocalColors z).map (fun k => if k = upccCaseM z then 1 else 0)

/-- Section 9.8: a row of the marked graph. The link color is read backwards,
as in `Babai.BlkCaseObj.upccBip`. -/
def upccCaseRow (z : (RawUpccCase × ℕ) × ℕ) : List ℕ :=
  (upccCaseBlock (z.1,upccCaseL z.1)).map (fun v =>
    if binColor (z.1.1.1,(z.1.2,z.2)) = upccCaseM z.1 ∧
      binColor (z.1.1.1,(v,z.2)) = upccCaseM z.1 then 1 else 0)

/-- Section 9.8: the returned graph keeps all of the first part. -/
def upccCaseGraph (z : RawUpccCase × ℕ) : RawUpccBip :=
  (z.1.2.1,upccCaseBlock (z,upccCaseL z),z.1.2.1.map (fun u => upccCaseRow (z,u)))

/-- Section 9.8, step 3: the smaller local constituent before keeping the
isolated first-part points for the reduction interface. -/
def upccCaseLocal (z : RawUpccCase × ℕ) : RawUpccBip :=
  (upccCaseLink (z,upccCaseM z),upccCaseBlock (z,upccCaseL z),
    (upccCaseLink (z,upccCaseM z)).map (fun u => upccCaseRow (z,u)))

theorem upccCasePoly_localColors : PolyFun upccCaseLocalColors :=
  ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_upccCellsRaw

theorem upccCasePoly_marks : PolyFun upccCaseMarks := by
  have he := ((polyFun_snd.pair polyFun_fst).comp polyFun_natEq)
  have ht : PolyFun (fun z : ℕ × ℕ => if z.2 = z.1 then (1 : ℕ) else 0) :=
    (PolyFun.ite he (polyFun_const 1) (polyFun_const 0)).of_eq (fun z => by simp)
  exact (upccCasePoly_m.pair upccCasePoly_localColors).comp (PolyFun.mapParam ht)

theorem upccCasePoly_row : PolyFun upccCaseRow := by
  let T := ((RawUpccCase × ℕ) × ℕ) × ℕ
  have hp : PolyFun (fun z : T => z.1.1.1.1) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst
  have hx : PolyFun (fun z : T => z.1.1.2) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_snd
  have hu : PolyFun (fun z : T => z.1.2) := polyFun_fst.comp polyFun_snd
  have hm : PolyFun (fun z : T => upccCaseM z.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp upccCasePoly_m
  have hc₁ := (((hp.pair (hx.pair hu)).comp polyFun_binColor).pair hm).comp polyFun_natEq
  have hc₂ := (((hp.pair (polyFun_snd.pair hu)).comp polyFun_binColor).pair hm).comp
    polyFun_natEq
  have ht : PolyFun (fun z : T => if binColor (z.1.1.1.1,(z.1.1.2,z.1.2)) =
      upccCaseM z.1.1 ∧ binColor (z.1.1.1.1,(z.2,z.1.2)) = upccCaseM z.1.1
      then (1 : ℕ) else 0) :=
    (PolyFun.ite (polyFun_rawJAnd hc₁ hc₂) (polyFun_const 1) (polyFun_const 0)).of_eq
      (fun z => by simp)
  have hb : PolyFun (fun z : (RawUpccCase × ℕ) × ℕ =>
      upccCaseBlock (z.1,upccCaseL z.1)) :=
    (polyFun_fst.pair (polyFun_fst.comp upccCasePoly_l)).comp upccCasePoly_block
  exact (polyFun_id.pair hb).comp (PolyFun.mapParam ht)

theorem upccCasePoly_graph : PolyFun upccCaseGraph := by
  have hl : PolyFun (fun z : RawUpccCase × ℕ => z.1.2.1) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_fst
  have hr := (polyFun_id.pair upccCasePoly_l).comp upccCasePoly_block
  exact hl.pair (hr.pair ((polyFun_id.pair hl).comp (PolyFun.mapParam upccCasePoly_row)))

theorem upccCasePoly_local : PolyFun upccCaseLocal := by
  have hl := (polyFun_id.pair upccCasePoly_m).comp upccCasePoly_link
  have hr := (polyFun_id.pair upccCasePoly_l).comp upccCasePoly_block
  exact hl.pair (hr.pair ((polyFun_id.pair hl).comp (PolyFun.mapParam upccCasePoly_row)))

namespace UpccCase

/-- Section 9.8, step 1: one version per vertex of the second part. -/
def widthF (r : RawUpccCase) : ℕ := r.2.2.length

/-- Section 9.8: individualize the named vertex and read the appropriate outcome.
An index outside the second part still has polynomial running time. -/
def versionF (z : RawUpccCase × ℕ) : RawUpccCaseOutcome :=
  if upccCaseSplits z then (z.1.2.1,upccCaseLocalColors z,none)
  else (z.1.2.1,upccCaseMarks z,some (upccCaseM z,upccCaseGraph z))

theorem polyFun_widthF : PolyFun widthF :=
  (polyFun_snd.comp polyFun_snd).comp polyFun_length

theorem polyFun_versionF : PolyFun versionF := by
  have hl : PolyFun (fun z : RawUpccCase × ℕ => z.1.2.1) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_fst
  exact PolyFun.ite upccCasePoly_splits
    (hl.pair (upccCasePoly_localColors.pair (polyFun_const none)))
    (hl.pair (upccCasePoly_marks.pair ((upccCasePoly_m.pair upccCasePoly_graph).comp polyFun_some)))

/-- Section 9.8: the indexed family has at most `n₂` raw values. -/
theorem versionFamily_card_le (r : RawUpccCase) :
    (Set.range (fun i : Fin (widthF r) => versionF (r,i))).ncard ≤ widthF r := by
  rw [← Set.image_univ]
  simpa only [Set.ncard_univ,Nat.card_fin] using
    Set.ncard_image_le (s := (Set.univ : Set (Fin (widthF r))))
      (f := fun i => versionF (r,i)) Set.finite_univ

end UpccCase
end Algo
