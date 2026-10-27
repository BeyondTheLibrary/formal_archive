import Workspace.Machine.GIPairs
import Workspace.Machine.TargetsGI
import Workspace.Algo.Perm
import Workspace.Machine.ListOps3

/-!
# Building the GI instance on raw lists

All loops run over input lists or products of those lists. Thus the constructor
has polynomial time and size bounds even on matrices that are not square or binary.
The specification is needed only for adjacency matrices.
-/

namespace RAM.GIReduction

open Algo Babai.GraphToString

abbrev Matrix := List (List ℕ)
abbrev RawGI := Matrix × Matrix

/-- Pair positions, enumerated using the number of rows. -/
def rawPairs (M : Matrix) : List (ℕ × ℕ) := pairList M.length

theorem polyFun_product {α β : Type*} [Enc α] [Enc β] :
    PolyFun (fun p : List α × List β => p.1.product p.2) := by
  have h : PolyFun (fun p : List β × α => p.1.map (fun b => (p.2, b))) :=
    (polyFun_snd.pair polyFun_fst).comp (PolyFun.mapParam (polyFun_fst.pair polyFun_snd))
  exact ((polyFun_snd.pair polyFun_fst).comp h.flatMapParam).of_eq (fun _ => rfl)

theorem polyFun_lt : PolyFun (fun p : ℕ × ℕ => decide (p.1 < p.2)) :=
  ((polyFun_fst.add (polyFun_const 1)).le polyFun_snd).of_eq
    (fun p => by simp [Nat.succ_le_iff])

theorem polyFun_rawPairs : PolyFun rawPairs := by
  have h : PolyFun (fun M : Matrix => (List.range M.length).product (List.range M.length)) :=
    (polyFun_rangeLength.pair polyFun_rangeLength).comp polyFun_product
  exact h.comp (PolyFun.filter polyFun_lt)

/-- Sort the two images so that the smaller endpoint comes first. -/
def rawPairImage (p : RawPerm × (ℕ × ℕ)) : ℕ × ℕ :=
  (min (rawApply (p.1, p.2.1)) (rawApply (p.1, p.2.2)),
   max (rawApply (p.1, p.2.1)) (rawApply (p.1, p.2.2)))

theorem polyFun_rawPairImage : PolyFun rawPairImage := by
  have h₁ : PolyFun (fun p : RawPerm × (ℕ × ℕ) => rawApply (p.1, p.2.1)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_rawApply
  have h₂ : PolyFun (fun p : RawPerm × (ℕ × ℕ) => rawApply (p.1, p.2.2)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_rawApply
  exact (h₁.min' h₂).pair (h₁.max' h₂)

theorem polyFun_pairEq :
    PolyFun (fun p : (ℕ × ℕ) × (ℕ × ℕ) => decide (p.1 = p.2)) := by
  have h₁ : PolyFun (fun p : (ℕ × ℕ) × (ℕ × ℕ) => decide (p.1.1 = p.2.1)) :=
    ((polyFun_fst.comp polyFun_fst).pair (polyFun_snd.comp polyFun_fst)).comp polyFun_natEq
  have h₂ : PolyFun (fun p : (ℕ × ℕ) × (ℕ × ℕ) => decide (p.1.2 = p.2.2)) :=
    ((polyFun_fst.comp polyFun_snd).pair (polyFun_snd.comp polyFun_snd)).comp polyFun_natEq
  exact (PolyFun.ite h₁ h₂ (polyFun_const false)).of_eq (fun p => by
    by_cases h : p.1.1 = p.2.1 <;> simp [h, Prod.ext_iff])

/-- Find a pair's index in the enumeration. The default handles malformed data. -/
def pairLookup (p : List ((ℕ × ℕ) × ℕ) × (ℕ × ℕ)) : ℕ :=
  (p.1.lookup p.2).getD 0

theorem polyFun_pairLookup : PolyFun pairLookup :=
  (((polyFun_listLookup polyFun_pairEq).pair (polyFun_const 0)).comp polyFun_optionGetD)

/-- The permutation induced on the numbered pairs. -/
def rawPairPerm (p : List (ℕ × ℕ) × RawPerm) : RawPerm :=
  p.1.map fun q => pairLookup (p.1.zipIdx, rawPairImage (p.2, q))

theorem polyFun_rawPairPerm : PolyFun rawPairPerm := by
  have h : PolyFun (fun p : (List (ℕ × ℕ) × RawPerm) × (ℕ × ℕ) =>
      pairLookup (p.1.1.zipIdx, rawPairImage (p.1.2, p.2))) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_zipIdx).pair
      (((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp polyFun_rawPairImage)).comp
      polyFun_pairLookup
  exact (polyFun_id.pair polyFun_fst).comp h.mapParam

/-- The cycle sends the last vertex to zero. -/
def rotateEntry (p : ℕ × ℕ) : ℕ := if p.2 + 1 < p.1 then p.2 + 1 else 0

theorem polyFun_rotateEntry : PolyFun rotateEntry :=
  (PolyFun.ite (((polyFun_snd.add (polyFun_const 1)).pair polyFun_fst).comp polyFun_lt)
    (polyFun_snd.add (polyFun_const 1)) (polyFun_const 0)).of_eq (fun p => by
      simp only [rotateEntry, decide_eq_true_eq])

/-- The adjacent transposition exchanges zero and one. -/
def swapEntry (i : ℕ) : ℕ := if i = 0 then 1 else if i = 1 then 0 else i

theorem polyFun_swapEntry : PolyFun swapEntry :=
  (PolyFun.ite ((polyFun_id.pair (polyFun_const 0)).comp polyFun_natEq)
    (polyFun_const 1)
    (PolyFun.ite ((polyFun_id.pair (polyFun_const 1)).comp polyFun_natEq)
      (polyFun_const 0) polyFun_id)).of_eq (fun i => by simp [swapEntry])

/-- The two vertex generators, as arrays of images. -/
def rawVertexGens (M : Matrix) : RawGens :=
  if 2 ≤ M.length then
    [(List.range M.length).map (fun i => rotateEntry (M.length, i)),
      (List.range M.length).map swapEntry]
  else []

theorem polyFun_rawVertexGens : PolyFun rawVertexGens := by
  have hc : PolyFun (fun M : Matrix =>
      (List.range M.length).map (fun i => rotateEntry (M.length, i))) :=
    (polyFun_length.pair polyFun_rangeLength).comp polyFun_rotateEntry.mapParam
  have hs : PolyFun (fun M : Matrix => (List.range M.length).map swapEntry) :=
    polyFun_rangeLength.comp (PolyFun.map polyFun_swapEntry)
  have hg : PolyFun (fun M : Matrix =>
      [(List.range M.length).map (fun i => rotateEntry (M.length, i)),
        (List.range M.length).map swapEntry]) :=
    (hc.pair ((hs.pair (polyFun_const [])).comp polyFun_cons)).comp polyFun_cons
  exact (PolyFun.ite ((polyFun_const 2).le polyFun_length) hg (polyFun_const [])).of_eq
    (fun M => by simp [rawVertexGens])

/-- Read the bit at a pair of endpoints. -/
def matrixEntry (p : Matrix × (ℕ × ℕ)) : ℕ := (p.1.getD p.2.1 []).getD p.2.2 0

theorem polyFun_matrixEntry : PolyFun matrixEntry := by
  have hr : PolyFun (fun p : Matrix × (ℕ × ℕ) => p.1.getD p.2.1 []) :=
    (((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).pair (polyFun_const [])).comp polyFun_getD)
  exact (((hr.pair (polyFun_snd.comp polyFun_snd)).pair (polyFun_const 0)).comp polyFun_getD)

/-- Build the binary SI instance and its two induced generators. -/
def build (a : RawGI) : RawSI :=
  ((rawVertexGens a.1).map (fun g => rawPairPerm (rawPairs a.1, g)),
    (rawPairs a.1).map (fun p => matrixEntry (a.1, p)),
    (rawPairs a.1).map (fun p => matrixEntry (a.2, p)))

/-- The constructor is polynomial on every raw input, including malformed matrices. -/
theorem polyFun_build : PolyFun build := by
  have hp : PolyFun (fun a : RawGI => rawPairs a.1) := polyFun_fst.comp polyFun_rawPairs
  have hg : PolyFun (fun a : RawGI =>
      (rawVertexGens a.1).map (fun g => rawPairPerm (rawPairs a.1, g))) :=
    (hp.pair (polyFun_fst.comp polyFun_rawVertexGens)).comp polyFun_rawPairPerm.mapParam
  exact hg.pair (((polyFun_fst.pair hp).comp polyFun_matrixEntry.mapParam).pair
    ((polyFun_snd.pair hp).comp polyFun_matrixEntry.mapParam))

end RAM.GIReduction
