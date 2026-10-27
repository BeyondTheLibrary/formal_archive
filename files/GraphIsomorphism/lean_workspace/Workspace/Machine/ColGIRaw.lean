import Workspace.Machine.ColGIInstance
import Workspace.Machine.CIRaw
import Workspace.Machine.GISpec

/-!
# Corollary 1.1.4: the raw constructor of the colored-GI SI instance

The machine reads a vertex-colored GI instance as two adjacency matrices and two color arrays
(`RAM.Targets.ColGIInput.raw`). This file builds, from those four lists, the raw form of the SI
instance `RAM.ColGIReduction.instanceSI`: the induced generators on ordered pairs and the two
strings. Every loop runs over the concatenated color array or over its square, so the
constructor is polynomial on every raw input (`RAM.ColGIReduction.polyFun_build`); the
specification `RAM.ColGIReduction.build_spec` is needed only on real inputs.
-/

namespace RAM.ColGIReduction

open Algo Targets Equiv Babai
open GIReduction (Matrix matrixEntry polyFun_matrixEntry polyFun_lt)
open CIReduction (points polyFun_points rawAction polyFun_rawAction)

/-- The raw colored-GI input. -/
abbrev RawCol := Matrix × Matrix × List ℕ × List ℕ

/-- The combined color array: first the colors of `X`, then those of `Y`. -/
def colList (r : RawCol) : List ℕ := r.2.2.1 ++ r.2.2.2

theorem polyFun_colList : PolyFun colList :=
  ((((polyFun_snd.comp polyFun_snd).comp polyFun_fst)).pair
    ((polyFun_snd.comp polyFun_snd).comp polyFun_snd)).comp polyFun_append

/-- The image of a point under the transposition of two points. -/
def swapImage (p : (ℕ × ℕ) × ℕ) : ℕ :=
  if p.2 = p.1.1 then p.1.2 else if p.2 = p.1.2 then p.1.1 else p.2

theorem polyFun_swapImage : PolyFun swapImage :=
  (PolyFun.ite (polyFun_snd.natEq (polyFun_fst.comp polyFun_fst)) (polyFun_fst.comp polyFun_snd)
    (PolyFun.ite (polyFun_snd.natEq (polyFun_fst.comp polyFun_snd))
      (polyFun_fst.comp polyFun_fst) polyFun_snd)).of_eq (fun p => by simp [swapImage])

/-- The generator of number `i`: the transposition of the points `i / N` and `i % N` when they
have the same color, the identity otherwise (`RAM.ColGIReduction.swp`). -/
def rawSwp (p : List ℕ × ℕ) : RawPerm :=
  if p.1.getD (p.2 / p.1.length) 0 = p.1.getD (p.2 % p.1.length) 0 then
    (List.range p.1.length).map fun ω => swapImage ((p.2 / p.1.length, p.2 % p.1.length), ω)
  else List.range p.1.length

theorem polyFun_rawSwp : PolyFun rawSwp := by
  have hL : PolyFun (fun p : List ℕ × ℕ => p.1.length) := polyFun_fst.comp polyFun_length
  have hU : PolyFun (fun p : List ℕ × ℕ => p.2 / p.1.length) := polyFun_snd.div hL
  have hV : PolyFun (fun p : List ℕ × ℕ => p.2 % p.1.length) := polyFun_snd.mod hL
  have hcU : PolyFun (fun p : List ℕ × ℕ => p.1.getD (p.2 / p.1.length) 0) :=
    ((polyFun_fst.pair hU).pair (polyFun_const 0)).comp polyFun_getD
  have hcV : PolyFun (fun p : List ℕ × ℕ => p.1.getD (p.2 % p.1.length) 0) :=
    ((polyFun_fst.pair hV).pair (polyFun_const 0)).comp polyFun_getD
  have hR : PolyFun (fun p : List ℕ × ℕ => List.range p.1.length) :=
    polyFun_fst.comp polyFun_rangeLength
  have hM := ((hU.pair hV).pair hR).comp polyFun_swapImage.mapParam
  exact (PolyFun.ite (hcU.natEq hcV) hM hR).of_eq (fun p => by simp [rawSwp])

/-- The generator of number `i`, acting on ordered pairs. -/
def rawGen (p : List ℕ × ℕ) : RawPerm := rawAction (rawOne p.1, rawSwp p, rawSwp p)

theorem polyFun_rawGen : PolyFun rawGen :=
  ((polyFun_fst.comp polyFun_rawOne).pair (polyFun_rawSwp.pair polyFun_rawSwp)).comp
    polyFun_rawAction

/-- The parameters of the string entries: the two matrices, `n`, `N = 2n`, and the two
diagonal marks. -/
abbrev StrParam := (Matrix × Matrix) × ((ℕ × ℕ) × (ℕ × ℕ))

/-- The letter at the pair of number `i` (`RAM.ColGIReduction.letter`). -/
def strEntry (p : StrParam × ℕ) : ℕ :=
  if p.2 / p.1.2.1.2 < p.1.2.1.1 then
    (if p.2 % p.1.2.1.2 < p.1.2.1.1 then
      (if p.2 / p.1.2.1.2 = p.2 % p.1.2.1.2 then p.1.2.2.1
        else matrixEntry (p.1.1.1, (p.2 / p.1.2.1.2, p.2 % p.1.2.1.2)))
     else 0)
  else if p.2 % p.1.2.1.2 < p.1.2.1.1 then 0
  else if p.2 / p.1.2.1.2 = p.2 % p.1.2.1.2 then p.1.2.2.2
  else matrixEntry (p.1.1.2, (p.2 / p.1.2.1.2 - p.1.2.1.1, p.2 % p.1.2.1.2 - p.1.2.1.1))

theorem polyFun_strEntry : PolyFun strEntry := by
  have hn : PolyFun (fun p : StrParam × ℕ => p.1.2.1.1) :=
    ((polyFun_fst.comp polyFun_snd).comp polyFun_fst).comp polyFun_fst
  have hN : PolyFun (fun p : StrParam × ℕ => p.1.2.1.2) :=
    ((polyFun_fst.comp polyFun_snd).comp polyFun_fst).comp polyFun_snd
  have hd1 : PolyFun (fun p : StrParam × ℕ => p.1.2.2.1) :=
    ((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hd2 : PolyFun (fun p : StrParam × ℕ => p.1.2.2.2) :=
    ((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd
  have hMX : PolyFun (fun p : StrParam × ℕ => p.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have hMY : PolyFun (fun p : StrParam × ℕ => p.1.1.2) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_snd
  have hu := polyFun_snd.div hN
  have hv := polyFun_snd.mod hN
  have hut : PolyFun (fun p : StrParam × ℕ => decide (p.2 / p.1.2.1.2 < p.1.2.1.1)) :=
    (hu.pair hn).comp polyFun_lt
  have hvt : PolyFun (fun p : StrParam × ℕ => decide (p.2 % p.1.2.1.2 < p.1.2.1.1)) :=
    (hv.pair hn).comp polyFun_lt
  have hX := (hMX.pair (hu.pair hv)).comp polyFun_matrixEntry
  have hY := (hMY.pair ((hu.sub hn).pair (hv.sub hn))).comp polyFun_matrixEntry
  exact (PolyFun.ite hut
    (PolyFun.ite hvt (PolyFun.ite (hu.natEq hv) hd1 hX) (polyFun_const 0))
    (PolyFun.ite hvt (polyFun_const 0) (PolyFun.ite (hu.natEq hv) hd2 hY))).of_eq
    (fun p => by simp [strEntry])

/-- The string parameters of a raw input. -/
def strParam (r : RawCol) (d₁ d₂ : ℕ) : StrParam :=
  ((r.1, r.2.1), ((r.2.2.1.length, (colList r).length), (d₁, d₂)))

theorem polyFun_strParam (d₁ d₂ : ℕ) : PolyFun (fun r : RawCol => strParam r d₁ d₂) :=
  (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).pair
    ((((polyFun_snd.comp polyFun_snd).comp polyFun_fst).comp polyFun_length).pair
      (polyFun_colList.comp polyFun_length) |>.pair (polyFun_const (d₁, d₂)))

/-- **The raw constructor.** -/
def build (r : RawCol) : RawSI :=
  ((points (colList r)).map (fun i => rawGen (colList r, i)),
    (points (colList r)).map (fun i => strEntry (strParam r 2 3, i)),
    (points (colList r)).map (fun i => strEntry (strParam r 3 2, i)))

theorem polyFun_build : PolyFun build := by
  have hP : PolyFun (fun r : RawCol => points (colList r)) := polyFun_colList.comp polyFun_points
  have hG := (polyFun_colList.pair hP).comp polyFun_rawGen.mapParam
  have hx := ((polyFun_strParam 2 3).pair hP).comp polyFun_strEntry.mapParam
  have hy := ((polyFun_strParam 3 2).pair hP).comp polyFun_strEntry.mapParam
  exact hG.pair (hx.pair hy)

/-! ## The specification -/

variable {n : ℕ}

theorem colList_raw (a : ColGIInput n) :
    colList a.raw = List.ofFn fun ω : Fin (n + n) => (col a ω : ℕ) := by
  rw [List.ofFn_add]
  simp only [colList, ColGIInput.raw, col, Fin.append_left', Fin.append_right]

theorem length_colList_raw (a : ColGIInput n) : (colList a.raw).length = n + n := by
  rw [colList_raw, List.length_ofFn]

theorem getD_colList_raw (a : ColGIInput n) (ω : Fin (n + n)) :
    (colList a.raw).getD ω 0 = (col a ω : ℕ) := by
  rw [colList_raw, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem div_val (i : Fin ((n + n) * (n + n))) :
    (i : ℕ) / (n + n) = ((finProdFinEquiv.symm i).1 : ℕ) := rfl

theorem mod_val (i : Fin ((n + n) * (n + n))) :
    (i : ℕ) % (n + n) = ((finProdFinEquiv.symm i).2 : ℕ) := rfl

theorem rawSwp_spec (a : ColGIInput n) (i : Fin ((n + n) * (n + n))) :
    rawSwp (colList a.raw, i) =
      encPerm (n + n) (swp a (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) := by
  set u := (finProdFinEquiv.symm i).1
  set v := (finProdFinEquiv.symm i).2
  simp only [rawSwp, length_colList_raw, div_val, mod_val]
  rw [getD_colList_raw a u, getD_colList_raw a v, swp]
  by_cases h : col a u = col a v
  · rw [if_pos (congrArg Fin.val h), if_pos h]
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      simp only [List.getElem_map, List.getElem_range, encPerm, List.getElem_ofFn, swapImage]
      have hk : k < n + n := by simpa using h1
      rw [swap_apply_def]
      by_cases hku : (⟨k, hk⟩ : Fin (n + n)) = u
      · rw [if_pos hku, if_pos (congrArg Fin.val hku)]
      · rw [if_neg hku, if_neg (fun h => hku (Fin.ext h))]
        by_cases hkv : (⟨k, hk⟩ : Fin (n + n)) = v
        · rw [if_pos hkv, if_pos (congrArg Fin.val hkv)]
        · rw [if_neg hkv, if_neg (fun h => hkv (Fin.ext h))]
  · rw [if_neg (fun h' => h (Fin.ext h')), if_neg h, encPerm_one]

theorem rawGen_spec (a : ColGIInput n) (i : Fin ((n + n) * (n + n))) :
    rawGen (colList a.raw, i) =
      encPerm ((n + n) * (n + n))
        (pairHom (swp a (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)) := by
  have hone : rawOne (colList a.raw) = encPerm (n + n) 1 := by
    rw [rawOne, length_colList_raw, encPerm_one]
  rw [rawGen, hone, rawSwp_spec]
  exact CIReduction.rawAction_spec 1 _ _

/-- The diagonal marks of `RAM.ColGIReduction.letter`. -/
def marks (mark : Bool) : ℕ × ℕ := if mark then (2, 3) else (3, 2)

theorem strEntry_spec (a : ColGIInput n) (mark : Bool) (i : Fin ((n + n) * (n + n))) :
    strEntry (strParam a.raw (marks mark).1 (marks mark).2, i) = (pairStr a mark i : ℕ) := by
  have hn : a.raw.2.2.1.length = n := by simp [ColGIInput.raw]
  simp only [strEntry, strParam, hn, length_colList_raw, div_val, mod_val, pairStr]
  set u := (finProdFinEquiv.symm i).1
  set v := (finProdFinEquiv.symm i).2
  have hX : a.raw.1 = graphMatrix a.X := rfl
  have hY : a.raw.2.1 = graphMatrix a.Y := rfl
  rw [hX, hY]
  clear_value u v
  induction u using Fin.addCases with
  | left u =>
    induction v using Fin.addCases with
    | left v =>
      simp only [Fin.val_castAdd, u.isLt, v.isLt, if_true, side,
        finSumFinEquiv_symm_apply_castAdd, letter, Fin.val_inj]
      by_cases huv : u = v
      · subst huv; cases mark <;> simp [marks]
      · rw [if_neg huv, if_neg huv, GIReduction.matrixEntry_graphMatrix]
        split <;> rfl
    | right v =>
      simp only [Fin.val_castAdd, Fin.val_natAdd, u.isLt, if_true, side,
        finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, letter]
      rw [if_neg (by omega)]
      rfl
  | right u =>
    induction v using Fin.addCases with
    | left v =>
      simp only [Fin.val_castAdd, Fin.val_natAdd, v.isLt, if_true, side,
        finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, letter]
      rw [if_neg (by omega)]
      rfl
    | right v =>
      simp only [Fin.val_natAdd, side, finSumFinEquiv_symm_apply_natAdd, letter]
      rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left,
        Nat.add_sub_cancel_left]
      by_cases huv : u = v
      · subst huv; cases mark <;> simp [marks]
      · have huv' : n + (u : ℕ) ≠ n + v := fun h => huv (Fin.ext (by omega))
        rw [if_neg huv', if_neg huv, GIReduction.matrixEntry_graphMatrix]
        split <;> rfl

/-- **The raw constructor meets its specification** on every real input. -/
theorem build_spec (a : ColGIInput n) : build a.raw = rawOfSI (instanceSI a) := by
  have hlen : (colList a.raw).length * (colList a.raw).length = (n + n) * (n + n) := by
    rw [length_colList_raw]
  simp only [build, rawOfSI, instanceSI]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply List.ext_getElem
    · simp [hlen, vertexGens]
    · intro k h1 h2
      have hk : k < (n + n) * (n + n) := by simpa [hlen] using h1
      simp only [List.getElem_map, CIReduction.points_eq, List.getElem_range, vertexGens,
        List.getElem_ofFn]
      exact rawGen_spec a ⟨k, hk⟩
  · apply List.ext_getElem
    · simp [hlen, encStr]
    · intro k h1 h2
      have hk : k < (n + n) * (n + n) := by simpa [hlen] using h1
      simp only [List.getElem_map, CIReduction.points_eq, List.getElem_range, encStr,
        List.getElem_ofFn]
      exact strEntry_spec a true ⟨k, hk⟩
  · apply List.ext_getElem
    · simp [hlen, encStr]
    · intro k h1 h2
      have hk : k < (n + n) * (n + n) := by simpa [hlen] using h1
      simp only [List.getElem_map, CIReduction.points_eq, List.getElem_range, encStr,
        List.getElem_ofFn]
      exact strEntry_spec a false ⟨k, hk⟩

theorem encode_instanceSI (a : ColGIInput n) :
    Enc.encode (instanceSI a) = Enc.encode (build a.raw) := by
  rw [build_spec]; exact encode_si_eq _

end RAM.ColGIReduction
