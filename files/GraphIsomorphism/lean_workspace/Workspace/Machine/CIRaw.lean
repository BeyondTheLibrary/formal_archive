import Workspace.Machine.CIInstance
import Workspace.Machine.GIRaw
import Workspace.Machine.Div

/-! # A polynomial raw constructor for Coset Intersection -/

namespace RAM.CIReduction

open Algo Targets Equiv Babai.CosetToString

abbrev RawCI := RawGens × RawGens × RawPerm × RawPerm

def rawOfCI {n : ℕ} (a : CIInput n) : RawCI :=
  (a.1.map (encPerm n), a.2.1.map (encPerm n), encPerm n a.2.2.1, encPerm n a.2.2.2)

theorem encode_rawOfCI {n : ℕ} (a : CIInput n) : Enc.encode (rawOfCI a) = Enc.encode a := by
  have hpair : ∀ {α β γ δ : Type} [Enc α] [Enc β] [Enc γ] [Enc δ]
      (x : α) (y : β) (z : γ) (w : δ),
      Enc.encode x = Enc.encode z → Enc.encode y = Enc.encode w →
        Enc.encode (x, y) = Enc.encode (z, w) := by
    intro α β γ δ _ _ _ _ x y z w hx hy
    change frame (Enc.encode x) ++ frame (Enc.encode y) =
      frame (Enc.encode z) ++ frame (Enc.encode w)
    rw [hx, hy]
  exact hpair _ _ _ _ (encode_gens_eq _ _).symm
    (hpair _ _ _ _ (encode_gens_eq _ _).symm
      (hpair _ _ _ _ (encode_perm_eq _ _).symm (encode_perm_eq _ _).symm))

/-- Enumerate the square domain using a list of vertices as fuel. -/
def points (r : RawPerm) : List ℕ :=
  List.range ((List.range r.length).product (List.range r.length)).length

@[simp] theorem points_eq (r : RawPerm) : points r = List.range (r.length * r.length) := by
  simp [points, List.product, List.length_flatMap, List.sum_replicate]

theorem polyFun_points : PolyFun points :=
  ((polyFun_rangeLength.pair polyFun_rangeLength).comp GIReduction.polyFun_product).comp
    polyFun_rangeLength

/-- One entry of the permutation induced by a pair of vertex permutations. -/
def actionEntry (p : (ℕ × (RawPerm × RawPerm)) × ℕ) : ℕ :=
  rawApply (p.1.2.2, p.2 % p.1.1) + p.1.1 * rawApply (p.1.2.1, p.2 / p.1.1)

theorem polyFun_actionEntry : PolyFun actionEntry := by
  have hn : PolyFun (fun p : (ℕ × (RawPerm × RawPerm)) × ℕ => p.1.1) :=
    polyFun_fst.comp polyFun_fst
  have hg : PolyFun (fun p : (ℕ × (RawPerm × RawPerm)) × ℕ => p.1.2.1) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_fst
  have hh : PolyFun (fun p : (ℕ × (RawPerm × RawPerm)) × ℕ => p.1.2.2) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_snd
  exact ((hh.pair (polyFun_snd.mod hn)).comp polyFun_rawApply).add
    (hn.mul ((hg.pair (polyFun_snd.div hn)).comp polyFun_rawApply))

/-- The whole induced permutation, with its degree taken from the fuel list. -/
def rawAction (p : RawPerm × (RawPerm × RawPerm)) : RawPerm :=
  (points p.1).map fun i => actionEntry ((p.1.length, p.2), i)

theorem polyFun_rawAction : PolyFun rawAction :=
  (((polyFun_fst.comp polyFun_length).pair polyFun_snd).pair
    (polyFun_fst.comp polyFun_points)).comp polyFun_actionEntry.mapParam

/-- Lift a generator from either factor. The Boolean chooses the first factor. -/
def liftGen (p : (RawPerm × Bool) × RawPerm) : RawPerm :=
  if p.1.2 then rawAction (p.1.1, p.2, rawOne p.1.1)
  else rawAction (p.1.1, rawOne p.1.1, p.2)

theorem polyFun_liftGen : PolyFun liftGen := by
  have hr : PolyFun (fun p : (RawPerm × Bool) × RawPerm => p.1.1) :=
    polyFun_fst.comp polyFun_fst
  exact PolyFun.ite (polyFun_fst.comp polyFun_snd)
    ((hr.pair (polyFun_snd.pair (hr.comp polyFun_rawOne))).comp polyFun_rawAction)
    ((hr.pair ((hr.comp polyFun_rawOne).pair polyFun_snd)).comp polyFun_rawAction)

/-- Test whether a numbered pair belongs to the graph of the given permutation. -/
def bitEntry (p : (ℕ × RawPerm) × ℕ) : ℕ :=
  if p.2 % p.1.1 = rawApply (p.1.2, p.2 / p.1.1) then 1 else 0

theorem polyFun_bitEntry : PolyFun bitEntry := by
  have hn : PolyFun (fun p : (ℕ × RawPerm) × ℕ => p.1.1) := polyFun_fst.comp polyFun_fst
  have hv : PolyFun (fun p : (ℕ × RawPerm) × ℕ => rawApply (p.1.2, p.2 / p.1.1)) :=
    ((polyFun_fst.comp polyFun_snd).pair (polyFun_snd.div hn)).comp polyFun_rawApply
  exact (PolyFun.ite (((polyFun_snd.mod hn).pair hv).comp polyFun_natEq)
    (polyFun_const 1) (polyFun_const 0)).of_eq (fun p => by simp [bitEntry])

def rawString (p : RawPerm × RawPerm) : RawStr :=
  (points p.1).map fun i => bitEntry ((p.1.length, p.2), i)

theorem polyFun_rawString : PolyFun rawString :=
  (((polyFun_fst.comp polyFun_length).pair polyFun_snd).pair
    (polyFun_fst.comp polyFun_points)).comp polyFun_bitEntry.mapParam

/-- Build the SI instance. Its first string marks the diagonal. -/
def build (a : RawCI) : RawSI :=
  (a.1.map (fun g => liftGen ((a.2.2.1, true), g)) ++
    a.2.1.map (fun h => liftGen ((a.2.2.1, false), h)),
    rawString (a.2.2.1, rawOne a.2.2.1),
    rawString (a.2.2.1, rawMul (rawInv a.2.2.2, a.2.2.1)))

/-- Polynomial on all inputs: the square domain is generated from a list length. -/
theorem polyFun_build : PolyFun build := by
  have hr : PolyFun (fun a : RawCI => a.2.2.1) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_fst
  have ht : PolyFun (fun a : RawCI => a.2.2.2) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_snd
  have hg := ((hr.pair (polyFun_const true)).pair polyFun_fst).comp polyFun_liftGen.mapParam
  have hh := ((hr.pair (polyFun_const false)).pair (polyFun_snd.comp polyFun_fst)).comp
    polyFun_liftGen.mapParam
  have hx := (hr.pair (hr.comp polyFun_rawOne)).comp polyFun_rawString
  have hy := (hr.pair (((ht.comp polyFun_rawInv).pair hr).comp polyFun_rawMul)).comp polyFun_rawString
  exact ((hg.pair hh).comp polyFun_append).pair (hx.pair hy)

theorem actionEntry_spec {n : ℕ} (g h : Perm (Fin n)) (i : Fin (n * n)) :
    actionEntry ((n, encPerm n g, encPerm n h), i.val) = (action n (g, h) i).val := by
  have h₁ : i.val / n < n := (finProdFinEquiv.symm i).1.isLt
  have h₂ : i.val % n < n := (finProdFinEquiv.symm i).2.isLt
  rw [actionEntry, rawApply_encPerm _ _ h₂, rawApply_encPerm _ _ h₁]
  rfl

theorem rawAction_spec {n : ℕ} (r g h : Perm (Fin n)) :
    rawAction (encPerm n r, encPerm n g, encPerm n h) = encPerm (n * n) (action n (g, h)) := by
  apply List.ext_getElem
  · simp [rawAction, encPerm]
  · intro i hi hi'
    have hin : i < n * n := by simpa [rawAction] using hi
    simpa only [rawAction, points_eq, length_encPerm, List.getElem_map, List.getElem_range,
      encPerm, List.length_ofFn, List.getElem_ofFn] using actionEntry_spec g h ⟨i, hin⟩

theorem rawString_spec {n : ℕ} (r σ : Perm (Fin n)) :
    rawString (encPerm n r, encPerm n σ) = encStr (graphString σ ∘ finProdFinEquiv.symm) := by
  classical
  apply List.ext_getElem
  · simp [rawString, encStr]
  · intro i hi hi'
    have hin : i < n * n := by simpa [rawString] using hi
    have h₁ : i / n < n := (finProdFinEquiv.symm (⟨i, hin⟩ : Fin (n * n))).1.isLt
    simp only [rawString, points_eq, length_encPerm, List.getElem_map, List.getElem_range]
    rw [bitEntry, rawApply_encPerm _ _ h₁]
    simp only [encStr, List.getElem_ofFn, Function.comp_def, graphString, Fin.ext_iff]
    change (if i % n = (σ ⟨i / n, h₁⟩).val then 1 else 0) =
      (if i % n = (σ ⟨i / n, h₁⟩).val then (1 : Fin 2) else 0).val
    split <;> rfl

theorem build_spec {n : ℕ} (a : CIInput n) : build (rawOfCI a) = rawOfSI (instanceSI a) := by
  have hone : rawOne (encPerm n a.2.2.1) = encPerm n 1 := by simp [rawOne, encPerm_one]
  simp only [build, rawOfCI, hone, rawInv_encPerm, rawMul_encPerm, rawString_spec,
    rawOfSI, instanceSI, gens, List.map_append, List.map_map]
  congr 2
  · apply List.map_congr_left
    intro g hg
    simpa [liftGen, hone] using rawAction_spec a.2.2.1 g 1
  · apply List.map_congr_left
    intro h hh
    simpa [liftGen, hone] using rawAction_spec a.2.2.1 1 h

end RAM.CIReduction

#print axioms RAM.CIReduction.build_spec
