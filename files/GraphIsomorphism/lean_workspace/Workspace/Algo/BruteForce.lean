/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the brute force of §11.3, Reduce-to-Johnson, line 2.
-/
import Workspace.Algo.Coset
import Workspace.Algo.Stabilizer
import Workspace.Algo.Luks

/-!
# Line 2 of Procedure Reduce-to-Johnson: brute force for a small group

§11.3, line 5045: *"if `|G| < C₀` for some absolute constant `C₀` then compute `Iso_G(x,y)` by
brute force"*.  The paper cites no source, so `Workspace/Algo/DESIGN.md`, item 2, lists this as
a **class-B** item, to be proved.  This file is that proof.

## The routine

Enumerating the group is a special case of a routine the algorithmic layer already has.
`Algo.rawCosetReps` of `Workspace/Algo/Coset.lean` lists right coset representatives of `H` in
`G` by a breadth-first search on the Cayley graph, with the number of rounds supplied in unary.
For `H = 1` the right cosets are the elements, so

```
Algo.rawGroupElems ((dom, gens), js) = Algo.rawCosetReps ((dom, gens), ([], js))
```

lists the elements of `G`, each exactly once, and lists all of them as soon as
`|G| ≤ js.length + 1` (`Algo.mem_rawGroupElems`, `Algo.decPerm_mem_genGroup_of_mem`).  The
unary bound `js` is part of the input, so the routine is a `RAM.PolyFun` outright: its running
time is polynomial in `|G|` and the size of the instance, which is the paper's `|G|·poly(n)`.

`Algo.rawBrute` then filters the enumeration twice — once for `Iso_G(x,y)`, once for
`Aut_G(x) = Iso_G(x,x)` — and returns the answer in the `Algo.RawCoset` encoding of
Definition 11.1.2: `none` when there is no isomorphism, and otherwise a generating list of
`Aut_G(x)`, shortened to at most `n²` entries by `Algo.rawShorten`, together with one
representative.

## Main definitions

`Algo.rawGroupElems`, `Algo.rawIsoTest`, `Algo.rawBrute`.

## Main results

* `Algo.mem_rawGroupElems`, `Algo.decPerm_mem_genGroup_of_mem` — the enumeration is exactly `G`;
* `Algo.rawBrute_eq_none_iff` — `none` exactly when `Iso_G(x,y) = ∅`;
* `Algo.rawBrute_spec` — in the other case the representative lies in `Iso_G(x,y)` and the
  generating list generates `Aut_G(x)`: this is `RAM.Targets.SIRel`;
* `Algo.polyFun_rawBrute` — the running time.

No axiom, no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

variable {n : ℕ}

/-! ## Enumerating the group -/

/-- **The elements of a group given by generators**, listed once each: the right coset
representatives of the trivial subgroup.  The number of rounds is `js.length`, in unary. -/
def rawGroupElems (p : (List ℕ × RawGens) × List ℕ) : RawGens :=
  rawCosetReps ((p.1.1, p.1.2), (([] : RawGens), p.2))

section Enum

variable {dom : List ℕ} {gens : List (Perm (Fin n))} {js : List ℕ}

theorem genGroup_nil : genGroup ([] : List (Perm (Fin n))) = ⊥ := by
  have h : {g : Perm (Fin n) | g ∈ ([] : List (Perm (Fin n)))} = ∅ := by
    ext g
    simp
  rw [genGroup, h, Subgroup.closure_empty]

theorem rawGroupElems_eq :
    rawGroupElems ((dom, gens.map (encPerm n)), js)
      = rawCosetReps ((dom, gens.map (encPerm n)),
          (([] : List (Perm (Fin n))).map (encPerm n), js)) := by
  rw [rawGroupElems, List.map_nil]

/-- **Every listed element is an element of the group**, and is a well-formed permutation. -/
theorem decPerm_mem_genGroup_of_mem (hdom : dom.length = n) {r : RawPerm}
    (hr : r ∈ rawGroupElems ((dom, gens.map (encPerm n)), js)) :
    RawPerm.WF n r ∧ decPerm n r ∈ genGroup gens := by
  have hsound := rawCosetReps_sound (gensG := gens) (gensH := ([] : List (Perm (Fin n))))
    (js := js) hdom
  rw [← rawGroupElems_eq] at hsound
  exact hsound.1 r hr

/-- **Every element of the group is listed**, once the unary bound reaches `|G|`. -/
theorem mem_rawGroupElems (hdom : dom.length = n)
    (hidx : Nat.card (genGroup gens) ≤ js.length + 1) {σ : Perm (Fin n)}
    (hσ : σ ∈ genGroup gens) :
    ∃ r ∈ rawGroupElems ((dom, gens.map (encPerm n)), js), decPerm n r = σ := by
  have hrel : (genGroup ([] : List (Perm (Fin n)))).relIndex (genGroup gens) ≤ js.length + 1 := by
    rw [genGroup_nil, Subgroup.relIndex_bot_left]
    exact hidx
  have hcov := rawCosetReps_cover (dom := dom) (gensG := gens)
    (gensH := ([] : List (Perm (Fin n)))) (js := js) hdom hrel σ hσ
  rw [← rawGroupElems_eq] at hcov
  obtain ⟨r, hr, hmem⟩ := hcov
  refine ⟨r, hr, ?_⟩
  rw [genGroup_nil, Subgroup.mem_bot] at hmem
  exact (mul_inv_eq_one.1 hmem).symm

end Enum

/-- The head of a list that is not empty is an entry of it. -/
theorem headD_mem_of_not_isEmpty {α : Type*} {l : List α} (d : α) (h : ¬ l.isEmpty = true) :
    l.headD d ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => exact List.mem_cons_self ..

/-! ## The test, and the routine -/

/-- **The test `τ ∈ Iso_G(x,y)`**: `x(u) = y(τ(u))` for every point, which is
`y^{τ⁻¹} = x` in the notation of Eq. (55). -/
def rawIsoTest (p : (RawStr × RawStr) × RawPerm) : Bool :=
  decide (rawStrAct (rawInv p.2, p.1.2) = p.1.1)

/-- The isomorphisms among the listed elements. -/
def rawIsoList (p : ((List ℕ × RawGens) × List ℕ) × (RawStr × RawStr)) : RawGens :=
  (rawGroupElems p.1).filter (fun r => rawIsoTest (p.2, r))

/-- The automorphisms among the listed elements. -/
def rawAutList (p : ((List ℕ × RawGens) × List ℕ) × (RawStr × RawStr)) : RawGens :=
  (rawGroupElems p.1).filter (fun r => rawIsoTest ((p.2.1, p.2.1), r))

/-- **Line 2 of Procedure Reduce-to-Johnson** (§11.3, line 5045): `Iso_G(x,y)` by brute
force. -/
def rawBrute (p : ((List ℕ × RawGens) × List ℕ) × (RawStr × RawStr)) : RawCoset :=
  if (rawIsoList p).isEmpty then none
  else some (rawShorten (p.1.1.1, rawAutList p), (rawIsoList p).headD (rawOne p.1.1.1))

/-! ## The specification -/

section Spec

variable {s : ℕ} {dom : List ℕ} {gens : List (Perm (Fin n))} {js : List ℕ}
  {x y : Fin n → Fin s}

theorem encStr_injective : Function.Injective (encStr : (Fin n → Fin s) → RawStr) := by
  intro a b h
  funext i
  have h1 : rawGet (encStr a, (i : ℕ)) = rawGet (encStr b, (i : ℕ)) := by rw [h]
  rw [rawGet_encStr a i.isLt, rawGet_encStr b i.isLt] at h1
  refine Fin.ext ?_
  simpa using h1

/-- **What the test decides.** -/
theorem rawIsoTest_eq_true_iff {r : RawPerm} (hr : RawPerm.WF n r) :
    rawIsoTest ((encStr x, encStr y), r) = true ↔ ∀ u, x u = y (decPerm n r u) := by
  set σ : Perm (Fin n) := decPerm n r with hσ
  have hre : r = encPerm n σ := (encPerm_decPerm hr).symm
  rw [rawIsoTest]
  simp only [decide_eq_true_eq]
  rw [hre, rawInv_encPerm, rawStrAct_encStr]
  constructor
  · intro h
    have hy : Babai.strAct y σ⁻¹ = x := encStr_injective h
    intro u
    have := congrFun hy u
    rw [Babai.strAct] at this
    simpa using this.symm
  · intro h
    refine congrArg encStr (funext fun u => ?_)
    rw [Babai.strAct]
    simpa using (h u).symm

/-- **The listed isomorphisms are exactly `Iso_G(x,y)`.** -/
theorem mem_rawIsoList_iff (hdom : dom.length = n)
    (hidx : Nat.card (genGroup gens) ≤ js.length + 1) {τ : Perm (Fin n)} :
    (∃ r ∈ rawIsoList (((dom, gens.map (encPerm n)), js), (encStr x, encStr y)),
      decPerm n r = τ) ↔ τ ∈ IsoSet gens x y := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨hmem, htest⟩ := List.mem_filter.1 hr
    obtain ⟨hwf, hG⟩ := decPerm_mem_genGroup_of_mem hdom hmem
    exact ⟨hG, (rawIsoTest_eq_true_iff hwf).1 htest⟩
  · rintro ⟨hG, hiso⟩
    obtain ⟨r, hr, hrτ⟩ := mem_rawGroupElems hdom hidx hG
    obtain ⟨hwf, -⟩ := decPerm_mem_genGroup_of_mem hdom hr
    refine ⟨r, List.mem_filter.2 ⟨hr, ?_⟩, hrτ⟩
    rw [rawIsoTest_eq_true_iff hwf, hrτ]
    exact hiso

/-- **The listed automorphisms are exactly `Aut_G(x)`.** -/
theorem mem_rawAutList_iff (hdom : dom.length = n)
    (hidx : Nat.card (genGroup gens) ≤ js.length + 1) {τ : Perm (Fin n)} :
    (∃ r ∈ rawAutList (((dom, gens.map (encPerm n)), js), (encStr x, encStr y)),
      decPerm n r = τ) ↔ τ ∈ AutSet gens x := by
  have h : rawAutList (((dom, gens.map (encPerm n)), js), (encStr x, encStr y))
      = rawIsoList (((dom, gens.map (encPerm n)), js), (encStr x, encStr x)) := rfl
  rw [h, AutSet]
  exact mem_rawIsoList_iff hdom hidx

/-- `Aut_G(x)` is a subgroup: the permutations of `G` that leave the string where it is. -/
def autSubgroup (gens : List (Perm (Fin n))) (x : Fin n → Fin s) : Subgroup (Perm (Fin n)) where
  carrier := AutSet gens x
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun u => ?_⟩
    have h1 : x u = x (b u) := hb' u
    have h2 : x (b u) = x (a (b u)) := ha' (b u)
    exact h1.trans h2
  one_mem' := ⟨one_mem _, fun _ => rfl⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun u => ?_⟩
    have := ha' (a⁻¹ u)
    simpa using this.symm

theorem coe_autSubgroup : (autSubgroup gens x : Set (Perm (Fin n))) = AutSet gens x := rfl

/-- **`none` exactly when there is no isomorphism.** -/
theorem rawBrute_eq_none_iff (hdom : dom.length = n)
    (hidx : Nat.card (genGroup gens) ≤ js.length + 1) :
    rawBrute (((dom, gens.map (encPerm n)), js), (encStr x, encStr y)) = none ↔
      IsoSet gens x y = ∅ := by
  rw [rawBrute]
  by_cases hemp : (rawIsoList (((dom, gens.map (encPerm n)), js),
      (encStr x, encStr y))).isEmpty = true
  · rw [if_pos hemp]
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    refine Set.eq_empty_iff_forall_notMem.2 (fun τ hτ => ?_)
    obtain ⟨r, hr, -⟩ := (mem_rawIsoList_iff hdom hidx).2 hτ
    rw [List.isEmpty_iff.1 hemp] at hr
    exact absurd hr List.not_mem_nil
  · rw [if_neg hemp]
    refine ⟨fun hcon => absurd hcon (by simp), fun h => ?_⟩
    exfalso
    have hmem := headD_mem_of_not_isEmpty (rawOne dom) hemp
    have hiso := (mem_rawIsoList_iff hdom hidx).1 ⟨_, hmem, rfl⟩
    rw [h] at hiso
    exact Set.notMem_empty _ hiso

/-- **The answer in the other case** (Definition 11.1.2): the representative is an
isomorphism, and the generating list generates `Aut_G(x)`.  This is `RAM.Targets.SIRel`. -/
theorem rawBrute_spec (hdom : dom.length = n)
    (hidx : Nat.card (genGroup gens) ≤ js.length + 1) {aut : RawGens} {σ : RawPerm}
    (h : rawBrute (((dom, gens.map (encPerm n)), js), (encStr x, encStr y)) = some (aut, σ)) :
    decPerm n σ ∈ IsoSet gens x y ∧ (decGroup n aut : Set (Perm (Fin n))) = AutSet gens x := by
  by_cases hemp : (rawIsoList (((dom, gens.map (encPerm n)), js),
      (encStr x, encStr y))).isEmpty = true
  · rw [rawBrute, if_pos hemp] at h
    exact absurd h (by simp)
  rw [rawBrute, if_neg hemp] at h
  obtain ⟨haut, hσ⟩ :
      rawShorten (dom, rawAutList (((dom, gens.map (encPerm n)), js), (encStr x, encStr y)))
        = aut ∧
      (rawIsoList (((dom, gens.map (encPerm n)), js), (encStr x, encStr y))).headD
        (rawOne dom) = σ := by
    have h1 := Option.some.inj h
    exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩
  constructor
  · have hmem := headD_mem_of_not_isEmpty (rawOne dom) hemp
    rw [hσ] at hmem
    exact (mem_rawIsoList_iff hdom hidx).1 ⟨σ, hmem, rfl⟩
  · set A := rawAutList (((dom, gens.map (encPerm n)), js), (encStr x, encStr y)) with hA
    have hwfA : ∀ r ∈ A, RawPerm.WF n r := by
      intro r hr
      exact (decPerm_mem_genGroup_of_mem hdom (List.mem_filter.1 hr).1).1
    have hAmap : A = (A.map (decPerm n)).map (encPerm n) := (map_encPerm_decPerm hwfA).symm
    have hgen : decGroup n (rawShorten (dom, A)) = genGroup (A.map (decPerm n)) := by
      conv_lhs => rw [hAmap]
      exact decGroup_rawShorten dom hdom (A.map (decPerm n))
    have hset : {g : Perm (Fin n) | g ∈ A.map (decPerm n)} = AutSet gens x := by
      ext τ
      constructor
      · intro hτ
        obtain ⟨r, hr, hrτ⟩ := List.mem_map.1 hτ
        exact (mem_rawAutList_iff hdom hidx).1 ⟨r, hr, hrτ⟩
      · intro hτ
        obtain ⟨r, hr, hrτ⟩ := (mem_rawAutList_iff hdom hidx).2 hτ
        exact List.mem_map.2 ⟨r, hr, hrτ⟩
    rw [← haut, hgen, genGroup, hset, ← coe_autSubgroup (gens := gens) (x := x),
      Subgroup.closure_eq]

end Spec

/-! ## The running time -/

section Poly

theorem polyFun_rawGroupElems : PolyFun rawGroupElems :=
  (((polyFun_fst.comp polyFun_fst).pair (polyFun_fst.comp polyFun_snd)).pair
    ((polyFun_const ([] : RawGens)).pair polyFun_snd)).comp polyFun_rawCosetReps

theorem polyFun_rawIsoTest : PolyFun rawIsoTest := by
  have hact : PolyFun (fun p : (RawStr × RawStr) × RawPerm =>
      rawStrAct (rawInv p.2, p.1.2)) :=
    ((polyFun_snd.comp polyFun_rawInv).pair (polyFun_fst.comp polyFun_snd)).comp
      polyFun_rawStrAct
  exact ((hact.pair (polyFun_fst.comp polyFun_fst)).comp polyFun_listNatEq).of_eq (fun _ => rfl)

theorem polyFun_rawIsoList : PolyFun rawIsoList := by
  have hpred : PolyFun (fun z : (((List ℕ × RawGens) × List ℕ) × (RawStr × RawStr)) × RawPerm =>
      rawIsoTest (z.1.2, z.2)) :=
    ((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp polyFun_rawIsoTest
  have hin : PolyFun (fun p : ((List ℕ × RawGens) × List ℕ) × (RawStr × RawStr) =>
      ((p, rawGroupElems p.1) : (((List ℕ × RawGens) × List ℕ) × (RawStr × RawStr)) × RawGens)) :=
    polyFun_id.pair (polyFun_fst.comp polyFun_rawGroupElems)
  exact (hin.comp (PolyFun.filterParam hpred)).of_eq (fun _ => rfl)

theorem polyFun_rawAutList : PolyFun rawAutList := by
  have hpred : PolyFun (fun z : (((List ℕ × RawGens) × List ℕ) × (RawStr × RawStr)) × RawPerm =>
      rawIsoTest (((z.1.2.1, z.1.2.1) : RawStr × RawStr), z.2)) :=
    ((((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)).pair polyFun_snd).comp polyFun_rawIsoTest
  have hin : PolyFun (fun p : ((List ℕ × RawGens) × List ℕ) × (RawStr × RawStr) =>
      ((p, rawGroupElems p.1) : (((List ℕ × RawGens) × List ℕ) × (RawStr × RawStr)) × RawGens)) :=
    polyFun_id.pair (polyFun_fst.comp polyFun_rawGroupElems)
  exact (hin.comp (PolyFun.filterParam hpred)).of_eq (fun _ => rfl)

/-- **The brute force runs in time polynomial in `|G|` and the size of the instance.** -/
theorem polyFun_rawBrute : PolyFun rawBrute := by
  have hdom : PolyFun (fun p : ((List ℕ × RawGens) × List ℕ) × (RawStr × RawStr) =>
      p.1.1.1) := (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have hshort : PolyFun (fun p : ((List ℕ × RawGens) × List ℕ) × (RawStr × RawStr) =>
      rawShorten (p.1.1.1, rawAutList p)) := (hdom.pair polyFun_rawAutList).comp polyFun_rawShorten
  have hrep : PolyFun (fun p : ((List ℕ × RawGens) × List ℕ) × (RawStr × RawStr) =>
      (rawIsoList p).headD (rawOne p.1.1.1)) := by
    refine (((polyFun_rawIsoList.comp polyFun_headOption).pair
      (hdom.comp polyFun_rawOne)).comp polyFun_optionGetD).of_eq (fun p => ?_)
    rw [List.headD_eq_head?_getD]
  exact (PolyFun.ite (polyFun_rawIsoList.comp polyFun_isEmpty) (polyFun_const none)
    ((hshort.pair hrep).comp polyFun_some)).of_eq (fun p => by
      unfold rawBrute
      by_cases h : (rawIsoList p).isEmpty = true <;> simp [h])

end Poly

end Algo
