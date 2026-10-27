import Workspace.Algo.PrimitiveHypergraph
import Workspace.Algo.FunctorsAmbient
import Workspace.Algo.WFTests
import Workspace.Master.KAryOfString
import Workspace.Luks.JohnsonBarrier

/-! # Section 15, line 4c: construct the relations of the primitive hypergraph

For each supplied color, keep precisely the injective tuples whose underlying
edge has that color. The tuple table uses the original string domain as its
size witness. Its arity guard follows from the primitive identification:
`2^t ≤ choose m t = n`.

The color list is input data. This keeps the ordering of relations explicit,
including the ordering chosen by the mathematical `relOfColoring` interface.
-/

namespace Algo
open Babai RAM RAM.Targets
open Equiv (Perm)

/-- Action and string, arity witness, and ordered color names. -/
abbrev RawPrimitiveRelIn := ((RawAction × RawStr) × List ℕ) × List ℕ

/-- An injective tuple belongs to the relation of its edge color. -/
def primitiveRelTest (z : ((RawAction × RawStr) × ℕ) × List ℕ) : Bool :=
  wftNodup z.2 && decide ((primitiveHyperColor (z.1.1, z.2)).getD 0 = z.1.2)

def primitiveRelRows (z : ((RawAction × RawStr) × List (List ℕ)) × ℕ) : RawRel :=
  z.1.2.filter (fun row => primitiveRelTest ((z.1.1, z.2), row))

/-- One relation per supplied color, in the supplied order. -/
def primitiveRelations (c : ℕ) (p : RawPrimitiveRelIn) : RawRelStruct :=
  p.2.map (fun a => primitiveRelRows
    ((p.1.1, (aggTable c (p.1.2, p.1.1.1.1.1,
      List.range p.1.1.1.2.1.length)).2.map Prod.fst), a))

theorem polyFun_primitiveRelTest : PolyFun primitiveRelTest := by
  have hc : PolyFun (fun z : ((RawAction × RawStr) × ℕ) × List ℕ =>
      (primitiveHyperColor (z.1.1, z.2)).getD 0) :=
    ((((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp
    polyFun_primitiveHyperColor).pair (polyFun_const 0)).comp polyFun_optionGetD
  exact wftPolyFun_and (polyFun_snd.comp wftPolyFun_nodup)
    (hc.natEq (polyFun_fst.comp polyFun_snd))

theorem polyFun_primitiveRelRows : PolyFun primitiveRelRows := by
  have hin : PolyFun (fun z : ((RawAction × RawStr) × List (List ℕ)) × ℕ =>
      ((z.1.1, z.2), z.1.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).pair
      (polyFun_fst.comp polyFun_snd)
  exact hin.comp (PolyFun.filterParam polyFun_primitiveRelTest)

/-- The whole relation table has an unconditional quasipolynomial RAM bound. -/
theorem quasiFun_primitiveRelations (c : ℕ) : QuasiFun (primitiveRelations c) := by
  have hp : PolyFun (fun p : RawPrimitiveRelIn => p.1.1) :=
    polyFun_fst.comp polyFun_fst
  have ha := hp.comp polyFun_fst
  have hd := (ha.comp polyFun_fst).comp polyFun_fst
  have ht := ((ha.comp polyFun_snd).comp polyFun_fst).comp polyFun_rangeLength
  have htab := (((polyFun_fst.comp polyFun_snd).pair (hd.pair ht)).comp_quasiFun
    (aggQuasiFun_table c)).comp_poly (polyFun_snd.comp (PolyFun.map polyFun_fst))
  exact ((hp.quasiFun.pair htab).pair polyFun_snd.quasiFun).comp_poly
    (PolyFun.mapParam polyFun_primitiveRelRows)

@[simp] theorem length_primitiveRelations (c : ℕ) (p : RawPrimitiveRelIn) :
    (primitiveRelations c p).length = p.2.length := by simp [primitiveRelations]

theorem winSet_tupleOf {m t : ℕ} (v : Fin t → Fin m) :
    winSet m (tupleOf v) = (edgeOf v : Set (Fin m)) := by
  ext u
  simp only [winSet, Set.mem_setOf_eq, tupleOf, List.mem_ofFn,
    Finset.mem_coe, edgeOf, Finset.mem_image, Finset.mem_univ, true_and]
  exact exists_congr (fun i => Fin.val_inj)

theorem nodup_tupleOf_iff_edge_card {m t : ℕ} (v : Fin t → Fin m) :
    (tupleOf v).Nodup ↔ (edgeOf v).card = t := by
  have he : (tupleOf v).Nodup ↔ Function.Injective v := by
    rw [tupleOf, List.nodup_ofFn]
    exact ⟨fun h i j hij => h (congrArg Fin.val hij),
      fun h i j hij => h (Fin.ext hij)⟩
  rw [he, edgeOf]
  constructor
  · intro hi
    rw [Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]
  · intro hc
    have hcard : (Finset.univ.image v).card = (Finset.univ : Finset (Fin t)).card := by
      simpa only [Finset.card_univ, Fintype.card_fin] using hc
    intro i j hij
    exact Finset.card_image_iff.mp hcard (Finset.mem_univ i) (Finset.mem_univ j) hij

section Specification

variable {n m t : ℕ} {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {ϕ : genGroup gens →* Perm (Fin m)} {dom gdom : List ℕ}
    (hd : dom.length = n) (hg : gdom.length = m) (hI : ImgsOf gens imgs ϕ)
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength (genGroup gens)))
    (id : PrimitiveCaseId ϕ t)

local notation "act" => ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m)))

include hd hg hI hϕ hk id

theorem primitiveRelTest_spec (x : RawStr) (a : ℕ) (v : Fin t → Fin m) :
    primitiveRelTest (((act, x), a), tupleOf v) = true ↔
      v ∈ hyperRel t (hyperColoring id (decStrN n x)) a := by
  rw [primitiveRelTest, Bool.and_eq_true, wftNodup_eq_true_iff,
    nodup_tupleOf_iff_edge_card, decide_eq_true_eq]
  change ((_ = t) ∧ _) ↔ ∃ h : (edgeOf v).card = t, _
  constructor
  · rintro ⟨hc, ha⟩
    refine ⟨hc, ?_⟩
    rw [primitiveHyperColor_spec hd hg hI hϕ hk id x
      ⟨edgeOf v, hc⟩ (tupleOf v) (winSet_tupleOf v)] at ha
    exact ha
  · rintro ⟨hc, ha⟩
    refine ⟨hc, ?_⟩
    rw [primitiveHyperColor_spec hd hg hI hϕ hk id x
      ⟨edgeOf v, hc⟩ (tupleOf v) (winSet_tupleOf v)]
    exact ha

theorem primitiveRelations_index_spec {c : ℕ} (x : RawStr) (ks colors : List ℕ)
    (ht : ks.length = t) (hguard : ks.length ≤ guardBound c dom.length)
    (i : ℕ) (hi : i < colors.length) (v : Fin t → Fin m) :
    v ∈ (decRel m t (primitiveRelations c (((act, x), ks), colors))).rel i ↔
      v ∈ hyperRel t (hyperColoring id (decStrN n x)) (colors[i]) := by
  change tupleOf v ∈ (primitiveRelations c (((act, x), ks), colors)).getD i [] ↔ _
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [primitiveRelations, List.getElem_map, primitiveRelRows, List.mem_filter]
  change (tupleOf v ∈ (aggTable c (ks, dom, List.range gdom.length)).2.map Prod.fst ∧
    primitiveRelTest (((act, x), colors[i]), tupleOf v) = true) ↔ _
  rw [aggTable_of_guard (a := (ks, dom, List.range gdom.length)) hguard, keys_tupleTable]
  have hv : tupleOf v ∈ tuplesOf (List.range gdom.length) ks.length := by
    rw [mem_tuplesOf]
    exact ⟨(length_tupleOf v).trans ht.symm,
      fun a ha => List.mem_range.mpr (by simpa only [hg] using tupleOf_lt v ha)⟩
  rw [and_iff_right hv]
  exact primitiveRelTest_spec hd hg hI hϕ hk id x _ v

/-- With the supplied palette in the order used by `relOfColoring`, every
decoded relation is exactly the corresponding relation of that structure.
The machine never has to compute the arbitrary finite-type enumeration. -/
theorem primitiveRelations_relOfColoring {A : Type*} [Fintype A] [DecidableEq A]
    {c : ℕ} (code : A → ℕ) (hcode : Function.Injective code)
    (x : Fin n → A) (raw : RawStr) (hx : ∀ u : Fin n, raw.getD u 0 = code (x u))
    (ks colors : List ℕ) (ht : ks.length = t)
    (hguard : ks.length ≤ guardBound c dom.length)
    (hlen : colors.length = Fintype.card A)
    (hcolors : ∀ i : Fin (Fintype.card A),
      colors.getD i 0 = code ((Fintype.equivFin A).symm i))
    (i : Fin (Fintype.card A)) :
    (decRel m t (primitiveRelations c (((act, raw), ks), colors))).rel i =
      (relOfColoring t (hyperColoring id x)).rel i := by
  have hi : (i : ℕ) < colors.length := by simpa only [hlen] using i.isLt
  have hcol : colors[i.val] = code ((Fintype.equivFin A).symm i) := by
    rw [← List.getD_eq_getElem _ 0 hi]
    exact hcolors i
  ext v
  rw [primitiveRelations_index_spec hd hg hI hϕ hk id raw ks colors ht hguard i hi v]
  change (∃ h : (edgeOf v).card = t,
      hyperColoring id (decStrN n raw) ⟨edgeOf v, h⟩ = colors[i.val]) ↔
    ∃ h : (edgeOf v).card = t,
      hyperColoring id x ⟨edgeOf v, h⟩ = (Fintype.equivFin A).symm i
  apply exists_congr
  intro h
  rw [hcol]
  change raw.getD (id.label.symm ⟨edgeOf v, h⟩) 0 = _ ↔ _
  rw [hx]
  exact hcode.eq_iff

end Specification

/-- The guard needed by line 4c follows from the primitive identification itself. -/
theorem primitiveCase_arity_le_log {n m t : ℕ} {G : Subgroup (Perm (Fin n))}
    {ϕ : G →* Perm (Fin m)} (id : PrimitiveCaseId ϕ t) : t ≤ Nat.log 2 n := by
  have hc : n = m.choose t := by
    have he := Nat.card_congr id.label
    rw [card_binom (Fin m) t] at he
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using he
  have ht : 4 * t < m := by simpa only [Fintype.card_fin] using id.four_t
  apply Nat.le_log_of_pow_le (by norm_num)
  rw [hc]
  exact Babai.two_pow_le_choose (by omega)

theorem primitiveCase_arity_guard {n m t : ℕ} {G : Subgroup (Perm (Fin n))}
    {ϕ : G →* Perm (Fin m)} (id : PrimitiveCaseId ϕ t) : t ≤ guardBound 1 n := by
  have ht := primitiveCase_arity_le_log id
  simpa only [guardBound, pow_one] using ht.trans (Nat.le_succ _)

end Algo

#print axioms Algo.quasiFun_primitiveRelations
#print axioms Algo.primitiveRelations_index_spec
#print axioms Algo.primitiveRelations_relOfColoring
#print axioms Algo.primitiveCase_arity_guard
