import Workspace.Algo.TpointRaw
import Workspace.Algo.SplitHypergraph
import Workspace.Master.PrimitiveCaseIdUnique

/-! # Section 15, line 4b: the hypergraph of a string on the RAM

In the primitive case, each point of the string has a different label `T(u)`,
and these labels are all the `t`-subsets of the top domain. Store one pair
`(T(u), x(u))` per point. This is the edge-colored hypergraph `H(x)` in
version 2.5, Section 15, line 4b (page 98).

The existing polynomial routine computes `T(u)`. Its specification and
`PrimitiveCaseId.label_eq` identify the stored edge with the label used by
the mathematical reduction. No chosen ordering of subsets is needed.

The table and its color lookup have polynomial RAM bounds on all inputs.
Their specifications below apply to the primitive case. This does not yet
implement the symmetry-defect test or the relational structure of line 4c.
-/

namespace Algo
open Babai RAM RAM.Targets
open Equiv (Perm)

/-- Section 15, line 4b: one edge and its color. -/
def primitiveHyperRow (z : (RawAction × RawStr) × ℕ) : List ℕ × ℕ :=
  (rawTpoint (z.1.1, z.2), z.1.2.getD z.2 0)

/-- Section 15, line 4b: store the labeled edges in the string's point order. -/
def primitiveHypergraph (p : RawAction × RawStr) : List (List ℕ × ℕ) :=
  (List.range p.1.1.1.length).map (fun u => primitiveHyperRow (p, u))

/-- Look up an edge after listing its vertices in increasing order.
An absent edge returns `none`, including on malformed inputs. -/
def primitiveHyperColor (z : (RawAction × RawStr) × List ℕ) : Option ℕ :=
  (primitiveHypergraph z.1).lookup (splitNormalizeRow (z.1.1.2.1, z.2))

theorem polyFun_primitiveHyperRow : PolyFun primitiveHyperRow := by
  have hl : PolyFun (fun z : (RawAction × RawStr) × ℕ => rawTpoint (z.1.1, z.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_rawTpoint
  have hc : PolyFun (fun z : (RawAction × RawStr) × ℕ => z.1.2.getD z.2 0) :=
    (((polyFun_fst.comp polyFun_snd).pair polyFun_snd).pair
      (polyFun_const 0)).comp polyFun_getD
  exact hl.pair hc

theorem polyFun_primitiveHypergraph : PolyFun primitiveHypergraph := by
  have hr : PolyFun (fun p : RawAction × RawStr => List.range p.1.1.1.length) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_rangeLength
  exact (polyFun_id.pair hr).comp (PolyFun.mapParam polyFun_primitiveHyperRow)

theorem polyFun_primitiveHyperColor : PolyFun primitiveHyperColor := by
  have hd : PolyFun (fun z : (RawAction × RawStr) × List ℕ => z.1.1.2.1) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst
  exact ((polyFun_fst.comp polyFun_primitiveHypergraph).pair
    ((hd.pair polyFun_snd).comp polyFun_splitNormalizeRow)).comp
      (polyFun_listLookup polyFun_listNatEq)

@[simp] theorem length_primitiveHypergraph (p : RawAction × RawStr) :
    (primitiveHypergraph p).length = p.1.1.1.length := by
  simp [primitiveHypergraph]

/-- Equal decoded subsets have the same increasing list of vertices. -/
theorem normalizeRow_eq_rawTpoint {p : RawAction} {m u : ℕ} {row : List ℕ}
    (hg : p.2.1.length = m) (he : winSet m row = winSet m (rawTpoint (p, u))) :
    splitNormalizeRow (p.2.1, row) = rawTpoint (p, u) := by
  unfold splitNormalizeRow rawTpoint
  apply List.filter_congr
  intro j hj
  have hjp : j < p.2.1.length := List.mem_range.mp hj
  have hm := Set.ext_iff.mp he (⟨j, by omega⟩ : Fin m)
  change j ∈ row ↔ j ∈ rawTpoint (p, u) at hm
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq, mem_rawTpoint_iff_raw, hjp, true_and,
    rawTpointTest_eq_true_iff] using hm

section Specification

variable {n m t : ℕ} {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {ϕ : genGroup gens →* Perm (Fin m)} {dom gdom : List ℕ}
    (hd : dom.length = n) (hg : gdom.length = m) (hI : ImgsOf gens imgs ϕ)
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength (genGroup gens)))
    (id : PrimitiveCaseId ϕ t)

local notation "act" => ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m)))

include hd hg hI hϕ hk id

/-- The machine computes exactly the primitive-case label, including when
the mathematical reduction obtains its identification by choice. -/
theorem primitiveHyperRow_label (x : RawStr) (u : Fin n) :
    winSet m (primitiveHyperRow ((act, x), u)).1 =
      ((id.label u : Finset (Fin m)) : Set (Fin m)) := by
  exact (winSet_rawTpoint hd hg hI hϕ hk u).trans (id.label_eq u).symm

set_option maxHeartbeats 1000000 in
/-- Every stored row is an edge of `H(x)` with its stated color. -/
theorem primitiveHypergraph_row (x : RawStr) (row : List ℕ × ℕ)
    (hr : row ∈ primitiveHypergraph (act, x)) :
    ∃ T : binom (Fin m) t, winSet m row.1 = (T : Finset (Fin m)) ∧
      row.2 = hyperColoring id (decStrN n x) T := by
  change row ∈ (List.range dom.length).map
    (fun u => primitiveHyperRow ((act, x), u)) at hr
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
  have hun : u < n := by simpa only [List.mem_range, hd] using hu
  refine ⟨id.label ⟨u, hun⟩,
    primitiveHyperRow_label hd hg hI hϕ hk id x ⟨u, hun⟩, ?_⟩
  change x.getD u 0 = x.getD (id.label.symm (id.label ⟨u, hun⟩)) 0
  rw [Equiv.symm_apply_apply]

/-- Every edge of `H(x)` occurs in the table. -/
theorem primitiveHypergraph_complete (x : RawStr) (T : binom (Fin m) t) :
    ∃ row ∈ primitiveHypergraph (act, x),
      winSet m row.1 = (T : Finset (Fin m)) ∧
        row.2 = hyperColoring id (decStrN n x) T := by
  let u := id.label.symm T
  refine ⟨primitiveHyperRow ((act, x), u), ?_, ?_, rfl⟩
  · apply List.mem_map.mpr
    exact ⟨u, List.mem_range.mpr (by simpa only [hd] using u.isLt), rfl⟩
  · simpa only [u, Equiv.apply_symm_apply] using
      primitiveHyperRow_label hd hg hI hϕ hk id x u

/-- Distinct string points have distinct raw edge rows in the primitive case. -/
theorem primitiveHyperRow_injective (x : RawStr) :
    Function.Injective (fun u : Fin n => (primitiveHyperRow ((act, x), u)).1) := by
  intro u v huv
  apply id.label.injective
  apply Subtype.ext
  apply Finset.coe_injective
  rw [← primitiveHyperRow_label hd hg hI hϕ hk id x u,
    ← primitiveHyperRow_label hd hg hI hϕ hk id x v]
  exact congrArg (winSet m) huv

/-- The edge table has no repeated keys. -/
theorem primitiveHypergraph_keys_nodup (x : RawStr) :
    ((primitiveHypergraph (act, x)).map Prod.fst).Nodup := by
  rw [primitiveHypergraph, List.map_map]
  apply List.Nodup.map_on _ List.nodup_range
  intro u hu v hv huv
  have hun : u < n := by simpa only [List.mem_range, hd] using hu
  have hvn : v < n := by simpa only [List.mem_range, hd] using hv
  exact congrArg Fin.val
    (primitiveHyperRow_injective hd hg hI hϕ hk id x
      (a₁ := ⟨u, hun⟩) (a₂ := ⟨v, hvn⟩) huv)

/-- Section 15, line 4b: looking up any list representing `T` returns `H(x)(T)`.
Repeated vertices and vertices outside the top domain are discarded by normalization. -/
theorem primitiveHyperColor_spec (x : RawStr) (T : binom (Fin m) t) (row : List ℕ)
    (hr : winSet m row = (T : Finset (Fin m))) :
    primitiveHyperColor ((act, x), row) = some (hyperColoring id (decStrN n x) T) := by
  let u := id.label.symm T
  have hl : winSet m (rawTpoint (act, u)) = (T : Finset (Fin m)) := by
    simpa only [primitiveHyperRow, u, Equiv.apply_symm_apply] using
      primitiveHyperRow_label hd hg hI hϕ hk id x u
  have he : winSet m row = winSet m (rawTpoint (act, u)) := hr.trans hl.symm
  have hn := normalizeRow_eq_rawTpoint hg he
  rw [primitiveHyperColor, hn, RAM.lookup_eq_find?]
  let P := fun q : List ℕ × ℕ => decide (q.1 = rawTpoint (act, u))
  cases hf : (primitiveHypergraph (act, x)).find? P with
  | none =>
    have hn := List.find?_eq_none.mp hf
    have hu : primitiveHyperRow ((act, x), u) ∈ primitiveHypergraph (act, x) := by
      apply List.mem_map.mpr
      exact ⟨u, List.mem_range.mpr (by simpa only [hd] using u.isLt), rfl⟩
    have := hn _ hu
    simp [P, primitiveHyperRow] at this
  | some q =>
    have hq := List.mem_of_find?_eq_some hf
    have hp : q.1 = rawTpoint (act, u) := by
      simpa only [P, decide_eq_true_eq] using List.find?_some hf
    obtain ⟨T', hT', hc⟩ := primitiveHypergraph_row hd hg hI hϕ hk id x q hq
    have hTu : (T' : Finset (Fin m)) = (T : Finset (Fin m)) := by
      apply Finset.coe_injective
      rw [← hT', hp, hl]
    have ht : T' = T := Subtype.ext hTu
    simp only [Option.map_some, hc, ht]

end Specification
end Algo

#print axioms Algo.polyFun_primitiveHypergraph
#print axioms Algo.polyFun_primitiveHyperColor
#print axioms Algo.primitiveHyperRow_label
#print axioms Algo.primitiveHypergraph_row
#print axioms Algo.primitiveHypergraph_complete
#print axioms Algo.primitiveHyperRow_injective
#print axioms Algo.primitiveHypergraph_keys_nodup
#print axioms Algo.primitiveHyperColor_spec
