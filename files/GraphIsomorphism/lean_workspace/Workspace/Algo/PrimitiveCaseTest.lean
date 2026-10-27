import Workspace.Algo.AlignColorRaw
import Workspace.Algo.WFTests
import Workspace.Master.PrimitiveCaseConstruct

/-! # Section 15, lines 3–4: testing the standard-block identification

The points are the standard blocks exactly when their `T(u)` labels are
distinct. We also check that every label has the supplied size `t`. Both
tests scan the computed label table. Theorem 10.5.1(e) then supplies its
surjectivity onto the `t`-subsets, so the test produces the mathematical
identification used by line 4b.

This tests the `PrimitiveCaseId` interface. The master dispatcher must still
supply the encoded giant representation and the parameter of its hint.
-/

namespace Algo
open Babai RAM RAM.Targets
open Equiv (Perm)

/-- A row occurs exactly once in the supplied list. -/
def primitiveRowOnce (p : List (List ℕ) × List ℕ) : Bool :=
  decide ((p.1.filter (fun row => decide (row = p.2))).length = 1)

def primitiveRowsDistinct (rows : List (List ℕ)) : Bool :=
  wftAll primitiveRowOnce (rows, rows)

theorem primitiveRowsDistinct_spec (rows : List (List ℕ)) :
    primitiveRowsDistinct rows = true ↔ rows.Nodup := by
  rw [primitiveRowsDistinct, wftAll_eq_true_iff, List.nodup_iff_count_eq_one]
  apply forall_congr'
  intro row
  apply forall_congr'
  intro _
  have he : (fun r : List ℕ => decide (r = row)) = (fun r => r == row) := by
    funext r
    apply Bool.eq_iff_iff.mpr
    simp
  simp only [primitiveRowOnce, decide_eq_true_eq, List.count_eq_length_filter, he]

theorem polyFun_primitiveRowOnce : PolyFun primitiveRowOnce := by
  have he : PolyFun (fun z : (List (List ℕ) × List ℕ) × List ℕ =>
      decide (z.2 = z.1.2)) :=
    (polyFun_snd.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_listNatEq
  exact (((polyFun_id.pair polyFun_fst).comp (PolyFun.filterParam he)).comp
    polyFun_length).natEq (polyFun_const 1)

theorem polyFun_primitiveRowsDistinct : PolyFun primitiveRowsDistinct :=
  (polyFun_id.pair polyFun_id).comp (wftPolyFun_all polyFun_primitiveRowOnce)

/-- Section 15, lines 3–4: the labels distinguish the points and have size `t`. -/
def primitiveCaseTest (p : RawAction × ℕ) : Bool :=
  wftAll (fun q : ℕ × List ℕ => decide (q.2.length = q.1)) (p.2, rawTpointAll p.1) &&
    primitiveRowsDistinct (rawTpointAll p.1)

theorem polyFun_primitiveCaseTest : PolyFun primitiveCaseTest := by
  have hr : PolyFun (fun p : RawAction × ℕ => rawTpointAll p.1) :=
    polyFun_fst.comp polyFun_rawTpointAll
  have hs : PolyFun (fun q : ℕ × List ℕ => decide (q.2.length = q.1)) :=
    (polyFun_snd.comp polyFun_length).natEq polyFun_fst
  exact wftPolyFun_and ((polyFun_snd.pair hr).comp (wftPolyFun_all hs))
    (hr.comp polyFun_primitiveRowsDistinct)

/-- The two finite scans express uniform label size and injectivity. -/
theorem primitiveCaseTest_raw {p : RawAction} {n t : ℕ} (hd : p.1.1.length = n) :
    primitiveCaseTest (p, t) = true ↔
      (∀ u : Fin n, (rawTpoint (p, u)).length = t) ∧
        Function.Injective (fun u : Fin n => rawTpoint (p, u)) := by
  rw [primitiveCaseTest, Bool.and_eq_true, wftAll_eq_true_iff, primitiveRowsDistinct_spec]
  constructor
  · rintro ⟨hs, hi⟩
    refine ⟨fun u => ?_, fun u v huv => ?_⟩
    · apply of_decide_eq_true (hs _ ?_)
      exact List.mem_map.mpr ⟨u, List.mem_range.mpr (by simpa only [hd] using u.isLt), rfl⟩
    · apply Fin.ext
      exact List.inj_on_of_nodup_map hi
        (List.mem_range.mpr (by simpa only [hd] using u.isLt))
        (List.mem_range.mpr (by simpa only [hd] using v.isLt)) huv
  · rintro ⟨hs, hi⟩
    constructor
    · intro row hr
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
      apply decide_eq_true
      exact hs ⟨u, by simpa only [List.mem_range, hd] using hu⟩
    · apply List.Nodup.map_on _ List.nodup_range
      intro u hu v hv huv
      have hun : u < n := by simpa only [List.mem_range, hd] using hu
      have hvn : v < n := by simpa only [List.mem_range, hd] using hv
      exact congrArg Fin.val (hi (a₁ := ⟨u, hun⟩) (a₂ := ⟨v, hvn⟩) huv)

/-- Section 15, lines 3–4: the polynomial test is equivalent to existence
of the paper's standard-block identification, with its equivariance. -/
theorem primitiveCaseTest_spec {n m t : ℕ} {gens : List (Perm (Fin n))}
    {imgs : List (Perm (Fin m))} {ϕ : genGroup gens →* Perm (Fin m)}
    {dom gdom : List ℕ} (hd : dom.length = n) (hg : gdom.length = m)
    (hn : 0 < n) (hI : ImgsOf gens imgs ϕ) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength (genGroup gens))) :
    primitiveCaseTest (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), t) = true ↔
      Nonempty (PrimitiveCaseId ϕ t) := by
  rw [primitiveCaseTest_raw hd,
    nonempty_primitiveCaseId_iff ϕ ⟨⟨0, hn⟩⟩ hϕ hk]
  have hlen : ∀ u : Fin n,
      (rawTpoint (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), u)).length =
        tPoint ϕ u := by
    intro u
    simpa only [List.filter_true, Set.setOf_true, Set.inter_univ] using
      length_filter_rawTpoint hd hg hI hϕ hk u (fun _ => true)
  have hinj : Function.Injective (fun u : Fin n =>
      rawTpoint (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), u)) ↔
        Function.Injective (Tpoint ϕ) := by
    constructor
    · intro h u v huv
      exact h ((rawTpoint_eq_iff hd hg hI hϕ hk u v).mpr huv)
    · intro h u v huv
      exact h ((rawTpoint_eq_iff hd hg hI hϕ hk u v).mp huv)
  simp only [hlen, hinj, and_comm]

end Algo

#print axioms Algo.polyFun_primitiveCaseTest
#print axioms Algo.primitiveCaseTest_spec
