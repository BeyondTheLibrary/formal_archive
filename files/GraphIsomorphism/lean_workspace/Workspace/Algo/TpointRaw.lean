/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the set `T(u)` of Theorem 10.5.1 (a) on the RAM.
-/
import Workspace.Algo.LocalCertAff
import Workspace.AltQuotients.MainStructure
import Workspace.AltQuotients.SandwichOrbit

/-!
# `T(u)` on the RAM (§10.5, Theorem 10.5.1 (a))

Theorem 10.5.1 (a) gives, for every point `u ∈ Ω`, a unique subset `T(u) ⊆ Γ = [k]` with
`|T(u)| < k/4` and `(A_k)_(T(u)) ≤ G_u^ϕ ≤ (S_k)_{T(u)}` (Eq. (52)).  Everything in §12
that reads the top action through the points of `Ω` — `Ω(C)`, the classes `Ω_j`, the
standard blocks — is built from these sets, so the machine needs them.

The paper never says how to compute `T(u)`; it is part of what Proposition 10.5.4 calls
"standard".  Here is the route, in three steps.

1. **Generators of `G_u^ϕ`.**  Put the action on `Ω ⊔ Γ`, take the point stabilizer of `u`
   there, and read the `Γ`-halves.  This is `Algo.rawTopStabGens`
   (`Workspace/Algo/LocalCertAff.lean`), whose specification `Algo.decGroup_rawTopStabGens`
   says that the answer generates `(G_u)^ϕ`.
2. **The orbits of `G_u^ϕ` on `Γ`.**  `Algo.rawOrbit` (`Workspace/Algo/Orbits.lean`).
3. **`T(u)` is the set of points with a short orbit.**  This is the mathematics of
   `Workspace/AltQuotients/SandwichOrbit.lean`: from Eq. (51) alone, `Γ ∖ T` is one orbit
   of the sandwiching group and every other orbit sits inside `T`, so a point of `Γ` lies
   in `T` exactly when its orbit has fewer than `k/2` points.

Step 3 needs `|Γ ∖ T| ≥ 3`, which Theorem 10.5.1 (a) supplies: there `4|T| < k` and
`k ≥ 9`.

The routine is total: on junk input it returns the points of `[0, |gdom|)` whose computed
orbit is short, which is a harmless list.  The specification is claimed only under the
hypotheses of Theorem 10.5.1, exactly as the rest of §10.5.

## Main results

* `Algo.rawTpoint`, `Algo.winSet_rawTpoint` — the set `T(u)`, and its specification;
* `Algo.rawTpoint_eq_iff` — two points have the same `T` exactly when the two lists agree;
* `Algo.rawTpointAll` — the table `u ↦ T(u)`;
* `Algo.polyFun_rawTpoint`, `Algo.polyFun_rawTpointAll` — the running time.

No axiom, no `sorry`.
-/

namespace Algo

open RAM RAM.Targets MulAction
open Equiv (Perm)

variable {n m : ℕ} {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}

/-! ## The length of a raw orbit -/

/-- The number of points the orbit routine returns is the size of the orbit.  The answer is
repetition-free (`Algo.nodup_rawOrbit`) and its entries are the orbit
(`Algo.rawOrbit_spec`). -/
theorem length_rawOrbit_eq_ncard {N : ℕ} {gs : RawGens} (hgs : RawGens.WF N gs) {i : ℕ}
    (hi : i < N) :
    (rawOrbit (gs, i)).length = (orbit (decGroup N gs) (⟨i, hi⟩ : Fin N)).ncard := by
  classical
  have hspec := rawOrbit_spec hgs hi
  have h1 : ({j | j ∈ rawOrbit (gs, i)} : Set ℕ).ncard = (rawOrbit (gs, i)).length := by
    rw [← List.coe_toFinset, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup (nodup_rawOrbit gs i)]
  rw [← h1, hspec, Set.ncard_image_of_injective _ Fin.val_injective]

/-! ## The routine -/

/-- **Theorem 10.5.1 (a) on the RAM**: the set `T(u) ⊆ Γ`, as a repetition-free list of
points of `Γ` in increasing order.

The points of `Γ` are `0, …, k-1`, read off the *length* of the domain witness of `Γ`: a
machine natural is never a loop bound (`RAM.polyFun_rangeLength`).  A point is kept when
its orbit under `G_u^ϕ` has fewer than half the points of `Γ`. -/
def rawTpointTest (z : (RawAction × ℕ) × ℕ) : Bool :=
  decide (2 * (rawOrbit (rawTopStabGens z.1, z.2)).length < z.1.1.2.1.length)

/-- **Theorem 10.5.1 (a) on the RAM**: the set `T(u) ⊆ Γ`. -/
def rawTpoint (p : RawAction × ℕ) : List ℕ :=
  (List.range p.1.2.1.length).filter (fun j => rawTpointTest (p, j))

theorem rawTpointTest_eq_true_iff (p : RawAction × ℕ) (j : ℕ) :
    rawTpointTest (p, j) = true ↔
      2 * (rawOrbit (rawTopStabGens p, j)).length < p.1.2.1.length :=
  decide_eq_true_iff

theorem nodup_rawTpoint (p : RawAction × ℕ) : (rawTpoint p).Nodup :=
  List.Nodup.filter _ List.nodup_range

theorem lt_of_mem_rawTpoint {p : RawAction × ℕ} {j : ℕ} (hj : j ∈ rawTpoint p) :
    j < p.1.2.1.length := by
  rw [rawTpoint, List.mem_filter] at hj
  exact List.mem_range.1 hj.1

/-- What the routine does, unfolded: a point is kept when it is a point of `Γ` and its
orbit is short. -/
theorem mem_rawTpoint_iff_raw (p : RawAction × ℕ) (j : ℕ) :
    j ∈ rawTpoint p ↔
      j < p.1.2.1.length ∧
        2 * (rawOrbit (rawTopStabGens p, j)).length < p.1.2.1.length := by
  rw [rawTpoint, List.mem_filter, List.mem_range, rawTpointTest_eq_true_iff]

/-- Two answers of the routine for the same action are equal as soon as they have the same
entries: both are filters of the same list. -/
theorem rawTpoint_eq_of_mem_iff {p q : RawAction × ℕ} (hpq : p.1 = q.1)
    (h : ∀ j, j ∈ rawTpoint p ↔ j ∈ rawTpoint q) : rawTpoint p = rawTpoint q := by
  have hL : p.1.2.1.length = q.1.2.1.length := by rw [hpq]
  conv_lhs => rw [rawTpoint]
  conv_rhs => rw [rawTpoint]
  rw [hL]
  refine List.filter_congr (fun j hj => ?_)
  have hjq : j < q.1.2.1.length := List.mem_range.1 hj
  have h1 := h j
  rw [mem_rawTpoint_iff_raw, mem_rawTpoint_iff_raw, hL] at h1
  rw [Bool.eq_iff_iff, rawTpointTest_eq_true_iff, rawTpointTest_eq_true_iff, hL]
  exact ⟨fun hA => (h1.1 ⟨hjq, hA⟩).2, fun hB => (h1.2 ⟨hjq, hB⟩).2⟩

section Spec

variable {ϕ : genGroup gens →* Perm (Fin m)} {dom gdom : List ℕ}

/-- **Eq. (52) on raw data**: the routine lists exactly the points of `T(u)`. -/
theorem mem_rawTpoint_iff (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK m (Babai.maxOrbitLength (genGroup gens))) (u : Fin n) (j : ℕ) :
    j ∈ rawTpoint (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), (u : ℕ))
      ↔ ∃ h : j < m, (⟨j, h⟩ : Fin m) ∈ Babai.Tpoint ϕ u := by
  classical
  set H : Subgroup (Perm (Fin m)) := (stabilizer (genGroup gens) u).map ϕ with hH
  set T : Set (Fin m) := Babai.Tpoint ϕ u with hT
  -- Theorem 10.5.1 (a)
  have hitem := Babai.theorem_10_5_1_a ϕ hϕ hk u
  have hsand : Babai.IsSandwichSet H T := hitem.1.2
  have h4 : 4 * T.ncard < m := hitem.1.1
  have h9 : 9 ≤ m := hk.largeK.eight_lt
  have hcard : Nat.card (Fin m) = m := by simp
  have h3 : 3 ≤ (Tᶜ : Set (Fin m)).ncard :=
    Babai.three_le_ncard_compl_of_four_mul_lt (by rw [hcard]; exact h4) (by omega)
  have hshort : T = {a : Fin m | 2 * (orbit H a).ncard < Nat.card (Fin m)} :=
    Babai.eq_setOf_two_mul_ncard_orbit_lt hsand h3
  -- the generators the machine has
  have hgens : decGroup m (rawTopStabGens (((dom, gens.map (encPerm n)),
      (gdom, imgs.map (encPerm m))), (u : ℕ))) = H := decGroup_rawTopStabGens hd hg hI u
  have hwf : RawGens.WF m (rawTopStabGens (((dom, gens.map (encPerm n)),
      (gdom, imgs.map (encPerm m))), (u : ℕ))) := wf_rawTopStabGens hd hg hI u
  rw [mem_rawTpoint_iff_raw]
  show (j < gdom.length ∧
      2 * (rawOrbit (rawTopStabGens (((dom, gens.map (encPerm n)),
        (gdom, imgs.map (encPerm m))), (u : ℕ)), j)).length < gdom.length) ↔ _
  rw [hg]
  constructor
  · rintro ⟨hjm, htest⟩
    refine ⟨hjm, ?_⟩
    rw [hshort, Set.mem_setOf_eq, hcard]
    have hlen := length_rawOrbit_eq_ncard hwf (i := j) hjm
    rw [hgens] at hlen
    rw [← hlen]
    exact htest
  · rintro ⟨hjm, hmem⟩
    refine ⟨hjm, ?_⟩
    rw [hshort, Set.mem_setOf_eq, hcard] at hmem
    have hlen := length_rawOrbit_eq_ncard hwf (i := j) hjm
    rw [hgens] at hlen
    rw [hlen]
    exact hmem

/-- **Theorem 10.5.1 (a) on the RAM**: the set the routine returns is `T(u)`. -/
theorem winSet_rawTpoint (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK m (Babai.maxOrbitLength (genGroup gens))) (u : Fin n) :
    winSet m (rawTpoint (((dom, gens.map (encPerm n)),
        (gdom, imgs.map (encPerm m))), (u : ℕ)))
      = Babai.Tpoint ϕ u := by
  ext x
  rw [mem_winSet, mem_rawTpoint_iff hd hg hI hϕ hk]
  constructor
  · rintro ⟨h, hx⟩
    have : (⟨(x : ℕ), h⟩ : Fin m) = x := Fin.eta _ _
    rwa [this] at hx
  · intro hx
    exact ⟨x.isLt, by simpa using hx⟩

/-- Two points have the same `T` exactly when the routine returns the same list for them.
Both answers are filters of the same list, so list equality and equality of the sets are
the same thing. -/
theorem rawTpoint_eq_iff (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK m (Babai.maxOrbitLength (genGroup gens))) (u v : Fin n) :
    rawTpoint (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), (u : ℕ))
        = rawTpoint (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), (v : ℕ))
      ↔ Babai.Tpoint ϕ u = Babai.Tpoint ϕ v := by
  constructor
  · intro heq
    rw [← winSet_rawTpoint hd hg hI hϕ hk u, ← winSet_rawTpoint hd hg hI hϕ hk v, heq]
  · intro heq
    refine rawTpoint_eq_of_mem_iff rfl (fun j => ?_)
    rw [mem_rawTpoint_iff hd hg hI hϕ hk, mem_rawTpoint_iff hd hg hI hϕ hk, heq]

end Spec

/-! ## The table of all the sets `T(u)` -/

/-- **The table `u ↦ T(u)`**, one row per point of `Ω`.  The points are read off the length
of the domain witness of `Ω`. -/
def rawTpointAll (p : RawAction) : List (List ℕ) :=
  (List.range p.1.1.length).map (fun u => rawTpoint (p, u))

@[simp] theorem length_rawTpointAll (p : RawAction) :
    (rawTpointAll p).length = p.1.1.length := by
  simp [rawTpointAll]

/-- The row of a point is the set of that point. -/
theorem getD_rawTpointAll {p : RawAction} {u : ℕ} (hu : u < p.1.1.length) :
    (rawTpointAll p).getD u [] = rawTpoint (p, u) := by
  rw [rawTpointAll, List.getD_eq_getElem _ _ (by simpa using hu), List.getElem_map,
    List.getElem_range]

section TableSpec

variable {ϕ : genGroup gens →* Perm (Fin m)} {dom gdom : List ℕ}

/-- **The table is the table of the sets `T(u)`.** -/
theorem winSet_getD_rawTpointAll (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK m (Babai.maxOrbitLength (genGroup gens))) (u : Fin n) :
    winSet m ((rawTpointAll ((dom, gens.map (encPerm n)),
        (gdom, imgs.map (encPerm m)))).getD (u : ℕ) [])
      = Babai.Tpoint ϕ u := by
  rw [getD_rawTpointAll (by simpa [hd] using u.isLt)]
  exact winSet_rawTpoint hd hg hI hϕ hk u

end TableSpec

/-! ## The time classes -/

set_option maxHeartbeats 1000000 in
theorem polyFun_rawTStabOrbit :
    PolyFun (fun z : (RawAction × ℕ) × ℕ => rawOrbit (rawTopStabGens z.1, z.2)) :=
  ((polyFun_fst.comp polyFun_rawTopStabGens).pair polyFun_snd).comp polyFun_rawOrbit

set_option maxHeartbeats 1000000 in
theorem polyFun_rawTpointTest : PolyFun rawTpointTest := by
  have hlen : PolyFun (fun z : (RawAction × ℕ) × ℕ =>
      2 * (rawOrbit (rawTopStabGens z.1, z.2)).length) :=
    (polyFun_const 2).mul (polyFun_rawTStabOrbit.comp polyFun_length)
  have hgl : PolyFun (fun z : (RawAction × ℕ) × ℕ => z.1.1.2.1.length) :=
    (polyFun_fst.comp ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)).comp
      polyFun_length
  refine ((hlen.add (polyFun_const 1)).le hgl).of_eq (fun z => ?_)
  simp only [rawTpointTest]
  exact decide_eq_decide.2 (by omega)

set_option maxHeartbeats 1000000 in
theorem polyFun_rawTpoint : PolyFun rawTpoint := by
  have hrange : PolyFun (fun p : RawAction × ℕ => List.range p.1.2.1.length) :=
    ((polyFun_fst.comp polyFun_snd).comp polyFun_fst).comp polyFun_rangeLength
  exact ((polyFun_id.pair hrange).comp
    (PolyFun.filterParam polyFun_rawTpointTest)).of_eq (fun _ => rfl)

set_option maxHeartbeats 4000000 in
theorem polyFun_rawTpointAll : PolyFun rawTpointAll := by
  have hrange : PolyFun (fun p : RawAction => List.range p.1.1.length) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_rangeLength
  have hf : PolyFun (fun z : RawAction × ℕ => rawTpoint (z.1, z.2)) :=
    (polyFun_fst.pair polyFun_snd).comp polyFun_rawTpoint
  exact ((polyFun_id.pair hrange).comp (PolyFun.mapParam hf)).of_eq (fun _ => rfl)

end Algo
