/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the color classes `Ω_j` of Section 12 on the RAM.
-/
import Workspace.Algo.TpointRaw
import Workspace.TopAction.Classes

/-!
# The classes `Ω_j` on the RAM (§12)

Section 12 splits `Ω` by how much of the label `T(u)` lies inside a set `C ⊆ Γ`:

> `Ω_j = {u ∈ Ω | |T(u) ∩ C| = j}`  (`Babai.omegaCut`).

With `Algo.rawTpoint` (`Workspace/Algo/TpointRaw.lean`) this is one filter per class.

## Main results

* `Algo.rawOmegaCut` — the class `Ω_j`, as a list of points of `Ω`;
* `Algo.winSet_rawOmegaCut` — the class the routine returns is `Babai.omegaCut`;
* `Algo.rawOmegaCuts` — the classes `Ω_0, …, Ω_{t-1}`, in the order
  `Babai.topAction4Body` uses them;
* `Algo.polyFun_rawOmegaCut`, `Algo.polyFun_rawOmegaCuts` — the running time.

No axiom, no `sorry`.
-/

namespace Algo

open RAM RAM.Targets MulAction
open Equiv (Perm)

variable {n m : ℕ} {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}

/-! ## The size of `T(u) ∩ C` -/

/-- `T(u) ∩ C`, as a list: the points of the computed `T(u)` that lie in `C`. -/
def rawTcut (q : (RawAction × List ℕ) × ℕ) : List ℕ :=
  (rawTpoint (q.1.1, q.2)).filter (fun j => decide (j ∈ q.1.2))

theorem nodup_rawTcut (q : (RawAction × List ℕ) × ℕ) : (rawTcut q).Nodup :=
  List.Nodup.filter _ (nodup_rawTpoint _)

theorem mem_rawTcut {q : (RawAction × List ℕ) × ℕ} {j : ℕ} :
    j ∈ rawTcut q ↔ j ∈ rawTpoint (q.1.1, q.2) ∧ j ∈ q.1.2 := by
  rw [rawTcut, List.mem_filter, decide_eq_true_iff]

section Cut

variable {ϕ : genGroup gens →* Perm (Fin m)} {dom gdom : List ℕ}

/-- **The routine counts `|T(u) ∩ C|`.**  The answer is repetition-free and its entries are
the points of `T(u) ∩ C`, so its length is the size of that set. -/
theorem length_rawTcut (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK m (Babai.maxOrbitLength (genGroup gens))) (u : Fin n)
    (C : List ℕ) :
    (rawTcut (((((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))) : RawAction),
        C), (u : ℕ))).length
      = (Babai.Tpoint ϕ u ∩ winSet m C).ncard := by
  classical
  set q : (RawAction × List ℕ) × ℕ :=
    (((((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))) : RawAction), C),
      (u : ℕ)) with hq
  have hmem : ∀ j : ℕ, j ∈ rawTcut q ↔ j ∈ rawTpoint ((((dom, gens.map (encPerm n)),
      (gdom, imgs.map (encPerm m))) : RawAction), (u : ℕ)) ∧ j ∈ C := fun j => mem_rawTcut
  have himg : (fun x : Fin m => (x : ℕ)) '' (Babai.Tpoint ϕ u ∩ winSet m C)
      = {j : ℕ | j ∈ rawTcut q} := by
    ext j
    constructor
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      refine (hmem _).2 ⟨?_, hx2⟩
      exact (mem_rawTpoint_iff hd hg hI hϕ hk u (x : ℕ)).2 ⟨x.isLt, by simpa using hx1⟩
    · intro hj
      obtain ⟨hj1, hj2⟩ := (hmem j).1 hj
      obtain ⟨hjm, hjT⟩ := (mem_rawTpoint_iff hd hg hI hϕ hk u j).1 hj1
      exact ⟨⟨j, hjm⟩, ⟨hjT, hj2⟩, rfl⟩
  have hlen : ({j : ℕ | j ∈ rawTcut q}).ncard = (rawTcut q).length := by
    rw [← List.coe_toFinset, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup (nodup_rawTcut q)]
  rw [← hlen, ← himg, Set.ncard_image_of_injective _ Fin.val_injective]

end Cut

/-! ## The classes -/

/-- **The class `Ω_j`** of §12: the points `u` with `|T(u) ∩ C| = j`.  The points of `Ω` are
read off the *length* of the domain witness of `Ω`. -/
def rawOmegaCut (q : (RawAction × List ℕ) × ℕ) : List ℕ :=
  (List.range q.1.1.1.1.length).filter
    (fun u => decide ((rawTcut ((q.1.1, q.1.2), u)).length = q.2))

theorem mem_rawOmegaCut {q : (RawAction × List ℕ) × ℕ} {u : ℕ} :
    u ∈ rawOmegaCut q ↔
      u < q.1.1.1.1.length ∧ (rawTcut ((q.1.1, q.1.2), u)).length = q.2 := by
  rw [rawOmegaCut, List.mem_filter, List.mem_range, decide_eq_true_iff]

section Classes

variable {ϕ : genGroup gens →* Perm (Fin m)} {dom gdom : List ℕ}

/-- **The routine returns `Ω_j`** (`Babai.omegaCut`, §12). -/
theorem winSet_rawOmegaCut (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK m (Babai.maxOrbitLength (genGroup gens)))
    (C : List ℕ) (j : ℕ) :
    winSet n (rawOmegaCut (((((dom, gens.map (encPerm n)),
        (gdom, imgs.map (encPerm m))) : RawAction), C), j))
      = Babai.omegaCut ϕ (winSet m C) j := by
  ext u
  rw [mem_winSet, mem_rawOmegaCut, Babai.mem_omegaCut,
    ← length_rawTcut hd hg hI hϕ hk u C]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    exact ⟨by rw [hd]; exact u.isLt, h⟩

end Classes

/-- **The classes `Ω_0, …, Ω_{t-1}`**, in the order the Chain Rule of
`Babai.topAction4Body` walks them.  The counter `t` is a list length, never a machine
natural. -/
def rawOmegaCuts (q : (RawAction × List ℕ) × List ℕ) : List (List ℕ) :=
  (List.range q.2.length).map (fun j => rawOmegaCut (q.1, j))

theorem getD_rawOmegaCuts {q : (RawAction × List ℕ) × List ℕ} {j : ℕ} (hj : j < q.2.length) :
    (rawOmegaCuts q).getD j [] = rawOmegaCut (q.1, j) := by
  rw [rawOmegaCuts, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
    List.getElem_range]

section Order

variable {ϕ : genGroup gens →* Perm (Fin m)} {dom gdom : List ℕ}

/-- **The list of windows the Chain Rule of `Babai.topAction4Body` walks**: the classes
`Ω_0, …, Ω_{t-1}` in that order, with `t` the length of the counter list. -/
theorem map_winSet_rawOmegaCuts (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK m (Babai.maxOrbitLength (genGroup gens)))
    (C tl : List ℕ) :
    (rawOmegaCuts (((((dom, gens.map (encPerm n)),
          (gdom, imgs.map (encPerm m))) : RawAction), C), tl)).map (winSet n)
      = (List.range tl.length).map (Babai.omegaCut ϕ (winSet m C)) := by
  rw [rawOmegaCuts, List.map_map]
  refine List.map_congr_left (fun j _ => ?_)
  exact winSet_rawOmegaCut hd hg hI hϕ hk C j

end Order

/-! ## The time classes -/

set_option maxHeartbeats 1000000 in
theorem polyFun_rawTcut : PolyFun rawTcut := by
  have hT : PolyFun (fun q : (RawAction × List ℕ) × ℕ => rawTpoint (q.1.1, q.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_rawTpoint
  have hstep : PolyFun (fun z : ((RawAction × List ℕ) × ℕ) × ℕ =>
      decide (z.2 ∈ z.1.1.2)) :=
    (polyFun_snd.pair (((polyFun_fst.comp polyFun_fst).comp polyFun_snd))).comp
      polyFun_natListMem
  exact ((polyFun_id.pair hT).comp (PolyFun.filterParam hstep)).of_eq (fun _ => rfl)

set_option maxHeartbeats 1000000 in
theorem polyFun_rawOmegaCut : PolyFun rawOmegaCut := by
  have hrange : PolyFun (fun q : (RawAction × List ℕ) × ℕ =>
      List.range q.1.1.1.1.length) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst).comp
      polyFun_rangeLength
  have hcut : PolyFun (fun z : ((RawAction × List ℕ) × ℕ) × ℕ =>
      (rawTcut ((z.1.1.1, z.1.1.2), z.2)).length) :=
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_fst).comp polyFun_snd)).pair polyFun_snd).comp
        (polyFun_rawTcut.comp polyFun_length)
  have hj : PolyFun (fun z : ((RawAction × List ℕ) × ℕ) × ℕ => z.1.2) :=
    polyFun_fst.comp polyFun_snd
  exact ((polyFun_id.pair hrange).comp (PolyFun.filterParam (hcut.natEq hj))).of_eq
    (fun _ => rfl)

set_option maxHeartbeats 1000000 in
theorem polyFun_rawOmegaCuts : PolyFun rawOmegaCuts := by
  have hrange : PolyFun (fun q : (RawAction × List ℕ) × List ℕ =>
      List.range q.2.length) :=
    polyFun_snd.comp polyFun_rangeLength
  have hf : PolyFun (fun z : ((RawAction × List ℕ) × List ℕ) × ℕ =>
      rawOmegaCut (z.1.1, z.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_rawOmegaCut
  exact ((polyFun_id.pair hrange).comp (PolyFun.mapParam hf)).of_eq (fun _ => rfl)

end Algo
