/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align, line 4 — the coloring of `Ω` induced by the
coloring of `Γ`, as raw data.
-/
import Workspace.Algo.TpointRaw
import Workspace.Algo.BlockSystem
import Workspace.Master.AlignClasses

/-!
# Procedure Align, line 4, on the RAM (§14.1)

> 4. (: Each of our structures has an underlying coloring – possibly trivial :)
>    Let `(Δ₁, …, Δ_k)` be the coloring of `X(x)`; so `Γ` is the disjoint union of the
>    `Δ_j`.  This coloring induces a canonical coloring of `Φ = (Γ choose t)` as described
>    in Lemma 7.2.1; let `Φ₁, …, Φ_s` be the color classes.  This coloring in turn lifts to
>    a canonical coloring of `Ω` with corresponding color classes `Ω₁, …, Ω_s` where
>    `Ω_i = ⋃_{T ∈ Φ_i} B_T`.
> 6. If `(∃ j)(|Δ_j| > m/2)` ("dominant color") then start the application of the Chain
>    Rule with the window `Ω(Δ_j) = ⋃_{T ∈ (Δ_j choose t)} B_T`.

The coloring of `Γ` arrives as a labelling (`Algo.RawLab`, one label per point of `Γ`); the
color classes `Δ_j` are its fibres.  The label `T(u)` of a point of `Ω` is
`Algo.rawTpoint` (`Workspace/Algo/TpointRaw.lean`).  So line 4 needs nothing new: the color
of `u` is the vector of the numbers `|T(u) ∩ Δ_j|`, which is `Babai.omegaColor`
(`Workspace/Canonical/Defs.lean`), and the class of `u` is the set of points of the same
color, which is `Babai.omegaColorClass` (`Workspace/Master/AlignClasses.lean`).

**How the color vector is written down.**  `Babai.omegaColor ϕ c u` is a function on the
*color type*.  A machine cannot hold a function, and it must not loop over a range of
colors either, because a color is a machine natural.  So the color of `u` is written as one
entry per *point* of `Γ`: the entry at `i ∈ Γ` is `|T(u) ∩ Δ|` for the class `Δ` of `i`.
Two points of `Ω` get the same list exactly when they get the same `Babai.omegaColor`
(`Algo.alignRColor_eq_iff`): a color that no point of `Γ` carries contributes `0` on both
sides, and the other colors are the ones the list runs over.

**The order of the windows** (lines 5 and 6).  `Algo.alignRClasses` lists the classes in the
order of their *least* point, which is canonical.  `Algo.alignRWindows` is that list with
line 6 applied: when a color class `Δ_j` has more than half of `Γ`, the window `Ω(Δ_j)`
heads the list and is dropped from the rest.  `Ω(Δ_j)` is a color class of `Ω` whenever it
has a point (`Babai.omegaColorClass_eq_omegaOf`), so this is a reordering and not a longer
list — except when `Ω(Δ_j)` is empty, where one empty window is prepended, which is the
call line 6 asks for.

## Main results

* `Algo.alignRColor`, `Algo.alignRColor_eq_iff` — line 4's color of a point of `Ω`;
* `Algo.alignROmegaClass`, `Algo.winSet_alignROmegaClass` — the class `Ω_i` of a point;
* `Algo.alignRClasses`, `Algo.alignRClasses_cover` — the classes, in canonical order;
* `Algo.alignRDomWindow`, `Algo.winSet_alignRDomWindow` — line 6's window `Ω(Δ_j)`;
* `Algo.alignRWindows`, `Algo.alignRWindows_cover`, `Algo.alignRWindows_head_dominant` —
  the list the Chain Rule of line 5 runs over;
* `Algo.polyFun_alignRColor`, …, `Algo.polyFun_alignRWindows` — the running time.

No axiom, no `sorry`.
-/

namespace Algo

open RAM RAM.Targets MulAction
open Equiv (Perm)

variable {n m : ℕ} {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}

/-! ## Counting inside `T(u)`

Every routine of this file counts the points of `T(u)` that pass a test.  One lemma does
all the counting: the length of the filtered list is the size of the corresponding subset
of `Γ`. -/

section Count

variable {ϕ : genGroup gens →* Perm (Fin m)} {dom gdom : List ℕ}

/-- **The filtered label, counted.**  The routine's list is repetition-free and its entries
are the points of `T(u)` that pass the test, so its length is the size of that set. -/
theorem length_filter_rawTpoint (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK m (Babai.maxOrbitLength (genGroup gens))) (u : Fin n)
    (P : ℕ → Bool) :
    ((rawTpoint ((((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))) : RawAction),
        (u : ℕ))).filter P).length
      = (Babai.Tpoint ϕ u ∩ {γ : Fin m | P (γ : ℕ) = true}).ncard := by
  classical
  set L : List ℕ := (rawTpoint ((((dom, gens.map (encPerm n)),
    (gdom, imgs.map (encPerm m))) : RawAction), (u : ℕ))).filter P with hL
  have hnd : L.Nodup := List.Nodup.filter _ (nodup_rawTpoint _)
  have himg : (fun x : Fin m => (x : ℕ)) ''
      (Babai.Tpoint ϕ u ∩ {γ : Fin m | P (γ : ℕ) = true}) = {j : ℕ | j ∈ L} := by
    ext j
    constructor
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      rw [Set.mem_setOf_eq, hL, List.mem_filter]
      exact ⟨(mem_rawTpoint_iff hd hg hI hϕ hk u (x : ℕ)).2 ⟨x.isLt, by simpa using hx1⟩, hx2⟩
    · intro hj
      rw [Set.mem_setOf_eq, hL, List.mem_filter] at hj
      obtain ⟨hjm, hjT⟩ := (mem_rawTpoint_iff hd hg hI hϕ hk u j).1 hj.1
      exact ⟨⟨j, hjm⟩, ⟨hjT, hj.2⟩, rfl⟩
  have hlen : ({j : ℕ | j ∈ L}).ncard = L.length := by
    rw [← List.coe_toFinset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
  rw [← hlen, ← himg, Set.ncard_image_of_injective _ Fin.val_injective]

end Count

/-! ## Line 4: the color of a point of `Ω` -/

/-- The test the color vector counts with: the point `j` of `Γ` has the same color as the
point `i` of `Γ`.  Naming the test keeps the running-time proof inside the heartbeat
budget. -/
def alignRSameCol (v : ((RawAction × RawLab) × ℕ × ℕ) × ℕ) : Bool :=
  decide (labAt v.1.1.2 v.2 = labAt v.1.1.2 v.1.2.2)

/-- §14.1, **line 4**: one entry of the color of `u ∈ Ω` — the number of points of the
label `T(u)` whose color is the color of the point `i` of `Γ`. -/
def alignRColorAt (w : (RawAction × RawLab) × ℕ × ℕ) : ℕ :=
  ((rawTpoint (w.1.1, w.2.1)).filter (fun j => alignRSameCol (w, j))).length

/-- §14.1, **line 4**: the color of `u ∈ Ω`, written as one entry per point of `Γ`.  The
entry at `i` is `|T(u) ∩ Δ|` for the color class `Δ` of `i`. -/
def alignRColor (z : (RawAction × RawLab) × ℕ) : List ℕ :=
  (List.range z.1.1.2.1.length).map (fun i => alignRColorAt (z.1, (z.2, i)))

@[simp] theorem length_alignRColor (z : (RawAction × RawLab) × ℕ) :
    (alignRColor z).length = z.1.1.2.1.length := by
  simp [alignRColor]

theorem getD_alignRColor {z : (RawAction × RawLab) × ℕ} {i : ℕ}
    (hi : i < z.1.1.2.1.length) :
    (alignRColor z).getD i 0 = alignRColorAt (z.1, (z.2, i)) := by
  rw [alignRColor, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    List.getElem_range]

section ColorSpec

variable {ϕ : genGroup gens →* Perm (Fin m)} {dom gdom lab : List ℕ}

/-- **One entry of the color vector is one entry of `Babai.omegaColor`.** -/
theorem alignRColorAt_eq (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK m (Babai.maxOrbitLength (genGroup gens))) (u : Fin n) (i : ℕ) :
    alignRColorAt (((((dom, gens.map (encPerm n)),
        (gdom, imgs.map (encPerm m))) : RawAction), lab), ((u : ℕ), i))
      = Babai.omegaColor ϕ (fun γ : Fin m => labAt lab (γ : ℕ)) u (labAt lab i) := by
  show ((rawTpoint ((((dom, gens.map (encPerm n)),
      (gdom, imgs.map (encPerm m))) : RawAction), (u : ℕ))).filter
      (fun j => alignRSameCol (((((((dom, gens.map (encPerm n)),
        (gdom, imgs.map (encPerm m))) : RawAction), lab), ((u : ℕ), i))), j))).length = _
  rw [length_filter_rawTpoint hd hg hI hϕ hk u
    (fun j => alignRSameCol (((((((dom, gens.map (encPerm n)),
      (gdom, imgs.map (encPerm m))) : RawAction), lab), ((u : ℕ), i))), j))]
  show _ = (Babai.Tpoint ϕ u ∩ {γ : Fin m | labAt lab (γ : ℕ) = labAt lab i}).ncard
  refine congrArg Set.ncard ?_
  ext γ
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, alignRSameCol, decide_eq_true_iff]

/-- **Two points of `Ω` get the same list exactly when they get the same color** in the
sense of `Babai.omegaColor`.  A color that no point of `Γ` carries meets no label, so it
contributes `0` to both vectors and the list needs no entry for it. -/
theorem alignRColor_eq_iff (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK m (Babai.maxOrbitLength (genGroup gens))) (u v : Fin n) :
    alignRColor (((((dom, gens.map (encPerm n)),
          (gdom, imgs.map (encPerm m))) : RawAction), lab), (u : ℕ))
        = alignRColor (((((dom, gens.map (encPerm n)),
          (gdom, imgs.map (encPerm m))) : RawAction), lab), (v : ℕ))
      ↔ Babai.omegaColor ϕ (fun γ : Fin m => labAt lab (γ : ℕ)) u
          = Babai.omegaColor ϕ (fun γ : Fin m => labAt lab (γ : ℕ)) v := by
  classical
  set cc : Fin m → ℕ := fun γ => labAt lab (γ : ℕ) with hcc
  constructor
  · intro hlist
    funext k
    by_cases hk' : ∃ γ : Fin m, cc γ = k
    · obtain ⟨γ, rfl⟩ := hk'
      have hγ : (γ : ℕ) < gdom.length := by rw [hg]; exact γ.isLt
      have h1 := congrArg (fun l : List ℕ => l.getD (γ : ℕ) 0) hlist
      simp only at h1
      rw [getD_alignRColor (by simpa using hγ), getD_alignRColor (by simpa using hγ),
        alignRColorAt_eq hd hg hI hϕ hk u (γ : ℕ),
        alignRColorAt_eq hd hg hI hϕ hk v (γ : ℕ)] at h1
      exact h1
    · push_neg at hk'
      have hempty : ∀ w : Fin n, Babai.Tpoint ϕ w ∩ {γ : Fin m | cc γ = k} = ∅ := by
        intro w
        rw [Set.eq_empty_iff_forall_notMem]
        rintro γ ⟨-, hγ⟩
        exact hk' γ hγ
      show (Babai.Tpoint ϕ u ∩ {γ : Fin m | cc γ = k}).ncard
        = (Babai.Tpoint ϕ v ∩ {γ : Fin m | cc γ = k}).ncard
      rw [hempty u, hempty v]
  · intro hcol
    rw [alignRColor, alignRColor]
    refine List.map_congr_left (fun i hi => ?_)
    have hi' : i < gdom.length := List.mem_range.1 hi
    rw [alignRColorAt_eq hd hg hI hϕ hk u i, alignRColorAt_eq hd hg hI hϕ hk v i, hcol]

end ColorSpec

/-! ## Line 4: the color classes `Ω_i` -/

/-- The test of `Algo.alignROmegaClass`: the point `v` of `Ω` has the color of the point
`u`. -/
def alignRSameOmega (w : ((RawAction × RawLab) × ℕ) × ℕ) : Bool :=
  decide (alignRColor (w.1.1, w.2) = alignRColor w.1)

/-- §14.1, **line 4**: the color class `Ω_i` of the point `u` — the points of `Ω` whose
label has the same color vector as the label of `u`. -/
def alignROmegaClass (z : (RawAction × RawLab) × ℕ) : List ℕ :=
  (List.range z.1.1.1.1.length).filter (fun v => alignRSameOmega (z, v))

theorem mem_alignROmegaClass {z : (RawAction × RawLab) × ℕ} {v : ℕ} :
    v ∈ alignROmegaClass z ↔
      v < z.1.1.1.1.length ∧ alignRColor (z.1, v) = alignRColor z := by
  rw [alignROmegaClass, List.mem_filter, List.mem_range, alignRSameOmega, decide_eq_true_iff]

theorem nodup_alignROmegaClass (z : (RawAction × RawLab) × ℕ) :
    (alignROmegaClass z).Nodup :=
  List.Nodup.filter _ List.nodup_range

/-- A point of `Ω` lies in its own class. -/
theorem self_mem_alignROmegaClass {z : (RawAction × RawLab) × ℕ}
    (hu : z.2 < z.1.1.1.1.length) : z.2 ∈ alignROmegaClass z :=
  mem_alignROmegaClass.2 ⟨hu, rfl⟩

/-- Points of the same color have the same class, as a list. -/
theorem alignROmegaClass_congr {q : RawAction × RawLab} {u v : ℕ}
    (h : alignRColor (q, u) = alignRColor (q, v)) :
    alignROmegaClass (q, u) = alignROmegaClass (q, v) := by
  rw [alignROmegaClass, alignROmegaClass]
  refine List.filter_congr (fun w _ => ?_)
  rw [alignRSameOmega, alignRSameOmega]
  simp only
  rw [h]

section ClassSpec

variable {ϕ : genGroup gens →* Perm (Fin m)} {dom gdom lab : List ℕ}

/-- **The class the routine returns is the color class of `u`**: the points of `Ω` with the
same `Babai.omegaColor`.  This set is `Babai.omegaColorClass ϕ c (Babai.omegaColor ϕ c u)`
with its definition unfolded; the Lean definition of `Babai.omegaColorClass` carries a
`Fintype` on the type of colors, and the colors here are naturals, so the class is written
out instead of named. -/
theorem winSet_alignROmegaClass (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK m (Babai.maxOrbitLength (genGroup gens))) (u : Fin n) :
    winSet n (alignROmegaClass (((((dom, gens.map (encPerm n)),
        (gdom, imgs.map (encPerm m))) : RawAction), lab), (u : ℕ)))
      = {v : Fin n | Babai.omegaColor ϕ (fun γ : Fin m => labAt lab (γ : ℕ)) v
          = Babai.omegaColor ϕ (fun γ : Fin m => labAt lab (γ : ℕ)) u} := by
  ext v
  rw [mem_winSet, mem_alignROmegaClass, Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, h⟩
    exact (alignRColor_eq_iff hd hg hI hϕ hk v u).1 h
  · intro h
    exact ⟨by rw [hd]; exact v.isLt, (alignRColor_eq_iff hd hg hI hϕ hk v u).2 h⟩

end ClassSpec

/-! ## The classes in canonical order -/

/-- The point `u` is the first point of its class.  The class is a filter of the points of
`Ω` in increasing order, so its first point is its least one. -/
def alignRIsFirst (z : (RawAction × RawLab) × ℕ) : Bool :=
  decide (rawGet (alignROmegaClass z, 0) = z.2)

/-- §14.1, **line 4**: the color classes `Ω₁, …, Ω_s`, one entry per class, in the order of
their least points.  The order is canonical: it depends on the coloring and on nothing
else. -/
def alignRClasses (q : RawAction × RawLab) : List (List ℕ) :=
  ((List.range q.1.1.1.length).filter (fun u => alignRIsFirst (q, u))).map
    (fun u => alignROmegaClass (q, u))

theorem mem_alignRClasses {q : RawAction × RawLab} {W : List ℕ} (h : W ∈ alignRClasses q) :
    ∃ u, u < q.1.1.1.length ∧ W = alignROmegaClass (q, u) := by
  rw [alignRClasses, List.mem_map] at h
  obtain ⟨u, hu, rfl⟩ := h
  exact ⟨u, List.mem_range.1 (List.mem_of_mem_filter hu), rfl⟩

theorem length_alignRClasses_le (q : RawAction × RawLab) :
    (alignRClasses q).length ≤ q.1.1.1.length := by
  rw [alignRClasses, List.length_map]
  exact le_trans (List.length_filter_le _ _) (by simp)

/-- **The classes cover `Ω`**: every point of `Ω` lies in one of the listed classes. -/
theorem alignRClasses_cover {q : RawAction × RawLab} {u : ℕ} (hu : u < q.1.1.1.length) :
    ∃ W ∈ alignRClasses q, u ∈ W := by
  have hmem : u ∈ alignROmegaClass (q, u) := self_mem_alignROmegaClass (z := (q, u)) hu
  have hlen : 0 < (alignROmegaClass (q, u)).length := List.length_pos_iff_exists_mem.2 ⟨u, hmem⟩
  set u₀ : ℕ := rawGet (alignROmegaClass (q, u), 0) with hu₀
  have h0mem : u₀ ∈ alignROmegaClass (q, u) := by
    rw [hu₀, rawGet, List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem hlen
  obtain ⟨h0lt, h0col⟩ := mem_alignROmegaClass.1 h0mem
  have heq : alignROmegaClass (q, u₀) = alignROmegaClass (q, u) :=
    alignROmegaClass_congr (q := q) h0col
  refine ⟨alignROmegaClass (q, u), ?_, hmem⟩
  rw [alignRClasses, List.mem_map]
  refine ⟨u₀, ?_, heq⟩
  rw [List.mem_filter, List.mem_range]
  refine ⟨h0lt, ?_⟩
  rw [alignRIsFirst, decide_eq_true_iff]
  show rawGet (alignROmegaClass (q, u₀), 0) = u₀
  rw [heq]

/-! ## Line 6: the dominant color and its window -/

/-- The test of line 6: the color class of the point `i` of `Γ` has more than half of the
points of `Γ`. -/
def alignRDomTest (z : (RawAction × RawLab) × ℕ) : Bool :=
  decide (z.1.1.2.1.length <
    2 * ((List.range z.1.1.2.1.length).filter
      (fun j => decide (labAt z.1.2 j = labAt z.1.2 z.2))).length)

/-- The points of `Γ` whose color class is dominant. -/
def alignRDomPoints (q : RawAction × RawLab) : List ℕ :=
  (List.range q.1.2.1.length).filter (fun i => alignRDomTest (q, i))

/-- §14.1, **line 6**: is there a dominant color? -/
def alignRHasDom (q : RawAction × RawLab) : Bool :=
  decide (0 < (alignRDomPoints q).length)

/-- §14.1, **line 6**: the dominant color, read off the first point of `Γ` that carries
one.  Its value is used only when `Algo.alignRHasDom` says there is one. -/
def alignRDomColor (q : RawAction × RawLab) : ℕ :=
  labAt q.2 ((alignRDomPoints q).getD 0 0)

/-- The test inside `Algo.alignRDomWindow`: the point `j` of `Γ` does *not* carry the given
color. -/
def alignRDomNe (v : ((RawAction × RawLab) × ℕ) × ℕ) : Bool :=
  decide (labAt v.1.1.2 v.2 ≠ v.1.2)

/-- The test of `Algo.alignRDomWindow`: the whole label `T(u)` carries the given color. -/
def alignRDomOff (w : ((RawAction × RawLab) × ℕ) × ℕ) : Bool :=
  decide (((rawTpoint (w.1.1.1, w.2)).filter (fun j => alignRDomNe (w.1, j))).length = 0)

/-- §14.1, **line 6**: the window `Ω(Δ_j) = ⋃_{T ∈ (Δ_j choose t)} B_T` for the color `k` —
the points of `Ω` whose label lies inside the color class of `k`. -/
def alignRDomWindow (z : (RawAction × RawLab) × ℕ) : List ℕ :=
  (List.range z.1.1.1.1.length).filter (fun u => alignRDomOff (z, u))

theorem mem_alignRDomWindow {z : (RawAction × RawLab) × ℕ} {u : ℕ} :
    u ∈ alignRDomWindow z ↔
      u < z.1.1.1.1.length ∧ ∀ j ∈ rawTpoint (z.1.1, u), labAt z.1.2 j = z.2 := by
  rw [alignRDomWindow, List.mem_filter, List.mem_range, alignRDomOff, decide_eq_true_iff,
    List.length_eq_zero_iff, List.filter_eq_nil_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun j hj => ?_⟩
    have := h2 j hj
    rw [alignRDomNe, decide_eq_true_iff] at this
    exact not_not.1 this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun j hj => ?_⟩
    rw [alignRDomNe, decide_eq_true_iff]
    exact fun hne => hne (h2 j hj)

theorem nodup_alignRDomWindow (z : (RawAction × RawLab) × ℕ) :
    (alignRDomWindow z).Nodup :=
  List.Nodup.filter _ List.nodup_range

section DomSpec

variable {ϕ : genGroup gens →* Perm (Fin m)} {dom gdom lab : List ℕ}

/-- **The window the routine returns is `Ω(Δ)`** (`Babai.omegaOf`) for the color class `Δ`
of the color `k`. -/
theorem winSet_alignRDomWindow (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK m (Babai.maxOrbitLength (genGroup gens))) (k : ℕ) :
    winSet n (alignRDomWindow (((((dom, gens.map (encPerm n)),
        (gdom, imgs.map (encPerm m))) : RawAction), lab), k))
      = Babai.omegaOf ϕ {γ : Fin m | labAt lab (γ : ℕ) = k} := by
  ext u
  rw [mem_winSet, mem_alignRDomWindow, Babai.mem_omegaOf]
  constructor
  · rintro ⟨-, h⟩
    intro γ hγ
    have hmem : (γ : ℕ) ∈ rawTpoint ((((dom, gens.map (encPerm n)),
        (gdom, imgs.map (encPerm m))) : RawAction), (u : ℕ)) :=
      (mem_rawTpoint_iff hd hg hI hϕ hk u (γ : ℕ)).2 ⟨γ.isLt, by simpa using hγ⟩
    exact h (γ : ℕ) hmem
  · intro h
    refine ⟨by rw [hd]; exact u.isLt, fun j hj => ?_⟩
    obtain ⟨hjm, hjT⟩ := (mem_rawTpoint_iff hd hg hI hϕ hk u j).1 hj
    exact h hjT

/-- **Line 6's hypothesis, on raw data**: when the routine reports a dominant color, the
class of that color really has more than half of the points of `Γ`. -/
theorem alignRDomColor_dominant (hg : gdom.length = m)
    (h : alignRHasDom ((((dom, gens.map (encPerm n)),
      (gdom, imgs.map (encPerm m))) : RawAction), lab) = true) :
    m < 2 * ({γ : Fin m | labAt lab (γ : ℕ)
      = alignRDomColor ((((dom, gens.map (encPerm n)),
        (gdom, imgs.map (encPerm m))) : RawAction), lab)}).ncard := by
  classical
  set q : RawAction × RawLab := ((((dom, gens.map (encPerm n)),
    (gdom, imgs.map (encPerm m))) : RawAction), lab) with hq
  rw [alignRHasDom, decide_eq_true_iff, List.length_pos_iff_exists_mem] at h
  obtain ⟨i, hi⟩ := h
  have hi0 : (alignRDomPoints q).getD 0 0 ∈ alignRDomPoints q := by
    have hlen : 0 < (alignRDomPoints q).length := List.length_pos_iff_exists_mem.2 ⟨i, hi⟩
    rw [List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem hlen
  set i₀ : ℕ := (alignRDomPoints q).getD 0 0 with hi₀
  rw [alignRDomPoints, List.mem_filter] at hi0
  have htest := hi0.2
  rw [alignRDomTest, decide_eq_true_iff] at htest
  -- the filtered list of `Γ` is the color class, counted
  set L : List ℕ := (List.range gdom.length).filter
    (fun j => decide (labAt lab j = labAt lab i₀)) with hL
  have hnd : L.Nodup := List.Nodup.filter _ List.nodup_range
  have himg : (fun x : Fin m => (x : ℕ)) ''
      {γ : Fin m | labAt lab (γ : ℕ) = alignRDomColor q} = {j : ℕ | j ∈ L} := by
    ext j
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Set.mem_setOf_eq, hL, List.mem_filter, List.mem_range, decide_eq_true_iff]
      exact ⟨by rw [hg]; exact x.isLt, hx⟩
    · intro hj
      rw [Set.mem_setOf_eq, hL, List.mem_filter, List.mem_range, decide_eq_true_iff] at hj
      exact ⟨⟨j, by rw [← hg]; exact hj.1⟩, hj.2, rfl⟩
  have hcard : ({γ : Fin m | labAt lab (γ : ℕ) = alignRDomColor q}).ncard = L.length := by
    rw [← Set.ncard_image_of_injective _ Fin.val_injective, himg, ← List.coe_toFinset,
      Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
  rw [hcard]
  have : q.1.2.1.length = gdom.length := rfl
  rw [hq] at htest
  simpa [hg, hL, this] using htest

end DomSpec

/-! ## Lines 5 and 6: the list of windows -/

/-- The test that removes the dominant window from the list of the remaining classes. -/
def alignRNotDom (w : (RawAction × RawLab) × List ℕ) : Bool :=
  decide (w.2 ≠ alignRDomWindow (w.1, alignRDomColor w.1))

/-- §14.1, **lines 5 and 6**: the windows the Chain Rule of line 5 runs over, in the order
line 6 asks for.  With a dominant color the window `Ω(Δ_j)` comes first and is removed from
the rest of the list; with no dominant color the classes are taken in their canonical
order. -/
def alignRWindows (q : RawAction × RawLab) : List (List ℕ) :=
  if alignRHasDom q then
    alignRDomWindow (q, alignRDomColor q) ::
      (alignRClasses q).filter (fun W => alignRNotDom (q, W))
  else alignRClasses q

/-- **Line 6**: with a dominant color the first window is `Ω(Δ_j)`. -/
theorem alignRWindows_head_dominant {q : RawAction × RawLab} (h : alignRHasDom q = true) :
    (alignRWindows q).head? = some (alignRDomWindow (q, alignRDomColor q)) := by
  rw [alignRWindows, if_pos h]
  rfl

/-- With no dominant color the windows are the classes in their canonical order. -/
theorem alignRWindows_eq_classes {q : RawAction × RawLab} (h : alignRHasDom q = false) :
    alignRWindows q = alignRClasses q := by
  rw [alignRWindows, if_neg (by rw [h]; exact Bool.false_ne_true)]

/-- **The windows cover `Ω`.**  Line 6 only reorders the classes and drops the one it has
put first, so what is left still covers. -/
theorem alignRWindows_cover {q : RawAction × RawLab} {u : ℕ} (hu : u < q.1.1.1.length) :
    ∃ W ∈ alignRWindows q, u ∈ W := by
  obtain ⟨W, hW, huW⟩ := alignRClasses_cover hu
  rw [alignRWindows]
  by_cases hdom : alignRHasDom q = true
  · rw [if_pos hdom]
    by_cases hWd : W = alignRDomWindow (q, alignRDomColor q)
    · exact ⟨alignRDomWindow (q, alignRDomColor q), List.mem_cons_self, by rwa [← hWd]⟩
    · refine ⟨W, List.mem_cons_of_mem _ ?_, huW⟩
      rw [List.mem_filter]
      exact ⟨hW, by rw [alignRNotDom, decide_eq_true_iff]; exact hWd⟩
  · rw [if_neg (by simpa using hdom)]
    exact ⟨W, hW, huW⟩

/-- Every window is a class, or — in the dominant case — the window `Ω(Δ_j)`. -/
theorem alignRWindows_mem {q : RawAction × RawLab} {W : List ℕ} (hW : W ∈ alignRWindows q) :
    W = alignRDomWindow (q, alignRDomColor q) ∨ W ∈ alignRClasses q := by
  rw [alignRWindows] at hW
  by_cases hdom : alignRHasDom q = true
  · rw [if_pos hdom, List.mem_cons] at hW
    rcases hW with rfl | hW
    · exact Or.inl rfl
    · exact Or.inr (List.mem_of_mem_filter hW)
  · rw [if_neg (by simpa using hdom)] at hW
    exact Or.inr hW

/-- **The number of windows**, hence the number of calls line 5 makes: at most one per
color class of `Ω`, plus the window of line 6. -/
theorem length_alignRWindows_le (q : RawAction × RawLab) :
    (alignRWindows q).length ≤ q.1.1.1.length + 1 := by
  rw [alignRWindows]
  by_cases hdom : alignRHasDom q = true
  · rw [if_pos hdom, List.length_cons]
    have := le_trans (List.length_filter_le (fun W => alignRNotDom (q, W)) (alignRClasses q))
      (length_alignRClasses_le q)
    omega
  · rw [if_neg (by simpa using hdom)]
    have := length_alignRClasses_le q
    omega

/-- Every window is a repetition-free list of points of `Ω`. -/
theorem nodup_of_mem_alignRWindows {q : RawAction × RawLab} {W : List ℕ}
    (hW : W ∈ alignRWindows q) : W.Nodup := by
  rcases alignRWindows_mem hW with rfl | hW'
  · exact nodup_alignRDomWindow _
  · obtain ⟨u, -, rfl⟩ := mem_alignRClasses hW'
    exact nodup_alignROmegaClass _

theorem lt_of_mem_of_mem_alignRWindows {q : RawAction × RawLab} {W : List ℕ}
    (hW : W ∈ alignRWindows q) {u : ℕ} (hu : u ∈ W) : u < q.1.1.1.length := by
  rcases alignRWindows_mem hW with rfl | hW'
  · exact (mem_alignRDomWindow.1 hu).1
  · obtain ⟨v, -, rfl⟩ := mem_alignRClasses hW'
    exact (mem_alignROmegaClass.1 hu).1

/-! ## The time classes

`RAM.PolyFun.comp` composes the other way round: `h₁.comp h₂` applies `h₁` first.  So a
projection chain `z.1.1.2` is `(polyFun_fst.comp polyFun_fst).comp polyFun_snd`. -/

set_option maxHeartbeats 1000000 in
theorem polyFun_alignRSameCol : PolyFun alignRSameCol := by
  have h1 : PolyFun (fun v : ((RawAction × RawLab) × ℕ × ℕ) × ℕ => labAt v.1.1.2 v.2) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).pair polyFun_snd).comp polyFun_labAt
  have h2 : PolyFun (fun v : ((RawAction × RawLab) × ℕ × ℕ) × ℕ => labAt v.1.1.2 v.1.2.2) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).pair
      ((polyFun_fst.comp polyFun_snd).comp polyFun_snd)).comp polyFun_labAt
  exact (h1.natEq h2).of_eq (fun _ => rfl)

set_option maxHeartbeats 1000000 in
theorem polyFun_alignRColorAt : PolyFun alignRColorAt := by
  have hT : PolyFun (fun w : (RawAction × RawLab) × ℕ × ℕ => rawTpoint (w.1.1, w.2.1)) :=
    ((polyFun_fst.comp polyFun_fst).pair (polyFun_snd.comp polyFun_fst)).comp polyFun_rawTpoint
  exact (((polyFun_id.pair hT).comp (PolyFun.filterParam polyFun_alignRSameCol)).comp
    polyFun_length).of_eq (fun _ => rfl)

set_option maxHeartbeats 1000000 in
theorem polyFun_alignRColor : PolyFun alignRColor := by
  have hrange : PolyFun (fun z : (RawAction × RawLab) × ℕ =>
      List.range z.1.1.2.1.length) :=
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst).comp
      polyFun_rangeLength)
  have hf : PolyFun (fun w : ((RawAction × RawLab) × ℕ) × ℕ =>
      alignRColorAt (w.1.1, (w.1.2, w.2))) :=
    ((polyFun_fst.comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_snd).pair polyFun_snd)).comp polyFun_alignRColorAt
  exact ((polyFun_id.pair hrange).comp (PolyFun.mapParam hf)).of_eq (fun _ => rfl)

set_option maxHeartbeats 1000000 in
theorem polyFun_alignRSameOmega : PolyFun alignRSameOmega := by
  have h1 : PolyFun (fun w : ((RawAction × RawLab) × ℕ) × ℕ =>
      alignRColor (w.1.1, w.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_alignRColor
  have h2 : PolyFun (fun w : ((RawAction × RawLab) × ℕ) × ℕ => alignRColor w.1) :=
    polyFun_fst.comp polyFun_alignRColor
  exact ((h1.pair h2).comp polyFun_listNatEq).of_eq (fun _ => rfl)

set_option maxHeartbeats 1000000 in
theorem polyFun_alignROmegaClass : PolyFun alignROmegaClass := by
  have hrange : PolyFun (fun z : (RawAction × RawLab) × ℕ =>
      List.range z.1.1.1.1.length) :=
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst).comp
      polyFun_rangeLength)
  exact ((polyFun_id.pair hrange).comp
    (PolyFun.filterParam polyFun_alignRSameOmega)).of_eq (fun _ => rfl)

set_option maxHeartbeats 1000000 in
theorem polyFun_alignRIsFirst : PolyFun alignRIsFirst := by
  have h1 : PolyFun (fun z : (RawAction × RawLab) × ℕ =>
      rawGet (alignROmegaClass z, 0)) :=
    (polyFun_alignROmegaClass.pair (polyFun_const 0)).comp polyFun_rawGet
  exact (h1.natEq polyFun_snd).of_eq (fun _ => rfl)

set_option maxHeartbeats 1000000 in
theorem polyFun_alignRClasses : PolyFun alignRClasses := by
  have hrange : PolyFun (fun q : RawAction × RawLab => List.range q.1.1.1.length) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_rangeLength)
  have hfirst : PolyFun (fun w : (RawAction × RawLab) × ℕ => alignRIsFirst (w.1, w.2)) :=
    (polyFun_fst.pair polyFun_snd).comp polyFun_alignRIsFirst
  have hcl : PolyFun (fun w : (RawAction × RawLab) × ℕ => alignROmegaClass (w.1, w.2)) :=
    (polyFun_fst.pair polyFun_snd).comp polyFun_alignROmegaClass
  exact ((polyFun_id.pair ((polyFun_id.pair hrange).comp
    (PolyFun.filterParam hfirst))).comp (PolyFun.mapParam hcl)).of_eq (fun _ => rfl)

set_option maxHeartbeats 1000000 in
theorem polyFun_alignRDomTest : PolyFun alignRDomTest := by
  have hgl : PolyFun (fun z : (RawAction × RawLab) × ℕ => z.1.1.2.1.length) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst).comp polyFun_length
  have hrange : PolyFun (fun z : (RawAction × RawLab) × ℕ =>
      List.range z.1.1.2.1.length) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst).comp
      polyFun_rangeLength
  have hstep : PolyFun (fun w : ((RawAction × RawLab) × ℕ) × ℕ =>
      decide (labAt w.1.1.2 w.2 = labAt w.1.1.2 w.1.2)) := by
    have h1 : PolyFun (fun w : ((RawAction × RawLab) × ℕ) × ℕ => labAt w.1.1.2 w.2) :=
      (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).pair polyFun_snd).comp polyFun_labAt
    have h2 : PolyFun (fun w : ((RawAction × RawLab) × ℕ) × ℕ => labAt w.1.1.2 w.1.2) :=
      (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).pair
        (polyFun_fst.comp polyFun_snd)).comp polyFun_labAt
    exact h1.natEq h2
  have hcnt : PolyFun (fun z : (RawAction × RawLab) × ℕ =>
      2 * ((List.range z.1.1.2.1.length).filter
        (fun j => decide (labAt z.1.2 j = labAt z.1.2 z.2))).length) :=
    (polyFun_const 2).mul
      (((polyFun_id.pair hrange).comp (PolyFun.filterParam hstep)).comp polyFun_length)
  exact ((hgl.add (polyFun_const 1)).le hcnt).of_eq (fun z => by
    simp only [alignRDomTest]
    exact decide_eq_decide.2 (by omega))

set_option maxHeartbeats 1000000 in
theorem polyFun_alignRDomPoints : PolyFun alignRDomPoints := by
  have hrange : PolyFun (fun q : RawAction × RawLab => List.range q.1.2.1.length) :=
    ((polyFun_fst.comp polyFun_snd).comp polyFun_fst).comp polyFun_rangeLength
  have hstep : PolyFun (fun w : (RawAction × RawLab) × ℕ => alignRDomTest (w.1, w.2)) :=
    (polyFun_fst.pair polyFun_snd).comp polyFun_alignRDomTest
  exact ((polyFun_id.pair hrange).comp (PolyFun.filterParam hstep)).of_eq (fun _ => rfl)

theorem polyFun_alignRHasDom : PolyFun alignRHasDom :=
  ((polyFun_const 1).le (polyFun_alignRDomPoints.comp polyFun_length)).of_eq (fun q => by
    simp only [alignRHasDom]
    exact decide_eq_decide.2 (by omega))

theorem polyFun_alignRDomColor : PolyFun alignRDomColor :=
  ((polyFun_snd.pair ((polyFun_alignRDomPoints.pair (polyFun_const 0)).comp
    polyFun_rawGet)).comp polyFun_labAt).of_eq (fun _ => rfl)

set_option maxHeartbeats 1000000 in
theorem polyFun_alignRDomNe : PolyFun alignRDomNe := by
  have h1 : PolyFun (fun v : ((RawAction × RawLab) × ℕ) × ℕ => labAt v.1.1.2 v.2) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).pair polyFun_snd).comp polyFun_labAt
  have h2 : PolyFun (fun v : ((RawAction × RawLab) × ℕ) × ℕ => v.1.2) :=
    polyFun_fst.comp polyFun_snd
  exact (PolyFun.ite (h1.natEq h2) (polyFun_const false)
    (polyFun_const true)).of_eq (fun v => by
      by_cases h : labAt v.1.1.2 v.2 = v.1.2 <;> simp [alignRDomNe, h])

set_option maxHeartbeats 1000000 in
theorem polyFun_alignRDomOff : PolyFun alignRDomOff := by
  have hT : PolyFun (fun w : ((RawAction × RawLab) × ℕ) × ℕ =>
      rawTpoint (w.1.1.1, w.2)) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair polyFun_snd).comp
      polyFun_rawTpoint
  have hstep : PolyFun (fun v : (((RawAction × RawLab) × ℕ) × ℕ) × ℕ =>
      alignRDomNe (v.1.1, v.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_alignRDomNe
  exact ((((polyFun_id.pair hT).comp (PolyFun.filterParam hstep)).comp
    polyFun_length).natEq (polyFun_const 0)).of_eq (fun _ => rfl)

set_option maxHeartbeats 1000000 in
theorem polyFun_alignRDomWindow : PolyFun alignRDomWindow := by
  have hrange : PolyFun (fun z : (RawAction × RawLab) × ℕ =>
      List.range z.1.1.1.1.length) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst).comp
      polyFun_rangeLength
  have hstep : PolyFun (fun w : ((RawAction × RawLab) × ℕ) × ℕ => alignRDomOff (w.1, w.2)) :=
    (polyFun_fst.pair polyFun_snd).comp polyFun_alignRDomOff
  exact ((polyFun_id.pair hrange).comp (PolyFun.filterParam hstep)).of_eq (fun _ => rfl)

set_option maxHeartbeats 1000000 in
theorem polyFun_alignRNotDom : PolyFun alignRNotDom := by
  have h1 : PolyFun (fun w : (RawAction × RawLab) × List ℕ =>
      alignRDomWindow (w.1, alignRDomColor w.1)) :=
    (polyFun_fst.pair (polyFun_fst.comp polyFun_alignRDomColor)).comp polyFun_alignRDomWindow
  exact (PolyFun.ite ((polyFun_snd.pair h1).comp polyFun_listNatEq) (polyFun_const false)
    (polyFun_const true)).of_eq (fun w => by
      by_cases h : w.2 = alignRDomWindow (w.1, alignRDomColor w.1) <;>
        simp [alignRNotDom, h])

set_option maxHeartbeats 1000000 in
theorem polyFun_alignRWindows : PolyFun alignRWindows := by
  have hdw : PolyFun (fun q : RawAction × RawLab =>
      alignRDomWindow (q, alignRDomColor q)) :=
    (polyFun_id.pair polyFun_alignRDomColor).comp polyFun_alignRDomWindow
  have hstep : PolyFun (fun w : (RawAction × RawLab) × List ℕ => alignRNotDom (w.1, w.2)) :=
    (polyFun_fst.pair polyFun_snd).comp polyFun_alignRNotDom
  have hrest : PolyFun (fun q : RawAction × RawLab =>
      (alignRClasses q).filter (fun W => alignRNotDom (q, W))) :=
    ((polyFun_id.pair polyFun_alignRClasses).comp (PolyFun.filterParam hstep)).of_eq
      (fun _ => rfl)
  exact (PolyFun.ite polyFun_alignRHasDom ((hdw.pair hrest).comp polyFun_cons)
    polyFun_alignRClasses).of_eq (fun q => by
      by_cases h : alignRHasDom q = true <;> simp [alignRWindows, h])

end Algo
