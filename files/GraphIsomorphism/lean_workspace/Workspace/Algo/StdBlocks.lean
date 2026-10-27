/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the standard blocks as raw data (§10.5, Proposition 10.5.4).
-/
import Workspace.Algo.StdBlocksProved
import Workspace.Algo.BlockSystem

/-!
# The standard blocks on the RAM (§10.5, Proposition 10.5.4)

Proposition 10.5.4 (§10.5, lines 4749–4752) reads

> Given a giant representation `ϕ : G → S_k`, we can find the standard blocks in each
> `G`-orbit in polynomial time.  *Proof.* Standard.

The paper gives no proof and no citation.  The polynomial-time half was an axiom by a
decision of the user and is now the theorem
`Algo.proposition_10_5_4` of `Workspace/Algo/StdBlocksProved.lean`.  What it gives is a
`RAM.PolyFun` that *labels the points*: two points get the same label exactly when one lies
in the standard block of the other.

This file turns that labelling into the data the rest of the algorithmic layer works with:

* `Algo.stdLab` is a routine the theorem provides, named by `Classical.choose` (the theorem
  is an existence statement; its witness is `Algo.tptLabels`);
* `Algo.rawStdBlocks` reads the classes of that labelling off as a `Algo.RawBlocks`, using
  `Algo.labBlocks` of `Workspace/Algo/BlockSystem.lean`.  Its blocks are exactly the standard
  blocks of *all* the orbits at once (`Algo.blockSets_rawStdBlocks`);
* `Algo.rawStdBlocksAt` keeps the blocks of one orbit (`Algo.blockSets_rawStdBlocksAt`), which
  is the form in which the paper states the proposition ("in each `G`-orbit");
* `Algo.blockData_rawStdBlocks` is the `Algo.BlockData` datum that the descent round of
  `Workspace/Algo/Imprimitive.lean` asks for, from Theorem 10.5.1 (e).

Only the *labels* are used, never their size: `Algo.labBlocks` compares labels for equality
and nothing else, so the axiom's silence about which labels the routine uses costs nothing.
`Algo.blocksWF_rawStdBlocks` and all the `RAM.PolyFun` statements below hold for an arbitrary
labelling.

## Non-vacuity of the hypotheses

The hypotheses `Babai.IsGiantRep ϕ` and `Babai.VeryLargeK k (maxOrbitLength G)` that every
statement below carries are satisfiable: the proof of `Babai.not_Remark_12_0_7_as_printed`
(`Workspace/TopAction/TopAction2.lean`) exhibits `Ω = Γ = [20]`, `G = S(Ω) = ⊤` and `ϕ` the
identity representation `G →* Perm (Fin 20)`, and verifies `Babai.IsGiantRep ϕ` and
`Babai.VeryLargeK 20 (Nat.card (Fin 20))`, whence
`Babai.VeryLargeK 20 (Babai.maxOrbitLength G)` by `Babai.veryLargeK_of_card`
(`Workspace/TopAction/Classes.lean`).

## Main results

* `Algo.polyFun_stdLab`, `Algo.labRel_stdLab` — the axiom, restated in the vocabulary of
  labellings;
* `Algo.blockSets_rawStdBlocks` — the computed blocks are the standard blocks;
* `Algo.blockSets_rawStdBlocksAt` — the blocks of one orbit, `Babai.standardBlocks ϕ Δ`;
* `Algo.blockData_rawStdBlocks` — the `Algo.BlockData` datum;
* `Algo.isSystemOfImprimitivity_rawStdBlocks` — Theorem 10.5.1 (e) for a transitive group;
* `Algo.polyFun_rawStdBlocks`, `Algo.polyFun_rawStdBlocksAt` — the running time.

Every statement of this file that mentions `Algo.stdLab` rests on the theorem
`Algo.proposition_10_5_4`; no axiom about running time is involved.  No `sorry`.
-/

namespace Algo

open RAM RAM.Targets MulAction
open Equiv (Perm)

/-! ## The routine of Proposition 10.5.4

The theorem asserts that a routine exists; `Classical.choose` names one. -/

/-- §10.5, **Proposition 10.5.4**: the labelling of the points by standard blocks.

This is a routine whose existence the theorem `Algo.proposition_10_5_4` asserts, named by
`Classical.choose`.  Its input is the input of Proposition 2.2.6 (`Algo.ImgsOf`): the domain
witness and the generators of `G ≤ S_n`, then the domain witness of `[k]` and the images of
those generators under `ϕ`.  Its output is a list with one label per point.

Rests on the theorem `Algo.proposition_10_5_4`. -/
noncomputable def stdLab : (List ℕ × RawGens) × (List ℕ × RawGens) → List ℕ :=
  Classical.choose proposition_10_5_4

/-- §10.5, **Proposition 10.5.4**, the running time: *"in polynomial time"*.

Rests on the theorem `Algo.proposition_10_5_4`. -/
theorem polyFun_stdLab : PolyFun stdLab :=
  (Classical.choose_spec proposition_10_5_4).1

/-- §10.5, **Proposition 10.5.4**, the specification, in the vocabulary of labellings
(`Algo.LabRel` of `Workspace/Algo/BlockSystem.lean`): two points lie in one class of
`Algo.stdLab` exactly when one lies in the standard block of the other.

Rests on the theorem `Algo.proposition_10_5_4`. -/
theorem labRel_stdLab {n k : ℕ} {dom gdom : List ℕ} {gens : List (Perm (Fin n))}
    {imgs : List (Perm (Fin k))} {ϕ : genGroup gens →* Perm (Fin k)}
    (hdom : dom.length = n) (hgdom : gdom.length = k) (hI : ImgsOf gens imgs ϕ)
    (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK k (Babai.maxOrbitLength (genGroup gens))) (u v : Fin n) :
    LabRel (stdLab ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm k))))
        (u : ℕ) (v : ℕ) ↔ v ∈ Babai.standardBlock ϕ u :=
  (Classical.choose_spec proposition_10_5_4).2 n k dom gdom gens imgs ϕ hdom hgdom hI hϕ
    hk u v

/-- The class of a point in the labelling of Proposition 10.5.4 is its standard block.

Rests on the theorem `Algo.proposition_10_5_4`. -/
theorem labSet_stdLab {n k : ℕ} {dom gdom : List ℕ} {gens : List (Perm (Fin n))}
    {imgs : List (Perm (Fin k))} {ϕ : genGroup gens →* Perm (Fin k)}
    (hdom : dom.length = n) (hgdom : gdom.length = k) (hI : ImgsOf gens imgs ϕ)
    (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK k (Babai.maxOrbitLength (genGroup gens))) (u : Fin n) :
    labSet n (stdLab ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm k)))) (u : ℕ)
      = Babai.standardBlock ϕ u := by
  ext x
  rw [mem_labSet]
  constructor
  · intro h
    exact (labRel_stdLab hdom hgdom hI hϕ hk u x).1 (LabRel.symm h)
  · intro h
    exact LabRel.symm ((labRel_stdLab hdom hgdom hI hϕ hk u x).2 h)

/-! ## The standard blocks as raw data -/

/-- §10.5, **Proposition 10.5.4**: the standard blocks of *every* `G`-orbit, as a raw block
system.  The classes of the labelling `Algo.stdLab` are read off by `Algo.labBlocks`.

Rests on the theorem `Algo.proposition_10_5_4`. -/
noncomputable def rawStdBlocks (p : (List ℕ × RawGens) × (List ℕ × RawGens)) : RawBlocks :=
  labBlocks (p.1.1, stdLab p)

/-- §10.5, **Proposition 10.5.4**, the running time.

Rests on the theorem `Algo.proposition_10_5_4`. -/
theorem polyFun_rawStdBlocks : PolyFun rawStdBlocks :=
  (((polyFun_fst.comp polyFun_fst).pair polyFun_stdLab).comp polyFun_labBlocks).of_eq
    (fun _ => rfl)

/-- The computed block system is well formed (`Algo.BlocksWF`).  This holds for an arbitrary
labelling, so it needs none of the hypotheses of Theorem 10.5.1.

Rests on the theorem `Algo.proposition_10_5_4`. -/
theorem blocksWF_rawStdBlocks {n : ℕ} {dom gdom : List ℕ} (hdom : dom.length = n)
    (gs gis : RawGens) :
    BlocksWF n (rawStdBlocks ((dom, gs), (gdom, gis))) :=
  blocksWF_labBlocks hdom _

section Spec

variable {n k : ℕ} {dom gdom : List ℕ} {gens : List (Perm (Fin n))}
  {imgs : List (Perm (Fin k))} {ϕ : genGroup gens →* Perm (Fin k)}

/-- §10.5, **Proposition 10.5.4**: the blocks the routine returns are exactly the standard
blocks (Theorem 10.5.1 (e)) of the points, one per point, with repetitions removed.

Rests on the theorem `Algo.proposition_10_5_4`. -/
theorem blockSets_rawStdBlocks (hdom : dom.length = n) (hgdom : gdom.length = k)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK k (Babai.maxOrbitLength (genGroup gens))) :
    blockSets n (rawStdBlocks ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm k))))
      = {B | ∃ x : Fin n, B = Babai.standardBlock ϕ x} := by
  ext S
  rw [show rawStdBlocks ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm k)))
      = labBlocks (dom, stdLab ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm k))))
    from rfl, mem_blockSets_labBlocks hdom]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    exact labSet_stdLab hdom hgdom hI hϕ hk ⟨u, hu⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(x : ℕ), x.isLt, (labSet_stdLab hdom hgdom hI hϕ hk x).symm⟩

/-- §10.5, **Proposition 10.5.4**, *"in each `G`-orbit"*: the blocks of the computed system
that meet an orbit `Δ` are the standard blocks of `Δ`, `Babai.standardBlocks ϕ Δ`.

Rests on the theorem `Algo.proposition_10_5_4`. -/
theorem standardBlocks_eq_sep (hdom : dom.length = n) (hgdom : gdom.length = k)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK k (Babai.maxOrbitLength (genGroup gens))) (x₀ : Fin n) :
    Babai.standardBlocks ϕ (orbit (genGroup gens) x₀)
      = {B | B ∈ blockSets n
              (rawStdBlocks ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm k)))) ∧
            (B ∩ orbit (genGroup gens) x₀).Nonempty} := by
  ext B
  rw [blockSets_rawStdBlocks hdom hgdom hI hϕ hk]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, ⟨x, Babai.mem_standardBlock_self ϕ x, hx⟩⟩
  · rintro ⟨⟨x, rfl⟩, ⟨y, hyB, hy0⟩⟩
    refine ⟨x, ?_, rfl⟩
    have h1 : orbit (genGroup gens) y = orbit (genGroup gens) x := orbit_eq_iff.2 hyB.1
    have h2 : orbit (genGroup gens) y = orbit (genGroup gens) x₀ := orbit_eq_iff.2 hy0
    exact orbit_eq_iff.1 (h1.symm.trans h2)

end Spec

/-! ## The blocks of one orbit

The paper says *"the standard blocks in each `G`-orbit"*.  A standard block lies inside one
orbit, so the blocks of the orbit of a point `i` are those whose first point lies in the orbit
of `i` — and the orbit of a point is `Algo.rawOrbit` of `Workspace/Algo/Orbits.lean`. -/

/-- §10.5, **Proposition 10.5.4**: the standard blocks in the `G`-orbit of the point `p.2`.

Rests on the theorem `Algo.proposition_10_5_4`. -/
noncomputable def rawStdBlocksAt (p : ((List ℕ × RawGens) × (List ℕ × RawGens)) × ℕ) :
    RawBlocks :=
  (rawStdBlocks p.1).filter (fun B => decide (blkPt B ∈ rawOrbit (p.1.1.2, p.2)))

theorem mem_rawStdBlocksAt {p : ((List ℕ × RawGens) × (List ℕ × RawGens)) × ℕ} {B : List ℕ} :
    B ∈ rawStdBlocksAt p ↔
      B ∈ rawStdBlocks p.1 ∧ blkPt B ∈ rawOrbit (p.1.1.2, p.2) := by
  rw [rawStdBlocksAt, List.mem_filter, decide_eq_true_iff]

/-- §10.5, **Proposition 10.5.4**, the running time of the filtered routine.

Rests on the theorem `Algo.proposition_10_5_4`. -/
theorem polyFun_rawStdBlocksAt : PolyFun rawStdBlocksAt := by
  have hq : PolyFun (fun z : (((List ℕ × RawGens) × (List ℕ × RawGens)) × ℕ) × List ℕ =>
      decide (blkPt z.2 ∈ rawOrbit (z.1.1.1.2, z.1.2))) := by
    have h1 : PolyFun (fun z : (((List ℕ × RawGens) × (List ℕ × RawGens)) × ℕ) × List ℕ =>
        blkPt z.2) := polyFun_snd.comp polyFun_blkPt
    have h2 : PolyFun (fun z : (((List ℕ × RawGens) × (List ℕ × RawGens)) × ℕ) × List ℕ =>
        rawOrbit (z.1.1.1.2, z.1.2)) :=
      ((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd).pair
        (polyFun_fst.comp polyFun_snd)).comp polyFun_rawOrbit
    exact (h1.pair h2).comp polyFun_natListMem
  exact (((polyFun_id.pair (polyFun_fst.comp polyFun_rawStdBlocks)).comp
    (PolyFun.filterParam hq)).of_eq (fun _ => rfl))

section SpecAt

variable {n k : ℕ} {dom gdom : List ℕ} {gens : List (Perm (Fin n))}
  {imgs : List (Perm (Fin k))} {ϕ : genGroup gens →* Perm (Fin k)}

/-- §10.5, **Proposition 10.5.4**, as the paper states it: the routine returns the standard
blocks of the `G`-orbit `Δ` of the point `i`, that is `Babai.standardBlocks ϕ Δ` of
Theorem 10.5.1 (e).

Rests on the theorem `Algo.proposition_10_5_4`. -/
theorem blockSets_rawStdBlocksAt (hdom : dom.length = n) (hgdom : gdom.length = k)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK k (Babai.maxOrbitLength (genGroup gens))) {i : ℕ} (hi : i < n) :
    blockSets n
        (rawStdBlocksAt (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm k))), i))
      = Babai.standardBlocks ϕ (orbit (genGroup gens) ⟨i, hi⟩) := by
  have hwf : RawGens.WF n (gens.map (encPerm n)) := wf_map_encPerm n gens
  have hbwf : BlocksWF n (rawStdBlocks ((dom, gens.map (encPerm n)),
      (gdom, imgs.map (encPerm k)))) := blocksWF_rawStdBlocks hdom _ _
  -- the filter is exactly "the block meets the orbit"
  have hfilter : ∀ B ∈ rawStdBlocks ((dom, gens.map (encPerm n)),
        (gdom, imgs.map (encPerm k))),
      (blkPt B ∈ rawOrbit (gens.map (encPerm n), i) ↔
        (winSet n B ∩ orbit (genGroup gens) ⟨i, hi⟩).Nonempty) := by
    intro B hB
    have hne : B ≠ [] := hbwf.nonempty B hB
    have hmem : blkPt B ∈ B := blkPt_mem hne
    have hlt : blkPt B < n := hbwf.lt _ (List.mem_flatten.2 ⟨B, hB, hmem⟩)
    constructor
    · intro hor
      obtain ⟨h', hor'⟩ := (mem_rawOrbit_iff hwf hi (blkPt B)).1 hor
      refine ⟨⟨blkPt B, hlt⟩, mem_winSet.2 hmem, ?_⟩
      rw [decGroup_map_encPerm] at hor'
      exact hor'
    · rintro ⟨y, hyB, hy0⟩
      -- every point of a standard block lies in the same orbit as its first point
      have hy0' : y ∈ orbit (decGroup n (gens.map (encPerm n))) ⟨i, hi⟩ := by
        rwa [decGroup_map_encPerm]
      have hpt : (⟨blkPt B, hlt⟩ : Fin n) ∈ winSet n B := mem_winSet.2 hmem
      -- the block is a standard block, so it sits inside one orbit
      obtain ⟨x, hx⟩ : ∃ x : Fin n, winSet n B = Babai.standardBlock ϕ x := by
        have : winSet n B ∈ blockSets n (rawStdBlocks ((dom, gens.map (encPerm n)),
            (gdom, imgs.map (encPerm k)))) := ⟨B, hB, rfl⟩
        rw [blockSets_rawStdBlocks hdom hgdom hI hϕ hk] at this
        exact this
      rw [hx] at hpt hyB
      have h1 : orbit (genGroup gens) y = orbit (genGroup gens) x := orbit_eq_iff.2 hyB.1
      have h2 : orbit (genGroup gens) (⟨blkPt B, hlt⟩ : Fin n) = orbit (genGroup gens) x :=
        orbit_eq_iff.2 hpt.1
      have h3 : orbit (genGroup gens) y = orbit (genGroup gens) ⟨i, hi⟩ := orbit_eq_iff.2 hy0
      refine (mem_rawOrbit_iff hwf hi (blkPt B)).2 ⟨hlt, ?_⟩
      rw [decGroup_map_encPerm]
      exact orbit_eq_iff.1 (h2.trans (h1.symm.trans h3))
  ext S
  rw [standardBlocks_eq_sep hdom hgdom hI hϕ hk ⟨i, hi⟩]
  constructor
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨hB1, hB2⟩ := mem_rawStdBlocksAt.1 hB
    exact ⟨⟨B, hB1, rfl⟩, (hfilter B hB1).1 hB2⟩
  · rintro ⟨⟨B, hB, rfl⟩, hmeet⟩
    exact ⟨B, mem_rawStdBlocksAt.2 ⟨hB, (hfilter B hB).2 hmeet⟩, rfl⟩

end SpecAt

/-! ## The block system, and the datum a descent instance carries

Theorem 10.5.1 (e) says that the standard blocks of an orbit form a system of imprimitivity
(`Babai.Proposition_10_5_4_statement`, proved as `Babai.theorem_10_5_1_e_isSystem`).  What the
descent round of `Workspace/Algo/Imprimitive.lean` needs is only that `G` permutes the computed
blocks, which is Eq. (54) in block form (`Babai.image_standardBlock`). -/

section BlockData

variable {n k : ℕ} {dom gdom : List ℕ} {gens : List (Perm (Fin n))}
  {imgs : List (Perm (Fin k))} {ϕ : genGroup gens →* Perm (Fin k)}

/-- **Theorem 10.5.1 (e)**, §10.5: `G` permutes the standard blocks, by Eq. (54) in block
form.  Transitivity of `G` is not needed: the computed system holds the standard blocks of
every orbit, and each orbit is `G`-invariant.

Rests on the theorem `Algo.proposition_10_5_4`. -/
theorem permutes_rawStdBlocks (hdom : dom.length = n) (hgdom : gdom.length = k)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK k (Babai.maxOrbitLength (genGroup gens))) :
    ∀ σ ∈ genGroup gens, ∀ B ∈ blockSets n
        (rawStdBlocks ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm k)))),
      (σ : Perm (Fin n)) '' B ∈ blockSets n
        (rawStdBlocks ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm k)))) := by
  intro σ hσ B hB
  rw [blockSets_rawStdBlocks hdom hgdom hI hϕ hk] at hB ⊢
  obtain ⟨x, rfl⟩ := hB
  refine ⟨(⟨σ, hσ⟩ : genGroup gens) • x, ?_⟩
  exact Babai.image_standardBlock ϕ hϕ hk x ⟨σ, hσ⟩

/-- **The datum a descent instance carries** (`Algo.BlockData`,
`Workspace/Algo/Blocks.lean`), for the standard blocks: the images of the generators on the
computed blocks are the images of the action `ψ : G → S(ℬ)`.  This is the analogue, for
Proposition 10.5.4, of `Algo.blockData_rawMinBlocks`.

Rests on the theorem `Algo.proposition_10_5_4`. -/
theorem blockData_rawStdBlocks (hdom : dom.length = n) (hgdom : gdom.length = k)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK k (Babai.maxOrbitLength (genGroup gens))) :
    BlockData n
      (rawStdBlocks ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm k)))) gens :=
  (blockData_of_permutes (blocksWF_rawStdBlocks hdom _ _)
    (permutes_rawStdBlocks hdom hgdom hI hϕ hk)).1

/-- **Theorem 10.5.1 (e)**, §10.5, for a transitive group: the computed blocks form a system
of imprimitivity of `G` on the whole domain.  For a transitive `G` the single orbit is
everything, so `Babai.theorem_10_5_1_e_isSystem` applies directly.

Rests on the theorem `Algo.proposition_10_5_4`. -/
theorem isSystemOfImprimitivity_rawStdBlocks (hdom : dom.length = n) (hgdom : gdom.length = k)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK k (Babai.maxOrbitLength (genGroup gens)))
    (htr : Babai.IsTransitive (genGroup gens)) :
    Babai.IsSystemOfImprimitivity (genGroup gens) Set.univ
      (blockSets n
        (rawStdBlocks ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm k))))) := by
  obtain ⟨x₀, hx₀⟩ := htr
  have hsys := Babai.theorem_10_5_1_e_isSystem ϕ hϕ hk x₀
  rw [hx₀] at hsys
  have hblocks : blockSets n
      (rawStdBlocks ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm k))))
      = Babai.standardBlocks ϕ (Set.univ : Set (Fin n)) := by
    rw [blockSets_rawStdBlocks hdom hgdom hI hϕ hk]
    ext B
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, Set.mem_univ x, hx⟩
    · rintro ⟨x, -, hx⟩
      exact ⟨x, hx⟩
  rw [hblocks]
  exact hsys

end BlockData

end Algo
