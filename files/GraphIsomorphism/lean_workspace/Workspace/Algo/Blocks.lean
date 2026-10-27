/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the action of a group on a block system, as raw data (§2.2, §11.1).
-/
import Workspace.Algo.Extend
import Workspace.Algo.Luks

/-!
# The action on the blocks, on raw data (§2.2.1, §11.1)

Theorem 11.1.9 descends to `N = ker(ψ)`, where `ψ : G → Ḡ ≤ S_m` is the action of `G` on a
`G`-invariant partition `ℬ = {B₁,…,B_m}` of the window.  `Workspace/Algo/Extend.lean` computes
generators of the kernel of *any* action given by the images of the generators
(Proposition 2.2.6 (a)); this file produces those images for the action on the blocks, from a
block system given as raw data, and ties the kernel it computes to `Babai.blockKernel`.

## The encoding

A block system is a list of blocks, each a list of points:

```
Algo.RawBlocks := List (List ℕ)
```

and `Algo.BlocksWF n bl` says what the paper's "nonempty, pairwise disjoint subsets" says of
that list: no block is empty, every point is below `n`, and the flattening has no repetition
— which is exactly "the blocks are pairwise disjoint and each is repetition-free"
(`List.nodup_flatten`).  The index of a block is its position in the list, so `ℬ` is indexed
by `Fin bl.length` and `S(ℬ)` is `Perm (Fin bl.length)`: this is the `S_m` of the paper.

The routine `Algo.rawBlockImg` sends a permutation `g` of the domain to its image on the block
indices: the `i`-th entry is the index of the block containing `g(u)`, where `u` is the first
point of the `i`-th block.  One point of a block determines the image block because `g` maps
blocks to blocks and blocks are disjoint, which is `Algo.blkIdx_eq_of_mem`.

## The homomorphism is a hypothesis about `ℬ`, not about the list

That `g ↦ g^ℬ` is a homomorphism `G → S(ℬ)` needs "`G` permutes the blocks", which is a
statement about *all* of `G` and which no routine can check on the generators alone (the lift
from the generators to `G` needs the finiteness of `ℬ`).  So it is a hypothesis here, exactly
as the invariance of a window is in `Workspace/Algo/Restrict.lean`, and
`Algo.blockData_of_permutes` is what a caller proves: it produces the `Algo.ImgsOf` datum
`Workspace/Algo/Extend.lean` asks for, together with the identification of the kernel with
`Babai.blockKernel`.

## Main definitions

* `Algo.RawBlocks`, `Algo.BlocksWF` — raw block systems;
* `Algo.blkIdx`, `Algo.rawBlockImg`, `Algo.rawBlockImgs`, `Algo.blkDom` — the routines;
* `Algo.blockSets`, `Algo.blockEquiv`, `Algo.blockPhi` — `ℬ`, its indexing by `Fin m`, and the
  action `ψ : G → S(ℬ) = S_m`;
* `Algo.BlockData` — the datum a descent instance carries;
* `Algo.blockKerGens`, `Algo.blockCosetRep`, `Algo.blockCosetIndex` — Proposition 2.2.6 (a)
  for the action on the blocks.

## Main results

* `Algo.blockData_of_permutes` — the images the routine computes are the images of the
  generators under `ψ` (Prop. 2.2.6, the datum);
* `Algo.actKer_blockPhi` — **`ker ψ` is `Babai.blockKernel`**, the `N` of Theorem 11.1.9;
* `Algo.decGroup_blockKerGens`, `Algo.cover_blockCosetRep` — Proposition 2.2.6 (a) for this
  action: generators of `N`, and the covering of `G` by the `|G : N|` left cosets;
* `Algo.polyFun_blkIdx`, `Algo.polyFun_rawBlockImgs`, `Algo.polyFun_blockKerGens`,
  `Algo.polyFun_blockCosetRep` — the running times.

No axiom, no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)
open scoped Pointwise

variable {n : ℕ}

/-! ## Raw block systems -/

/-- A **block system on raw data**: a list of blocks, each a list of points. -/
abbrev RawBlocks := List (List ℕ)

/-- **The index of the block containing a point**; `bl.length` when there is none.  The list
is scanned once and the first block containing the point wins; under `Algo.BlocksWF` there is
at most one such block (`Algo.blkIdx_eq_of_mem`). -/
def blkIdx (p : RawBlocks × ℕ) : ℕ :=
  ((p.1.zipIdx.filter (fun q => decide (p.2 ∈ q.1))).map Prod.snd).headD p.1.length

/-- The point of a block the routines read: its first one. -/
def blkPt (B : List ℕ) : ℕ := B.headD 0

/-- **The domain witness of the set of blocks**: one point per block, so that the number of
blocks never has to be a machine natural (the convention of `Workspace/Algo/Extend.lean`). -/
def blkDom (bl : RawBlocks) : List ℕ := bl.map blkPt

@[simp] theorem length_blkDom (bl : RawBlocks) : (blkDom bl).length = bl.length := by
  simp [blkDom]

/-- **The image of one permutation on the block indices**: the `i`-th entry is the index of
the block containing the image of the first point of the `i`-th block. -/
def rawBlockImg (p : RawBlocks × RawPerm) : RawPerm :=
  p.1.map (fun B => blkIdx (p.1, rawApply (p.2, blkPt B)))

@[simp] theorem length_rawBlockImg (bl : RawBlocks) (g : RawPerm) :
    (rawBlockImg (bl, g)).length = bl.length := by simp [rawBlockImg]

/-- **The images of the generators on the block indices.**  This is the `Algo.ImgsOf` datum of
Proposition 2.2.6 for the action on the blocks. -/
def rawBlockImgs (p : RawBlocks × RawGens) : RawGens :=
  p.2.map (fun g => rawBlockImg (p.1, g))

/-- **Well-formed raw block systems** (§2.2.1): the blocks are nonempty, their points lie in
the domain, and they are pairwise disjoint repetition-free lists — which is what it means for
the flattening to have no repetition. -/
structure BlocksWF (n : ℕ) (bl : RawBlocks) : Prop where
  /-- "the `Bᵢ` are nonempty" -/
  nonempty : ∀ B ∈ bl, B ≠ []
  /-- the points are points of the domain -/
  lt : ∀ u ∈ bl.flatten, u < n
  /-- "pairwise disjoint subsets", with no repetition inside a block -/
  nodup : bl.flatten.Nodup

theorem mem_flatten_getElem {bl : RawBlocks} {i : ℕ} (hi : i < bl.length) {u : ℕ}
    (hu : u ∈ bl[i]) : u ∈ bl.flatten :=
  List.mem_flatten.2 ⟨bl[i], List.getElem_mem hi, hu⟩

/-- **The blocks are pairwise disjoint**: a point lies in at most one of them. -/
theorem BlocksWF.uniq {bl : RawBlocks} (hb : BlocksWF n bl) {i j : ℕ} (hi : i < bl.length)
    (hj : j < bl.length) {u : ℕ} (hui : u ∈ bl[i]) (huj : u ∈ bl[j]) : i = j := by
  obtain ⟨-, hpw⟩ := List.nodup_flatten.1 hb.nodup
  rw [List.pairwise_iff_getElem] at hpw
  by_contra hne
  rcases Nat.lt_or_ge i j with hlt | hge
  · exact hpw i j hi hj hlt hui huj
  · have hlt' : j < i := by omega
    exact hpw j i hj hi hlt' huj hui

/-- The point a routine reads off a block is a point of that block. -/
theorem blkPt_mem {B : List ℕ} (h : B ≠ []) : blkPt B ∈ B := by
  cases B with
  | nil => exact absurd rfl h
  | cons a l => exact List.mem_cons_self ..

/-- Every entry of the filtered list is the index of a block containing the point. -/
theorem blkIdx_eq_of_mem {bl : RawBlocks} (hb : BlocksWF n bl) {i : ℕ} (hi : i < bl.length)
    {u : ℕ} (hu : u ∈ bl[i]) : blkIdx (bl, u) = i := by
  set L := (bl.zipIdx.filter (fun q => decide (u ∈ q.1))).map Prod.snd with hL
  have hall : ∀ a ∈ L, a = i := by
    intro a ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
    obtain ⟨hqmem, hqp⟩ := List.mem_filter.1 hq
    obtain ⟨k, hk, hkq⟩ := List.mem_iff_getElem.1 hqmem
    have hklen : k < bl.length := by simpa using hk
    have hqeq : q = (bl[k], k) := by
      rw [← hkq, List.getElem_zipIdx]
      simp
    have huq : u ∈ q.1 := of_decide_eq_true hqp
    rw [hqeq] at huq ⊢
    exact hb.uniq hklen hi huq hu
  have hne : L ≠ [] := by
    have hmem : (bl[i], i) ∈ bl.zipIdx.filter (fun q => decide (u ∈ q.1)) := by
      refine List.mem_filter.2 ⟨?_, by simpa using hu⟩
      have hlen : i < bl.zipIdx.length := by simpa using hi
      have : bl.zipIdx[i] = (bl[i], i) := by rw [List.getElem_zipIdx]; simp
      exact this ▸ List.getElem_mem hlen
    intro hcon
    have : i ∈ L := List.mem_map.2 ⟨(bl[i], i), hmem, rfl⟩
    rw [hcon] at this
    exact absurd this (List.not_mem_nil)
  show L.headD bl.length = i
  cases hcase : L with
  | nil => exact absurd hcase hne
  | cons a l =>
      have : a = i := hall a (by rw [hcase]; exact List.mem_cons_self ..)
      simpa using this

/-! ## The blocks as a set of sets, indexed by `Fin m` -/

/-- **The block system `ℬ`** the list describes. -/
def blockSets (n : ℕ) (bl : RawBlocks) : Set (Set (Fin n)) :=
  (fun B => winSet n B) '' {B | B ∈ bl}

theorem mem_blockSets_getElem {bl : RawBlocks} {i : ℕ} (hi : i < bl.length) :
    winSet n bl[i] ∈ blockSets n bl :=
  ⟨bl[i], List.getElem_mem hi, rfl⟩

/-- The `i`-th block of the list, as an element of `ℬ`. -/
def blockFun (n : ℕ) (bl : RawBlocks) (i : Fin bl.length) : blockSets n bl :=
  ⟨winSet n bl[i], mem_blockSets_getElem i.isLt⟩

theorem bijective_blockFun {bl : RawBlocks} (hb : BlocksWF n bl) :
    Function.Bijective (blockFun n bl) := by
  constructor
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
    have hset : winSet n bl[i] = winSet n bl[j] := congrArg Subtype.val hij
    have hu : blkPt bl[i] ∈ bl[i] := blkPt_mem (hb.nonempty _ (List.getElem_mem hi))
    have hlt : blkPt bl[i] < n := hb.lt _ (mem_flatten_getElem hi hu)
    have hmem : (⟨blkPt bl[i], hlt⟩ : Fin n) ∈ winSet n bl[i] := hu
    rw [hset] at hmem
    exact Fin.ext (hb.uniq hi hj hu hmem)
  · rintro ⟨S, B, hB, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hB
    exact ⟨⟨i, hi⟩, rfl⟩

/-- **The indexing of `ℬ` by `Fin m`**, `m` the number of blocks: this is the identification
of `S(ℬ)` with the paper's `S_m`. -/
noncomputable def blockEquiv (n : ℕ) (bl : RawBlocks) (hb : BlocksWF n bl) :
    Fin bl.length ≃ blockSets n bl :=
  Equiv.ofBijective _ (bijective_blockFun hb)

@[simp] theorem blockEquiv_apply {bl : RawBlocks} (hb : BlocksWF n bl) (i : Fin bl.length) :
    blockEquiv n bl hb i = blockFun n bl i := rfl

theorem blockEquiv_symm_apply {bl : RawBlocks} (hb : BlocksWF n bl) {i : Fin bl.length}
    {B : blockSets n bl} (h : (B : Set (Fin n)) = winSet n bl[(i : ℕ)]) :
    (blockEquiv n bl hb).symm B = i := by
  have : B = blockFun n bl i := Subtype.ext h
  rw [this, show blockFun n bl i = blockEquiv n bl hb i from rfl, Equiv.symm_apply_apply]

/-! ## The action `ψ : G → S(ℬ)` -/

variable {gens : List (Perm (Fin n))}

/-- **The action of `G` on the blocks**, `ψ : G → Ḡ ≤ S_m` of Theorem 11.1.9: the block
action `Babai.blockHom`, read through the indexing of `ℬ` by `Fin m`. -/
noncomputable def blockPhi (n : ℕ) (bl : RawBlocks) (hb : BlocksWF n bl)
    (gens : List (Perm (Fin n)))
    (hperm : ∀ σ ∈ genGroup gens, ∀ B ∈ blockSets n bl,
      (σ : Perm (Fin n)) '' B ∈ blockSets n bl) :
    genGroup gens →* Perm (Fin bl.length) :=
  (Equiv.permCongrHom (blockEquiv n bl hb).symm).toMonoidHom.comp
    (Babai.blockHom (genGroup gens) (blockSets n bl) hperm)

theorem blockPhi_apply {bl : RawBlocks} (hb : BlocksWF n bl)
    {hperm : ∀ σ ∈ genGroup gens, ∀ B ∈ blockSets n bl,
      (σ : Perm (Fin n)) '' B ∈ blockSets n bl}
    (g : genGroup gens) (i : Fin bl.length) :
    blockPhi n bl hb gens hperm g i =
      (blockEquiv n bl hb).symm
        (Babai.blockHom (genGroup gens) (blockSets n bl) hperm g (blockEquiv n bl hb i)) := by
  show (Equiv.permCongr (blockEquiv n bl hb).symm)
      (Babai.blockHom (genGroup gens) (blockSets n bl) hperm g) i = _
  rw [Equiv.permCongr_apply, Equiv.symm_symm]

/-- **`ker ψ` is the `N` of Theorem 11.1.9.** -/
theorem actKer_blockPhi {bl : RawBlocks} (hb : BlocksWF n bl)
    (hperm : ∀ σ ∈ genGroup gens, ∀ B ∈ blockSets n bl,
      (σ : Perm (Fin n)) '' B ∈ blockSets n bl) :
    actKer gens (blockPhi n bl hb gens hperm)
      = Babai.blockKernel (genGroup gens) (blockSets n bl) hperm := by
  have hker : (blockPhi n bl hb gens hperm).ker
      = (Babai.blockHom (genGroup gens) (blockSets n bl) hperm).ker := by
    ext g
    simp only [MonoidHom.mem_ker]
    constructor
    · intro h
      have h2 : (Equiv.permCongrHom (blockEquiv n bl hb).symm)
          (Babai.blockHom (genGroup gens) (blockSets n bl) hperm g) = 1 := h
      exact (MulEquiv.map_eq_one_iff
        (Equiv.permCongrHom (blockEquiv n bl hb).symm)).1 h2
    · intro h
      show (Equiv.permCongrHom (blockEquiv n bl hb).symm)
        (Babai.blockHom (genGroup gens) (blockSets n bl) hperm g) = 1
      rw [h, map_one]
  rw [actKer, hker, Babai.blockKernel]

/-! ## The images of the generators

The routine's answer is the encoding of the images of the generators under `ψ`.  The proof is
the one sentence of §2.2: a permutation of `G` maps a block to a block, so the block the image
of one point lies in is the image block, and the blocks are disjoint, so the index is
determined. -/

/-- **The images of the generators under an action**, as a list in the order of the
generators. -/
noncomputable def imgsList {m : ℕ} (gens : List (Perm (Fin n)))
    (ϕ : genGroup gens →* Perm (Fin m)) : List (Perm (Fin m)) :=
  gens.attach.map (fun g => ϕ ⟨g.1, Subgroup.subset_closure g.2⟩)

theorem imgsOf_imgsList {m : ℕ} (gens : List (Perm (Fin n)))
    (ϕ : genGroup gens →* Perm (Fin m)) : ImgsOf gens (imgsList gens ϕ) ϕ := by
  refine ⟨by simp [imgsList], ?_⟩
  intro i hi hi'
  show (gens.attach.map (fun g => ϕ ⟨g.1, Subgroup.subset_closure g.2⟩))[i] = _
  rw [List.getElem_map]
  congr 1
  exact Subtype.ext (by simp)

/-- **The routine computes the image of one generator on the blocks.** -/
theorem rawBlockImg_eq {bl : RawBlocks} (hb : BlocksWF n bl)
    {hperm : ∀ σ ∈ genGroup gens, ∀ B ∈ blockSets n bl,
      (σ : Perm (Fin n)) '' B ∈ blockSets n bl}
    {g : Perm (Fin n)} (hg : g ∈ genGroup gens) :
    rawBlockImg (bl, encPerm n g)
      = encPerm bl.length (blockPhi n bl hb gens hperm ⟨g, hg⟩) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    have hilt : i < bl.length := by simpa using hi
    -- the image block
    have hBmem : winSet n bl[i] ∈ blockSets n bl := mem_blockSets_getElem hilt
    have himg : g '' winSet n bl[i] ∈ blockSets n bl := hperm g hg _ hBmem
    obtain ⟨B, hB, hBeq⟩ := himg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hB
    -- the point read off the block
    have hu : blkPt bl[i] ∈ bl[i] := blkPt_mem (hb.nonempty _ (List.getElem_mem hilt))
    have hult : blkPt bl[i] < n := hb.lt _ (mem_flatten_getElem hilt hu)
    have hgu : (g ⟨blkPt bl[i], hult⟩ : Fin n) ∈ g '' winSet n bl[i] :=
      ⟨⟨blkPt bl[i], hult⟩, hu, rfl⟩
    rw [← hBeq] at hgu
    have hgumem : ((g ⟨blkPt bl[i], hult⟩ : Fin n) : ℕ) ∈ bl[j] := hgu
    -- the left-hand side
    have hlhs : (rawBlockImg (bl, encPerm n g))[i]'hi = j := by
      show (bl.map (fun B => blkIdx (bl, rawApply (encPerm n g, blkPt B))))[i]'hi = j
      rw [List.getElem_map, rawApply_encPerm n g hult]
      exact blkIdx_eq_of_mem hb hj hgumem
    -- the right-hand side
    have hrhs : (encPerm bl.length (blockPhi n bl hb gens hperm ⟨g, hg⟩))[i]'hi' = j := by
      rw [getElem_encPerm _ _ i hilt, blockPhi_apply]
      have hval : ((Babai.blockHom (genGroup gens) (blockSets n bl) hperm ⟨g, hg⟩
          (blockEquiv n bl hb ⟨i, hilt⟩) : blockSets n bl) : Set (Fin n))
          = winSet n bl[j] := by
        rw [Babai.blockHom_apply_coe]
        show g '' (blockFun n bl ⟨i, hilt⟩ : Set (Fin n)) = winSet n bl[j]
        exact hBeq.symm
      have := blockEquiv_symm_apply (i := (⟨j, hj⟩ : Fin bl.length)) hb hval
      rw [this]
    rw [hlhs, hrhs]

/-- **The images of the generators the routine computes**, decoded. -/
noncomputable def blockImgsOf (n : ℕ) (bl : RawBlocks) (gens : List (Perm (Fin n))) :
    List (Perm (Fin bl.length)) :=
  (rawBlockImgs (bl, gens.map (encPerm n))).map (decPerm bl.length)

/-- **The datum a descent instance carries**: the images of the generators on the block
indices are the images of a homomorphism `G → S(ℬ)`, and they are well-formed raw
permutations.  Neither clause can be checked by the round on its own; both come from
`Algo.blockData_of_permutes`. -/
def BlockData (n : ℕ) (bl : RawBlocks) (gens : List (Perm (Fin n))) : Prop :=
  RawGens.WF bl.length (rawBlockImgs (bl, gens.map (encPerm n))) ∧
    ∃ ϕ : genGroup gens →* Perm (Fin bl.length), ImgsOf gens (blockImgsOf n bl gens) ϕ

/-- The raw images are the encodings of the decoded ones, which is what
`Workspace/Algo/Extend.lean` asks of an `Algo.ImgsOf` datum. -/
theorem rawBlockImgs_eq_map_encPerm {bl : RawBlocks} {gens : List (Perm (Fin n))}
    (h : RawGens.WF bl.length (rawBlockImgs (bl, gens.map (encPerm n)))) :
    rawBlockImgs (bl, gens.map (encPerm n))
      = (blockImgsOf n bl gens).map (encPerm bl.length) :=
  (map_encPerm_decPerm h).symm

/-- **The block action is an `Algo.ImgsOf` datum** (Prop. 2.2.6): from "`G` permutes the
blocks" the routine's answer is the list of images of the generators under `ψ`, and the
kernel of `ψ` is the `N` of Theorem 11.1.9. -/
theorem blockData_of_permutes {bl : RawBlocks} (hb : BlocksWF n bl)
    (hperm : ∀ σ ∈ genGroup gens, ∀ B ∈ blockSets n bl,
      (σ : Perm (Fin n)) '' B ∈ blockSets n bl) :
    BlockData n bl gens ∧
      blockImgsOf n bl gens = imgsList gens (blockPhi n bl hb gens hperm) := by
  have hraw : rawBlockImgs (bl, gens.map (encPerm n))
      = (imgsList gens (blockPhi n bl hb gens hperm)).map (encPerm bl.length) := by
    show (gens.map (encPerm n)).map (fun r => rawBlockImg (bl, r)) = _
    rw [List.map_map, imgsList, List.map_map]
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      have hilt : i < gens.length := by simpa using hi
      rw [List.getElem_map, List.getElem_map]
      show rawBlockImg (bl, encPerm n gens[i]) = _
      rw [rawBlockImg_eq (hperm := hperm) hb (Subgroup.subset_closure (List.getElem_mem hilt))]
      congr 2
      exact Subtype.ext (by simp)
  have hwf : RawGens.WF bl.length (rawBlockImgs (bl, gens.map (encPerm n))) := by
    rw [hraw]
    intro r hr
    obtain ⟨σ, -, rfl⟩ := List.mem_map.1 hr
    exact wf_encPerm _ _
  have hdec : blockImgsOf n bl gens = imgsList gens (blockPhi n bl hb gens hperm) := by
    rw [blockImgsOf, hraw, List.map_map]
    exact List.map_congr_left (fun σ _ => by simp) |>.trans (List.map_id _)
  exact ⟨⟨hwf, ⟨blockPhi n bl hb gens hperm, hdec ▸ imgsOf_imgsList _ _⟩⟩, hdec⟩

/-! ## Proposition 2.2.6 (a) for the action on the blocks

The three routines of `Workspace/Algo/Extend.lean`, with the second domain read off the block
list. -/

/-- **Generators of `N = ker ψ`** (Prop. 2.2.6 (a)). -/
def blockKerGens (p : (List ℕ × RawGens) × RawBlocks) : RawGens :=
  actKerGens ((p.1.1, p.1.2), (blkDom p.2, rawBlockImgs (p.2, p.1.2)))

/-- **The `j`-th left coset representative of `N` in `G`**, the index in binary. -/
def blockCosetRep (p : ((List ℕ × RawGens) × RawBlocks) × ℕ) : RawPerm :=
  actCosetRep (((p.1.1.1, p.1.1.2), (blkDom p.1.2, rawBlockImgs (p.1.2, p.1.1.2))), p.2)

/-- **The number of cosets**, `|G : N| = |Ḡ|` of Theorem 11.1.9. -/
noncomputable def blockCosetIndex (n : ℕ) (dom : List ℕ) (bl : RawBlocks)
    (gens : List (Perm (Fin n))) : ℕ :=
  actCosetIndex n bl.length dom (blkDom bl) gens (blockImgsOf n bl gens)

section Routines

variable {dom : List ℕ} {bl : RawBlocks}

/-- **Proposition 2.2.6 (a)**: the routine returns a generating list of `ker ψ`. -/
theorem decGroup_blockKerGens (hd : dom.length = n)
    {ϕ : genGroup gens →* Perm (Fin bl.length)}
    (hwf : RawGens.WF bl.length (rawBlockImgs (bl, gens.map (encPerm n))))
    (hI : ImgsOf gens (blockImgsOf n bl gens) ϕ) :
    decGroup n (blockKerGens ((dom, gens.map (encPerm n)), bl)) = actKer gens ϕ := by
  show decGroup n (actKerGens ((dom, gens.map (encPerm n)),
    (blkDom bl, rawBlockImgs (bl, gens.map (encPerm n))))) = _
  rw [rawBlockImgs_eq_map_encPerm hwf]
  exact decGroup_actKerGens hd (length_blkDom bl) hI

/-- **Proposition 2.2.6 (a), the covering half**: `G` is the union of the `|G : N|` left
cosets of `N` with the computed representatives. -/
theorem cover_blockCosetRep (hd : dom.length = n)
    {ϕ : genGroup gens →* Perm (Fin bl.length)}
    (hwf : RawGens.WF bl.length (rawBlockImgs (bl, gens.map (encPerm n))))
    (hI : ImgsOf gens (blockImgsOf n bl gens) ϕ) :
    (genGroup gens : Set (Perm (Fin n)))
      = ⋃ j ∈ List.range (blockCosetIndex n dom bl gens),
          decPerm n (blockCosetRep (((dom, gens.map (encPerm n)), bl), j))
            • (actKer gens ϕ : Set (Perm (Fin n))) := by
    have hcov := cover_actCosetRep (dom := dom) (gdom := blkDom bl)
      (imgs := blockImgsOf n bl gens) hd (length_blkDom bl) hI
    rw [hcov]
    refine Set.iUnion_congr (fun j => ?_)
    refine Set.iUnion_congr_Prop (by rw [blockCosetIndex]) (fun _ => ?_)
    congr 2
    show _ = actCosetRep (((dom, gens.map (encPerm n)),
      (blkDom bl, rawBlockImgs (bl, gens.map (encPerm n)))), j)
    rw [rawBlockImgs_eq_map_encPerm hwf]

end Routines

/-! ## The size of a block system

A block system of a domain of `n` points is a list of at most `n` lists of at most `n` points
below `n`: the blocks are nonempty and disjoint, so there are at most `n` of them. -/

theorem length_le_length_flatten_of_ne_nil :
    ∀ {L : List (List ℕ)}, (∀ B ∈ L, B ≠ []) → L.length ≤ L.flatten.length := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons B l ih =>
      intro h
      have hB : B ≠ [] := h B (List.mem_cons_self ..)
      have hBlen : 1 ≤ B.length := by
        cases B with
        | nil => exact absurd rfl hB
        | cons _ _ => simp
      have := ih (fun C hC => h C (List.mem_cons_of_mem _ hC))
      simp only [List.flatten_cons, List.length_append, List.length_cons]
      omega

/-- The number of blocks is at most the number of points. -/
theorem BlocksWF.length_le {bl : RawBlocks} (hb : BlocksWF n bl) : bl.length ≤ n := by
  have h1 : bl.length ≤ bl.flatten.length := length_le_length_flatten_of_ne_nil hb.nonempty
  have h2 : bl.flatten.length ≤ n := length_le_of_nodup_lt hb.nodup hb.lt
  omega

/-- Each block is a list of at most `n` points below `n`. -/
theorem BlocksWF.block_length_le {bl : RawBlocks} (hb : BlocksWF n bl) {B : List ℕ}
    (hB : B ∈ bl) : B.length ≤ n := by
  have h1 : B.length ≤ bl.flatten.length :=
    length_le_length_flatten hB
  have h2 : bl.flatten.length ≤ n := length_le_of_nodup_lt hb.nodup hb.lt
  omega

/-- **The size of a block system.** -/
def blocksBound (m : ℕ) : ℕ := 1 + m * (2 * strBound m + 1)

theorem size_blocks_le {bl : RawBlocks} (hb : BlocksWF n bl) {m : ℕ} (hnm : n ≤ m) :
    Enc.size bl ≤ blocksBound m := by
  have hentry : ∀ B ∈ bl, Enc.size B ≤ strBound m := by
    intro B hB
    refine size_natList_le (le_trans (hb.block_length_le hB) hnm) (fun a ha => ?_)
    exact lt_of_lt_of_le (hb.lt a (List.mem_flatten.2 ⟨B, hB, ha⟩)) hnm
  have h1 := size_list_le_of_entries bl (strBound m) hentry
  have h2 : bl.length * (2 * strBound m + 1) ≤ m * (2 * strBound m + 1) :=
    Nat.mul_le_mul_right _ (le_trans hb.length_le hnm)
  have h3 : blocksBound m = 1 + m * (2 * strBound m + 1) := rfl
  omega

theorem polyBound_blocksBound : PolyBound blocksBound := by
  have hS : PolyBound strBound :=
    (polyBound_const 1).add (polyBound_id.mul
      (((polyBound_const 2).mul (polyBound_id.add (polyBound_const 2))).add
        (polyBound_const 1)))
  exact (polyBound_const 1).add (polyBound_id.mul
    (((polyBound_const 2).mul hS).add (polyBound_const 1)))

theorem mono_blocksBound : Monotone blocksBound := by
  intro a b hab
  have h1 : strBound a ≤ strBound b :=
    Nat.add_le_add_left (Nat.mul_le_mul hab (by omega)) 1
  have h2 : blocksBound a = 1 + a * (2 * strBound a + 1) := rfl
  have h3 : blocksBound b = 1 + b * (2 * strBound b + 1) := rfl
  have h4 : a * (2 * strBound a + 1) ≤ b * (2 * strBound b + 1) :=
    Nat.mul_le_mul hab (by omega)
  omega

/-! ## The running times -/

theorem polyFun_blkIdx : PolyFun blkIdx := by
  have hq : PolyFun (fun z : (RawBlocks × ℕ) × (List ℕ × ℕ) => decide (z.1.2 ∈ z.2.1)) :=
    ((polyFun_fst.comp polyFun_snd).pair (polyFun_snd.comp polyFun_fst)).comp
      polyFun_natListMem
  have hfil : PolyFun (fun p : RawBlocks × ℕ =>
      p.1.zipIdx.filter (fun q => decide (p.2 ∈ q.1))) := by
    have hin : PolyFun (fun p : RawBlocks × ℕ =>
        ((p, p.1.zipIdx) : (RawBlocks × ℕ) × List (List ℕ × ℕ))) :=
      polyFun_id.pair (polyFun_fst.comp polyFun_zipIdx)
    exact (hin.comp (PolyFun.filterParam hq)).of_eq (fun _ => rfl)
  have hmap : PolyFun (fun p : RawBlocks × ℕ =>
      (p.1.zipIdx.filter (fun q => decide (p.2 ∈ q.1))).map Prod.snd) := by
    have hsnd : PolyFun (fun z : (RawBlocks × ℕ) × (List ℕ × ℕ) => z.2.2) :=
      polyFun_snd.comp polyFun_snd
    exact ((polyFun_id.pair hfil).comp (PolyFun.mapParam hsnd)).of_eq (fun _ => rfl)
  have hhead : PolyFun (fun p : RawBlocks × ℕ =>
      ((p.1.zipIdx.filter (fun q => decide (p.2 ∈ q.1))).map Prod.snd).head?) :=
    hmap.comp polyFun_headOption
  exact ((hhead.pair (polyFun_fst.comp polyFun_length)).comp polyFun_optionGetD).of_eq
    (fun p => by rw [blkIdx, List.headD_eq_head?_getD])

theorem polyFun_blkPt : PolyFun blkPt := by
  refine (((polyFun_headOption (α := ℕ)).pair (polyFun_const (0 : ℕ))).comp
    polyFun_optionGetD).of_eq (fun B => ?_)
  show B.head?.getD 0 = blkPt B
  rw [blkPt, List.headD_eq_head?_getD]

theorem polyFun_blkDom : PolyFun blkDom := by
  have h : PolyFun (fun z : RawBlocks × List ℕ => blkPt z.2) := polyFun_snd.comp polyFun_blkPt
  exact ((polyFun_id.pair polyFun_id).comp (PolyFun.mapParam h)).of_eq (fun _ => rfl)

theorem polyFun_rawBlockImg : PolyFun rawBlockImg := by
  have hinner : PolyFun (fun z : (RawBlocks × RawPerm) × List ℕ =>
      blkIdx (z.1.1, rawApply (z.1.2, blkPt z.2))) :=
    ((polyFun_fst.comp polyFun_fst).pair
      (((polyFun_fst.comp polyFun_snd).pair (polyFun_snd.comp polyFun_blkPt)).comp
        polyFun_rawApply)).comp polyFun_blkIdx
  have hin : PolyFun (fun p : RawBlocks × RawPerm =>
      ((p, p.1) : (RawBlocks × RawPerm) × RawBlocks)) := polyFun_id.pair polyFun_fst
  exact (hin.comp (PolyFun.mapParam hinner)).of_eq (fun _ => rfl)

theorem polyFun_rawBlockImgs : PolyFun rawBlockImgs := by
  have hinner : PolyFun (fun z : (RawBlocks × RawGens) × RawPerm =>
      rawBlockImg (z.1.1, z.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_rawBlockImg
  have hin : PolyFun (fun p : RawBlocks × RawGens =>
      ((p, p.2) : (RawBlocks × RawGens) × RawGens)) := polyFun_id.pair polyFun_snd
  exact (hin.comp (PolyFun.mapParam hinner)).of_eq (fun _ => rfl)

theorem polyFun_blockKerGens : PolyFun blockKerGens := by
  have hbl : PolyFun (fun p : (List ℕ × RawGens) × RawBlocks => p.2) := polyFun_snd
  have hgens : PolyFun (fun p : (List ℕ × RawGens) × RawBlocks => p.1.2) :=
    polyFun_fst.comp polyFun_snd
  exact ((((polyFun_fst.comp polyFun_fst).pair hgens).pair
    ((hbl.comp polyFun_blkDom).pair ((hbl.pair hgens).comp polyFun_rawBlockImgs))).comp
      polyFun_actKerGens).of_eq (fun _ => rfl)

theorem polyFun_blockCosetRep : PolyFun blockCosetRep := by
  have hbl : PolyFun (fun p : ((List ℕ × RawGens) × RawBlocks) × ℕ => p.1.2) :=
    polyFun_fst.comp polyFun_snd
  have hgens : PolyFun (fun p : ((List ℕ × RawGens) × RawBlocks) × ℕ => p.1.1.2) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_snd
  have hdom : PolyFun (fun p : ((List ℕ × RawGens) × RawBlocks) × ℕ => p.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  exact (((((hdom.pair hgens).pair
    ((hbl.comp polyFun_blkDom).pair ((hbl.pair hgens).comp polyFun_rawBlockImgs))).pair
      polyFun_snd)).comp polyFun_actCosetRep).of_eq (fun _ => rfl)

/-! ## The number of cosets of `N` is `|Ḡ|` (risk R-A7-3)

`Algo.cover_blockCosetRep` shows only that the computed representatives cover `G`.  With
`Algo.actCosetIndex_eq_card_range` the computed number is exactly `|G : N|`, and
`Babai.Theorem_11_1_9_card` identifies that with `|Ḡ| = |G^ℬ|`: the width of the descend
phase of Theorem 11.1.9 really is the paper's `|Ḡ|`. -/

section IndexBlocks

variable {dom : List ℕ} {bl : RawBlocks} {gens : List (Perm (Fin n))}

/-- **R-A7-3 for the block action**: the number of coset representatives the routine produces
is the order of the image of the action on the blocks. -/
theorem blockCosetIndex_eq_card_range (hd : dom.length = n)
    {ϕ : genGroup gens →* Perm (Fin bl.length)}
    (hI : ImgsOf gens (blockImgsOf n bl gens) ϕ) :
    blockCosetIndex n dom bl gens = Nat.card ϕ.range :=
  actCosetIndex_eq_card_range hd (length_blkDom bl) hI

/-- The computed images of the generators on the blocks are the images under `ψ`
(`Algo.blockPhi`). -/
theorem imgsOf_blockPhi (hb : BlocksWF n bl)
    (hperm : ∀ σ ∈ genGroup gens, ∀ B ∈ blockSets n bl,
      (σ : Perm (Fin n)) '' B ∈ blockSets n bl) :
    ImgsOf gens (blockImgsOf n bl gens) (blockPhi n bl hb gens hperm) := by
  rw [(blockData_of_permutes hb hperm).2]
  exact imgsOf_imgsList _ _

/-- §11.1, **Theorem 11.1.9**, the count `|G : N| = |Ḡ|`, as the routine computes it: the
number of children of the descend phase is `|G^ℬ|`, the order of the group `Ḡ` induced on the
blocks. -/
theorem blockCosetIndex_eq_card_onBlocks (hd : dom.length = n) (hb : BlocksWF n bl)
    (hperm : ∀ σ ∈ genGroup gens, ∀ B ∈ blockSets n bl,
      (σ : Perm (Fin n)) '' B ∈ blockSets n bl) :
    blockCosetIndex n dom bl gens
      = Nat.card (Babai.onBlocks (genGroup gens) (blockSets n bl) hperm) := by
  rw [blockCosetIndex_eq_card_range hd (imgsOf_blockPhi hb hperm)]
  have hrange : (blockPhi n bl hb gens hperm).range
      = (Babai.onBlocks (genGroup gens) (blockSets n bl) hperm).map
          (Equiv.permCongrHom (blockEquiv n bl hb).symm).toMonoidHom := by
    ext p
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨_, ⟨g, rfl⟩, rfl⟩
    · rintro ⟨q, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, rfl⟩
  rw [hrange]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _
    (Equiv.permCongrHom (blockEquiv n bl hb).symm).injective).toEquiv).symm

/-- §11.1, **Theorem 11.1.9**: the number of children of the descend phase is the index
`|G : N|`, through `Babai.Theorem_11_1_9_card`. -/
theorem blockCosetIndex_eq_card_quotient (hd : dom.length = n) (hb : BlocksWF n bl)
    (hperm : ∀ σ ∈ genGroup gens, ∀ B ∈ blockSets n bl,
      (σ : Perm (Fin n)) '' B ∈ blockSets n bl) :
    blockCosetIndex n dom bl gens
      = Nat.card (genGroup gens ⧸
          (Babai.blockKernel (genGroup gens) (blockSets n bl) hperm).subgroupOf
            (genGroup gens)) := by
  rw [blockCosetIndex_eq_card_onBlocks hd hb hperm, Babai.Theorem_11_1_9_card]

end IndexBlocks

end Algo
