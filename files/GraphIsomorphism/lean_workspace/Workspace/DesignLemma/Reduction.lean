/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 8.1: Theorem 8.1.2 as a reduction at a multiplicative cost (§6).
-/
import Workspace.DesignLemma.Functor
import Workspace.SplitOrJohnson.ExtendedDesign

/-!
# §8.1 The Design Lemma as a reduction at a multiplicative cost

Theorem 8.1.2 says that *"we can find a value `ℓ ≤ k − 1` and a string `x⃗ ∈ Ω^⟨ℓ⟩` of `ℓ`
distinct vertices such that by individualizing each `x_j` we obtain (a), (b) or (c)"*.  In
the language of §6 this is a reduction at a multiplicative cost: the family of "versions"
of the input is the family of admissible strings, and the outcome attached to a string is
the one the procedure of §8.2 returns there.

This file builds that reduction, `Babai.designLemma_finds`.

## The three pieces

1. *Naming the colors by natural numbers.*  The categories `Babai.ColoredPartitions` and
   `Babai.UPCCs` take `ℕ`-colorings and their morphisms preserve the color **labels**,
   while `k`-WL colors live in an abstract type.  `Babai.natRank`
   (`Workspace/DesignLemma/NatRank.lean`) is the naming.  This file adds what makes it
   usable: that it takes exactly the values `0, …, r − 1` (`Babai.natRank_surjOn`), so
   that it is the coloring of a partition structure in the sense of Def. 3.1.1
   (`Babai.PartitionStructure.ofNatColoring`), and that it commutes with the transport of
   the color type that the `k`-WL round count forces (`Babai.natRank_cast`).

2. *Transporting a partition structure along a bijection of vertex sets.*  The UPCC of
   outcome (c) lives on the dominant class `C ⊆ ↥(□X)`, while `Babai.Cat.sub` wants an
   object on a subset of `Ω`; the two are related by `Subtype.val`, so Def. 3.1.11 and
   Def. 3.2.1 have to be carried along a bijection
   (`Babai.PartitionStructure.congrEquiv`).

3. *The outcome attached to a string.*  `Babai.designOutcome` is a function of the input
   and the string, with no choice: outcomes (a) and (b) give the colored partition of `Ω`
   whose colors are the vertex colors of `X_x⃗` and whose blocks are the color classes,
   except inside the dominant class, where they are the blocks of
   `Babai.KAryPartStruct.designPartition`; outcome (c) gives the subconfiguration of
   `(X_x⃗)^{(2)}` induced on the dominant class.

## Numbering map

| Paper | Lean |
|---|---|
| Theorem 8.1.2 as a reduction in the sense of §6 | `Babai.designLemma_finds` |
| the outcome of Theorem 8.1.2 at the string `x⃗` | `Babai.designOutcome` |
| the strings at which Procedure "Design Lemma" returns | `Babai.DesignOut` |
-/

open scoped Classical

universe u v

namespace Babai

/-! ### 1. `natRank` takes exactly the values `0, …, r − 1` -/

variable {K : Type*}

/-- The name of a color is below the number of colors that occur. -/
theorem natRank_lt_ncard {R : Set K} (hR : R.Finite) {c : K} (hc : c ∈ R) :
    natRank R c < R.ncard := by
  have hsub : {d ∈ R | WellOrderingRel d c} ⊆ R := fun _ hd => hd.1
  have hssub : {d ∈ R | WellOrderingRel d c} ⊂ R := by
    refine ⟨hsub, fun h => ?_⟩
    exact irrefl_of (WellOrderingRel : K → K → Prop) c (h hc).2
  exact Set.ncard_lt_ncard hssub hR

/-- The naming `Babai.natRank` hits every value below the number of colors that occur: it
is a bijection from the occurring colors onto `{0, …, r − 1}`.  This is what makes it the
coloring of a partition structure of rank `r` in the sense of Def. 3.1.1. -/
theorem natRank_surjOn {R : Set K} (hR : R.Finite) {i : ℕ} (hi : i < R.ncard) :
    ∃ c ∈ R, natRank R c = i := by
  have hsub : natRank R '' R ⊆ Set.Iio R.ncard := by
    rintro _ ⟨c, hc, rfl⟩
    exact natRank_lt_ncard hR hc
  have himg : (natRank R '' R).ncard = R.ncard :=
    (natRank_injOn hR).ncard_image
  have hIio : (Set.Iio R.ncard).ncard = R.ncard := by
    classical
    have : (Set.Iio R.ncard) = ↑(Finset.range R.ncard) := by ext j; simp
    rw [this, Set.ncard_coe_finset, Finset.card_range]
  have heq : natRank R '' R = Set.Iio R.ncard :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [himg, hIio]) (Set.finite_Iio _)
  have : i ∈ natRank R '' R := by rw [heq]; exact hi
  obtain ⟨c, hc, hci⟩ := this
  exact ⟨c, hc, hci⟩

/-- The naming commutes with a transport of the color type: it depends only on the color
and the set of occurring colors, and `cast` carries the canonical well-ordering of one
type to that of the other. -/
theorem natRank_cast {K L : Type u} (h : K = L) (R : Set K) (c : K) :
    natRank (cast h '' R) (cast h c) = natRank R c := by
  subst h
  simp

/-! ### 2. Partition structures from a `ℕ`-naming, and transport along a bijection -/

namespace PartitionStructure

variable {V W : Type*} {K : Type*}

/-- The colors that actually occur in an edge-coloring. -/
def natCodes (d : V → V → K) : Set K := Set.range fun p : V × V => d p.1 p.2

theorem mem_natCodes (d : V → V → K) (x y : V) : d x y ∈ natCodes d := ⟨(x, y), rfl⟩

theorem finite_natCodes [Finite V] (d : V → V → K) : (natCodes d).Finite :=
  Set.finite_range _

/-- Definition 3.1.1 for a coloring by an arbitrary label set, with the colors named by
`Babai.natRank`: the rank is the number of colors that occur, and the color of `(x,y)` is
the name of `d x y`.  Unlike `Babai.PartitionStructure.ofColoring`, the numbering is a
function of the coloring alone (no `Fintype` numbering of a `Finset` is used), which is
what makes the resulting `ℕ`-coloring canonical. -/
noncomputable def ofNatColoring [Finite V] (d : V → V → K) : PartitionStructure V where
  rank := (natCodes d).ncard
  color x y :=
    ⟨natRank (natCodes d) (d x y),
      natRank_lt_ncard (finite_natCodes d) (mem_natCodes d x y)⟩
  color_surjective i := by
    obtain ⟨c, hc, hci⟩ := natRank_surjOn (finite_natCodes d) i.isLt
    obtain ⟨⟨x, y⟩, rfl⟩ := hc
    exact ⟨x, y, Fin.ext hci⟩

/-- `ofNatColoring d` has exactly the color classes of `d`. -/
theorem ofNatColoring_color_eq_iff [Finite V] (d : V → V → K) (x y u v : V) :
    (ofNatColoring d).color x y = (ofNatColoring d).color u v ↔ d x y = d u v := by
  constructor
  · intro h
    exact natRank_injOn (finite_natCodes d) (mem_natCodes d x y) (mem_natCodes d u v)
      (congrArg Fin.val h)
  · intro h
    exact Fin.ext (show natRank (natCodes d) (d x y) = natRank (natCodes d) (d u v) by
      rw [h])

/-- The `ℕ`-coloring of `ofNatColoring d` is the naming of `d` by `Babai.natRank`. -/
theorem natColor_ofNatColoring [Finite V] (d : V → V → K) (x y : V) :
    (ofNatColoring d).natColor x y = natRank (natCodes d) (d x y) := rfl

/-! #### Transport along a bijection of vertex sets -/

/-- A partition structure carried along a bijection `e : V ≃ W` of vertex sets. -/
def congrEquiv (S : PartitionStructure V) (e : V ≃ W) : PartitionStructure W where
  rank := S.rank
  color x y := S.color (e.symm x) (e.symm y)
  color_surjective i := by
    obtain ⟨x, y, h⟩ := S.color_surjective i
    exact ⟨e x, e y, by simpa using h⟩

@[simp] theorem congrEquiv_color (S : PartitionStructure V) (e : V ≃ W) (x y : W) :
    (S.congrEquiv e).color x y = S.color (e.symm x) (e.symm y) := rfl

theorem congrEquiv_color_apply (S : PartitionStructure V) (e : V ≃ W) (x y : V) :
    (S.congrEquiv e).color (e x) (e y) = S.color x y := by simp

@[simp] theorem congrEquiv_rank (S : PartitionStructure V) (e : V ≃ W) :
    (S.congrEquiv e).rank = S.rank := rfl

theorem congrEquiv_isConfiguration {S : PartitionStructure V} (e : V ≃ W)
    (h : S.IsConfiguration) : (S.congrEquiv e).IsConfiguration where
  diag x y z hxyz := e.symm.injective (h.diag _ _ _ hxyz)
  converse u v x y huv := h.converse _ _ _ _ huv

theorem congrEquiv_isCoherent {S : PartitionStructure V} (e : V ≃ W)
    (h : S.IsCoherent) : (S.congrEquiv e).IsCoherent := by
  classical
  refine ⟨congrEquiv_isConfiguration e h.toIsConfiguration, ?_⟩
  obtain ⟨p, hp⟩ := h.intersection
  refine ⟨p, fun i j k x y hxy => ?_⟩
  have hset : {z : W | (S.congrEquiv e).color x z = i ∧ (S.congrEquiv e).color z y = j}
      = e '' {z : V | S.color (e.symm x) z = i ∧ S.color z (e.symm y) = j} := by
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨e.symm z, ⟨h1, h2⟩, by simp⟩
    · rintro ⟨w, ⟨h1, h2⟩, rfl⟩
      exact ⟨by simpa using h1, by simpa using h2⟩
  rw [hset, Set.ncard_image_of_injective _ e.injective]
  exact hp i j k _ _ hxy

theorem congrEquiv_isHomogeneous {S : PartitionStructure V} (e : V ≃ W)
    (h : S.IsHomogeneous) : (S.congrEquiv e).IsHomogeneous := fun x y => h _ _

theorem congrEquiv_isOffDiagonalColor {S : PartitionStructure V} (e : V ≃ W)
    {i : Fin S.rank} (h : S.IsOffDiagonalColor i) :
    (S.congrEquiv e).IsOffDiagonalColor i := by
  rw [IsOffDiagonalColor, Set.eq_empty_iff_forall_notMem]
  rintro q ⟨hq1, hq2⟩
  have hq2' : q.1 = q.2 := hq2
  have : (e.symm q.1, e.symm q.2) ∈ S.rel i := hq1
  refine Set.eq_empty_iff_forall_notMem.1 h (e.symm q.1, e.symm q.2) ⟨this, ?_⟩
  show e.symm q.1 = e.symm q.2
  rw [hq2']

theorem congrEquiv_isPrimitive {S : PartitionStructure V} (e : V ≃ W)
    (h : S.IsPrimitive) : (S.congrEquiv e).IsPrimitive := by
  refine ⟨congrEquiv_isHomogeneous e h.1, fun i hoff => ?_⟩
  have hoff' : S.IsOffDiagonalColor i := by
    rw [IsOffDiagonalColor, Set.eq_empty_iff_forall_notMem]
    rintro q ⟨hq1, hq2⟩
    have hq2' : q.1 = q.2 := hq2
    have hmem : (e q.1, e q.2) ∈ (S.congrEquiv e).rel i := by
      show (S.congrEquiv e).color (e q.1) (e q.2) = i
      rw [congrEquiv_color_apply]; exact hq1
    exact Set.eq_empty_iff_forall_notMem.1 hoff (e q.1, e q.2)
      ⟨hmem, show e q.1 = e q.2 by rw [hq2']⟩
  have hadj : ∀ u v : V,
      ((S.congrEquiv e).extConstituent i).Adj (e u) (e v)
        ↔ (S.extConstituent i).Adj u v := by
    intro u v
    show (S.congrEquiv e).color (e u) (e v) = i ↔ S.color u v = i
    rw [congrEquiv_color_apply]
    exact Iff.rfl
  exact (Digraph.isWeaklyConnected_congr e hadj).2 (h.2 i hoff')

theorem congrEquiv_isUniprimitive {S : PartitionStructure V} (e : V ≃ W)
    (h : S.IsUniprimitive) : (S.congrEquiv e).IsUniprimitive :=
  ⟨congrEquiv_isPrimitive e h.1, h.2⟩

end PartitionStructure

/-! ### 3. The colored partition of outcomes (a) and (b)

Outcomes (a) and (b) of Theorem 8.1.2 return *"a canonical coloring of `Ω`"*, in case (b)
*"and a nontrivial canonical equipartition of the dominant color class"*.  Read as an
object of `Babai.ColoredPartitions` (Def. 7.1.1) this is: the coloring is the vertex
coloring of `X_x⃗`, named by `Babai.natRank`, and the partition of each color class is the
partition into one block, except on the dominant class, where it is the equipartition
`Babai.KAryPartStruct.designPartition`.  In case (a) the family of blocks handed in is
empty and every color class is one block. -/

namespace KAryPartStruct

variable {V : Type} [Fintype V] [DecidableEq V] {C : Type*} {m : ℕ}

/-- The `ℕ`-name of the vertex color of `v`: the number of occurring vertex colors below
it in the canonical well-ordering (`Babai.natRank`). -/
noncomputable def natVColor (Y : KAryPartStruct V C m) (v : V) : ℕ :=
  natRank (Set.range Y.vcolor) (Y.vcolor v)

theorem natVColor_eq_iff (Y : KAryPartStruct V C m) (u v : V) :
    Y.natVColor u = Y.natVColor v ↔ Y.vcolor u = Y.vcolor v :=
  natRank_eq_iff (Set.finite_range _) ⟨u, rfl⟩ ⟨v, rfl⟩

/-- The blocks of the colored partition: two vertices are in the same block if they have
the same vertex color and lie in the same member of the family `P` (the blocks the Design
Lemma puts on the dominant class; `P = ∅` in outcome (a)). -/
def designRel (Y : KAryPartStruct V C m) (P : Set (Set V)) (u v : V) : Prop :=
  Y.vcolor u = Y.vcolor v ∧ ∀ A ∈ P, (u ∈ A ↔ v ∈ A)

/-- `Babai.KAryPartStruct.designRel` is an equivalence relation. -/
def designSetoid (Y : KAryPartStruct V C m) (P : Set (Set V)) : Setoid V where
  r := Y.designRel P
  iseqv :=
    { refl := fun _ => ⟨rfl, fun _ _ => Iff.rfl⟩
      symm := fun h => ⟨h.1.symm, fun A hA => (h.2 A hA).symm⟩
      trans := fun h₁ h₂ => ⟨h₁.1.trans h₂.1, fun A hA => (h₁.2 A hA).trans (h₂.2 A hA)⟩ }

/-- Outcomes (a) and (b) of Theorem 8.1.2 as an object of `Babai.ColoredPartitions`
(Def. 7.1.1): the canonical coloring together with the partition of the dominant class. -/
noncomputable def designPart (Y : KAryPartStruct V C m) (P : Set (Set V)) :
    ColoredPartition V ℕ where
  color := Y.natVColor
  part := Y.designSetoid P
  part_le_color h := by
    show Y.natVColor _ = Y.natVColor _
    exact (Y.natVColor_eq_iff _ _).2 h.1

theorem designPart_block (Y : KAryPartStruct V C m) (P : Set (Set V)) (u : V) :
    (Y.designPart P).block u = {v | Y.vcolor v = Y.vcolor u ∧ ∀ A ∈ P, (v ∈ A ↔ u ∈ A)} :=
  rfl

theorem designPart_colorClass (Y : KAryPartStruct V C m) (P : Set (Set V)) (u : V) :
    (Y.designPart P).colorClass ((Y.designPart P).color u) = Y.vclass (Y.vcolor u) := by
  ext v
  exact Y.natVColor_eq_iff v u

/-! #### The blocks -/

variable {α : ℝ}

theorem mem_dominantClass_of_vcolor_eq (Y : KAryPartStruct V C m) {u v : V}
    (h : Y.vcolor v = Y.vcolor u) (hu : u ∈ dominantClass α Y) :
    v ∈ dominantClass α Y := by
  show IsDominant α (Y.vclass (Y.vcolor v))
  rw [h]; exact hu

/-- Outside the dominant class the blocks are the whole vertex-color classes: the Design
Lemma partitions only the dominant class. -/
theorem designPart_block_of_notMem (Y : KAryPartStruct V C m) {P : Set (Set V)}
    (hP : ∀ A ∈ P, A ⊆ dominantClass α Y) {u : V} (hu : u ∉ dominantClass α Y) :
    (Y.designPart P).block u = Y.vclass (Y.vcolor u) := by
  ext v
  constructor
  · intro h; exact h.1
  · intro h
    have h' : Y.vcolor v = Y.vcolor u := h
    refine ⟨h, fun A hA => ?_⟩
    have hv : v ∉ A := fun hva =>
      hu (mem_dominantClass_of_vcolor_eq Y h'.symm (hP A hA hva))
    have hu' : u ∉ A := fun hua => hu (hP A hA hua)
    exact ⟨fun hc => absurd hc hv, fun hc => absurd hc hu'⟩

/-- Inside the dominant class the block of `u` is the member of the equipartition that
contains `u`. -/
theorem designPart_block_of_mem (hα : 1 / 2 ≤ α) (Y : KAryPartStruct V C m)
    {P : Set (Set V)}
    (hP : IsEquipartitionOn P (dominantClass α Y)) {u : V} (hu : u ∈ dominantClass α Y)
    {A : Set V} (hA : A ∈ P) (huA : u ∈ A) :
    (Y.designPart P).block u = A := by
  have hDeq : dominantClass α Y = Y.vclass (Y.vcolor u) := by
    ext w
    constructor
    · intro hw
      exact (IsDominant.subsingleton hα Y.vcolor hw hu :
        Y.vcolor w = Y.vcolor u)
    · intro hw
      exact mem_dominantClass_of_vcolor_eq Y hw hu
  ext v
  constructor
  · rintro ⟨-, h2⟩
    exact (h2 A hA).2 huA
  · intro hv
    have hvD : v ∈ dominantClass α Y := hP.subset A hA hv
    refine ⟨by rw [hDeq] at hvD; exact hvD, fun B hB => ?_⟩
    constructor
    · intro hvB
      by_cases hBA : B = A
      · rw [hBA]; exact huA
      · exact absurd hv (Set.disjoint_left.1 (hP.pairwiseDisjoint B hB A hA hBA) hvB)
    · intro huB
      by_cases hBA : B = A
      · rw [hBA]; exact hv
      · exact absurd huA (Set.disjoint_left.1 (hP.pairwiseDisjoint B hB A hA hBA) huB)

/-! #### Outcomes (a) and (b) give a colored `α`-partition -/

theorem dominantClass_eq_empty_of_noDominantColor (Y : KAryPartStruct V C m)
    (hnd : NoDominantColor α Y) : dominantClass α Y = ∅ := by
  have h : ¬ HasDominantClass α Y := by
    rw [← not_noDominantColor_iff]; exact not_not.2 hnd
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hv
  exact h ⟨Y.vcolor v, hv⟩

/-- Outcome (a) of Theorem 8.1.2 is a colored `α`-partition (Def. 7.1.1): every block is a
whole vertex-color class, and no vertex-color class has size `> αn`.  (Observation 7.1.4,
first case.) -/
theorem designPart_isAlphaPartition_of_noDominant (hα : 1 / 2 ≤ α)
    (Y : KAryPartStruct V C m) (hnd : NoDominantColor α Y) :
    (Y.designPart ∅).IsAlphaPartition α := by
  have hD := dominantClass_eq_empty_of_noDominantColor (α := α) Y hnd
  have hblock : ∀ u : V, (Y.designPart ∅).block u = Y.vclass (Y.vcolor u) := by
    intro u
    refine designPart_block_of_notMem (α := α) Y (fun A hA => absurd hA (by simp)) ?_
    rw [hD]; exact Set.notMem_empty u
  refine (Y.designPart ∅).isAlphaPartition_of hα (fun u v h => ?_) (fun u h => ?_)
    (Or.inl fun c => ?_)
  · have hc : Y.vcolor u = Y.vcolor v := (Y.natVColor_eq_iff u v).1 h
    rw [hblock, hblock, hc]
  · rw [hblock]
    rw [designPart_colorClass] at h
    exact h
  · by_cases hc : ∃ u : V, (Y.designPart ∅).color u = c
    · obtain ⟨u, rfl⟩ := hc
      rw [designPart_colorClass]
      exact hnd (Y.vcolor u)
    · push_neg at hc
      have hempty : (Y.designPart ∅).colorClass c = ∅ := by
        ext v
        exact ⟨fun hv => hc v hv, fun hv => absurd hv (Set.notMem_empty v)⟩
      rw [hempty, Set.ncard_empty]
      have : (0 : ℝ) ≤ α * (Fintype.card V : ℝ) := by positivity
      simpa using this

omit [DecidableEq V] in
theorem exists_mem_of_mem_dominantClass {P : Set (Set V)} {Y : KAryPartStruct V C m}
    (hP : IsEquipartitionOn P (dominantClass α Y)) {u : V} (hu : u ∈ dominantClass α Y) :
    ∃ A ∈ P, u ∈ A := by
  have : u ∈ ⋃₀ P := by rw [hP.covers]; exact hu
  exact this

/-- Outcome (b) of Theorem 8.1.2 is a colored `α`-partition (Def. 7.1.1): the dominant
color class is partitioned into at least two blocks, each of size `≥ 2`.  (Observation
7.1.4, second case.) -/
theorem designPart_isAlphaPartition_of_dominant (hα : 1 / 2 ≤ α)
    (Y : KAryPartStruct V C m) (P : Set (Set V)) (hdom : HasDominantClass α Y)
    (hP : IsEquipartitionOn P (dominantClass α Y)) (hPnt : IsNontrivialPartition P) :
    (Y.designPart P).IsAlphaPartition α := by
  classical
  obtain ⟨i, hi⟩ := hdom
  have hDi : dominantClass α Y = Y.vclass i := dominantClass_eq hα Y hi
  have hDpos : (0 : ℝ) < ((dominantClass α Y).ncard : ℝ) := by
    have h0 : (0 : ℝ) ≤ α * (Fintype.card V : ℝ) := by positivity
    have : α * (Fintype.card V : ℝ) < ((Y.vclass i).ncard : ℝ) := hi
    rw [hDi]; linarith
  obtain ⟨u₀, hu₀⟩ : (dominantClass α Y).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hc
    rw [hc, Set.ncard_empty] at hDpos
    exact absurd hDpos (by norm_num)
  have hDeq : dominantClass α Y = Y.vclass (Y.vcolor u₀) := by
    ext w
    exact ⟨fun hw => (IsDominant.subsingleton hα Y.vcolor hw hu₀ : Y.vcolor w = Y.vcolor u₀),
      fun hw => mem_dominantClass_of_vcolor_eq Y hw hu₀⟩
  -- the block of a vertex
  have hblock : ∀ u : V, u ∈ dominantClass α Y →
      ∀ A ∈ P, u ∈ A → (Y.designPart P).block u = A :=
    fun u hu A hA huA => designPart_block_of_mem hα Y hP hu hA huA
  have hblock' : ∀ u : V, u ∉ dominantClass α Y →
      (Y.designPart P).block u = Y.vclass (Y.vcolor u) :=
    fun u hu => designPart_block_of_notMem Y hP.subset hu
  refine (Y.designPart P).isAlphaPartition_of hα (fun u v h => ?_) (fun u h => ?_)
    (Or.inr ⟨u₀, ?_, ?_⟩)
  · -- equipartition
    have hc : Y.vcolor u = Y.vcolor v := (Y.natVColor_eq_iff u v).1 h
    by_cases hu : u ∈ dominantClass α Y
    · have hv : v ∈ dominantClass α Y := mem_dominantClass_of_vcolor_eq Y hc.symm hu
      obtain ⟨A, hA, huA⟩ := exists_mem_of_mem_dominantClass hP hu
      obtain ⟨B, hB, hvB⟩ := exists_mem_of_mem_dominantClass hP hv
      rw [hblock u hu A hA huA, hblock v hv B hB hvB]
      exact hP.equal_size A hA B hB
    · have hv : v ∉ dominantClass α Y := fun hv =>
        hu (mem_dominantClass_of_vcolor_eq Y hc hv)
      rw [hblock' u hu, hblock' v hv, hc]
  · -- admissible
    rw [designPart_colorClass] at h
    by_cases hu : u ∈ dominantClass α Y
    · obtain ⟨A, hA, huA⟩ := exists_mem_of_mem_dominantClass hP hu
      rw [hblock u hu A hA huA]
      exact Set.one_lt_ncard_iff_nontrivial.2 (hPnt.2 A hA)
    · rw [hblock' u hu]; exact h
  · -- the dominant class has more than half the vertices
    have hcard : α * (Fintype.card V : ℝ) < ((dominantClass α Y).ncard : ℝ) := by
      rw [hDi]; exact hi
    have h2 : (Fintype.card V : ℝ) < 2 * ((dominantClass α Y).ncard : ℝ) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card V)]
    rw [designPart_colorClass, ← hDeq]
    exact_mod_cast h2
  · -- the dominant class has at least two blocks
    obtain ⟨A, hA, B, hB, hAB⟩ := hPnt.1
    obtain ⟨A₀, hA₀, hu₀A₀⟩ := exists_mem_of_mem_dominantClass hP hu₀
    obtain ⟨E, hE, hEne⟩ : ∃ E ∈ P, E ≠ A₀ := by
      by_cases hAA : A = A₀
      · exact ⟨B, hB, fun hc => hAB (by rw [hAA, hc])⟩
      · exact ⟨A, hA, hAA⟩
    obtain ⟨y, hy⟩ := hP.nonempty E hE
    have hyD : y ∈ dominantClass α Y := hP.subset E hE hy
    refine ⟨y, ?_, ?_⟩
    · exact (Y.natVColor_eq_iff y u₀).2 (by rw [hDeq] at hyD; exact hyD)
    · intro hpart
      have hmem : y ∈ A₀ := (hpart.2 A₀ hA₀).2 hu₀A₀
      exact absurd hmem (Set.disjoint_left.1 (hP.pairwiseDisjoint E hE A₀ hA₀ hEne) hy)

end KAryPartStruct

/-! ### 4. The UPCC of outcome (c)

Outcome (c) of Theorem 8.1.2 returns *"a canonically embedded uniprimitive coherent
configuration (UPCC) whose vertex set is the dominant color class"*: the subconfiguration
of `X* = (X_x⃗)^{(2)}` induced on the dominant class.  Two things have to be arranged for
it to be an object of `Babai.UPCCs`: the colors must be named by natural numbers
(`Babai.PartitionStructure.ofNatColoring`), and the vertex set must be a subset of the
ambient type `Ω`, not of `□X` (`Babai.KAryPartStruct.domImageEquiv`). -/

namespace KAryPartStruct

variable {Ω : Type} {s : Set Ω} [Fintype ↥s] [DecidableEq ↥s] {C : Type*} {m : ℕ}

/-- The dominant class, read as a subset of the ambient type `Ω`. -/
def domImage (α : ℝ) (Y : KAryPartStruct ↥s C m) : Set Ω :=
  Subtype.val '' dominantClass α Y

theorem domImage_subset (α : ℝ) (Y : KAryPartStruct ↥s C m) : domImage α Y ⊆ s := by
  rintro _ ⟨v, -, rfl⟩
  exact v.2

theorem finite_domImage (α : ℝ) (Y : KAryPartStruct ↥s C m) : (domImage α Y).Finite :=
  (Set.toFinite _).image _

noncomputable instance instFintypeDomImage (α : ℝ) (Y : KAryPartStruct ↥s C m) :
    Fintype ↥(domImage α Y) := (finite_domImage α Y).fintype

theorem ncard_domImage (α : ℝ) (Y : KAryPartStruct ↥s C m) :
    (domImage α Y).ncard = (dominantClass α Y).ncard :=
  Set.ncard_image_of_injective _ Subtype.val_injective

/-- The dominant class inside `□X` and its image in `Ω` are in bijection. -/
noncomputable def domImageEquiv (α : ℝ) (Y : KAryPartStruct ↥s C m) :
    ↥(dominantClass α Y) ≃ ↥(domImage α Y) :=
  Equiv.Set.image Subtype.val (dominantClass α Y) Subtype.val_injective

theorem domImageEquiv_val (α : ℝ) (Y : KAryPartStruct ↥s C m)
    (v : ↥(dominantClass α Y)) :
    (((domImageEquiv α Y) v : ↥(domImage α Y)) : Ω) = ((v : ↥s) : Ω) := rfl

/-- The color of a pair of vertices of the dominant class in `X* = Y^{(2)}`, read on the
image of the dominant class in `Ω`. -/
noncomputable def upccPairColor (α : ℝ) (Y : KAryPartStruct ↥s C m) (hm : 2 ≤ m)
    (a b : ↥(domImage α Y)) : C :=
  Y.pairColor hm (((domImageEquiv α Y).symm a : ↥(dominantClass α Y)) : ↥s)
    (((domImageEquiv α Y).symm b : ↥(dominantClass α Y)) : ↥s)

/-- Outcome (c) of Theorem 8.1.2 as a partition structure (Def. 3.1.1) on the image of the
dominant class, with the colors named by `Babai.natRank`. -/
noncomputable def upccStruct (α : ℝ) (Y : KAryPartStruct ↥s C m) (hm : 2 ≤ m) :
    PartitionStructure ↥(domImage α Y) :=
  PartitionStructure.ofNatColoring (upccPairColor α Y hm)

/-- Outcome (c) of Theorem 8.1.2 as an `ℕ`-coloring, which is what the category
`Babai.UPCCs` takes. -/
noncomputable def upccColoring (α : ℝ) (Y : KAryPartStruct ↥s C m) (hm : 2 ≤ m) :
    ↥(domImage α Y) → ↥(domImage α Y) → ℕ :=
  (upccStruct α Y hm).natColor


/-! #### The dominant class carries a homogeneous coherent configuration -/

variable {α : ℝ}

theorem dominantClass_nonempty (hα : 1 / 2 ≤ α) (Y : KAryPartStruct ↥s C m)
    (hdom : HasDominantClass α Y) : (dominantClass α Y).Nonempty := by
  obtain ⟨i, hi⟩ := hdom
  have hDi : dominantClass α Y = Y.vclass i := dominantClass_eq hα Y hi
  have h0 : (0 : ℝ) ≤ α * (Fintype.card ↥s : ℝ) := by
    have : (0 : ℝ) ≤ α := by linarith
    positivity
  have hpos : 0 < (Y.vclass i).ncard := by
    have : α * (Fintype.card ↥s : ℝ) < ((Y.vclass i).ncard : ℝ) := hi
    have hlt : (0 : ℝ) < ((Y.vclass i).ncard : ℝ) := lt_of_le_of_lt h0 this
    exact_mod_cast hlt
  rw [hDi]
  exact (Set.ncard_pos (Set.toFinite _)).1 hpos

theorem dominantClass_eq_vclass (hα : 1 / 2 ≤ α) (Y : KAryPartStruct ↥s C m) {u₀ : ↥s}
    (hu₀ : u₀ ∈ dominantClass α Y) : dominantClass α Y = Y.vclass (Y.vcolor u₀) := by
  ext w
  exact ⟨fun hw => (IsDominant.subsingleton hα Y.vcolor hw hu₀ : Y.vcolor w = Y.vcolor u₀),
    fun hw => mem_dominantClass_of_vcolor_eq Y hw hu₀⟩

/-- §8.1, the proof of Theorem 8.1.2: the dominant class is a vertex-color class of
`X* = (X_x⃗)^{(2)}`, hence a stable set, so `X*[C]` is a homogeneous coherent
configuration (Obs. 3.3.2). -/
theorem induced_isCoherent_isHomogeneous (hα : 1 / 2 ≤ α) (Y : KAryPartStruct ↥s C m)
    (hY : Y.IsCoherent) (hm : 2 ≤ m) (hdom : HasDominantClass α Y) :
    ((Y.skel2 hm).induced (dominantClass α Y)).IsCoherent ∧
      ((Y.skel2 hm).induced (dominantClass α Y)).IsHomogeneous := by
  classical
  obtain ⟨u₀, hu₀⟩ := dominantClass_nonempty hα Y hdom
  have hDeq := dominantClass_eq_vclass hα Y hu₀
  have hC : dominantClass α Y
      = (Y.skel2 hm).vertexClass ((Y.skel2 hm).vcolor u₀) := by
    rw [skel2_vertexClass_eq, hDeq]
  have hstable : (Y.skel2 hm).IsStable (dominantClass α Y) := by
    rw [hC]; exact PartitionStructure.isStable_vertexClass _ _
  have hScoh : (Y.skel2 hm).IsCoherent := skel2_isCoherent Y hY hm
  refine ⟨PartitionStructure.induced_isCoherent _ hScoh hstable, ?_⟩
  refine PartitionStructure.induced_isHomogeneous _ (fun a ha b hb => ?_)
  rw [hC] at ha hb
  exact ha.trans hb.symm

/-- §8.1, the proof of Theorem 8.1.2, the case in which outcome (c) is reached: if
`X*[C]` is not a clique configuration and has no disconnected non-diagonal constituent,
then it is a UPCC.  This is the second half of the dichotomy
`Babai.KAryPartStruct.imprimitive_or_uniprimitive`, with the first alternative excluded by
the hypothesis `hno`. -/
theorem induced_isUniprimitive (hα : 1 / 2 ≤ α) (Y : KAryPartStruct ↥s C m)
    (hY : Y.IsCoherent) (hm : 2 ≤ m) (hdom : HasDominantClass α Y)
    (hnt : (dominantClass α Y).Nontrivial)
    (hclq : ¬ (Y.skel2 hm).IsCliqueOn (dominantClass α Y))
    (hno : ¬ ∃ c : C, IsDesignColor α Y hm c) :
    ((Y.skel2 hm).induced (dominantClass α Y)).IsUniprimitive := by
  classical
  obtain ⟨hZcoh, hZhom⟩ := induced_isCoherent_isHomogeneous hα Y hY hm hdom
  have hScoh : (Y.skel2 hm).IsCoherent := skel2_isCoherent Y hY hm
  have hrk : ((Y.skel2 hm).induced (dominantClass α Y)).rank ≠ 2 := fun hc =>
    hclq ((PartitionStructure.isCliqueOn_iff _ _ _).2 hc)
  have hrank : 3 ≤ ((Y.skel2 hm).induced (dominantClass α Y)).rank :=
    PartitionStructure.three_le_rank_induced _ hScoh.toIsConfiguration hnt hrk
  refine ⟨⟨hZhom, fun j hoff => ?_⟩, hrank⟩
  by_contra hdisc
  exact hno (exists_isDesignColor α Y hm hoff hdisc)

/-- The colors of `upccStruct` are the colors of `X*` on the dominant class: the naming
changes nothing but the names. -/
theorem upccStruct_color_eq_iff (α : ℝ) (Y : KAryPartStruct ↥s C m) (hm : 2 ≤ m)
    (a b a' b' : ↥(domImage α Y)) :
    (((Y.skel2 hm).induced (dominantClass α Y)).congrEquiv
          (domImageEquiv α Y)).color a b
        = (((Y.skel2 hm).induced (dominantClass α Y)).congrEquiv
          (domImageEquiv α Y)).color a' b'
      ↔ (upccStruct α Y hm).color a b = (upccStruct α Y hm).color a' b' := by
  rw [upccStruct, PartitionStructure.ofNatColoring_color_eq_iff]
  show ((Y.skel2 hm).induced (dominantClass α Y)).color ((domImageEquiv α Y).symm a)
        ((domImageEquiv α Y).symm b)
      = ((Y.skel2 hm).induced (dominantClass α Y)).color ((domImageEquiv α Y).symm a')
        ((domImageEquiv α Y).symm b')
    ↔ _
  rw [PartitionStructure.induced_color_eq_iff, skel2_color_eq_iff']
  exact Iff.rfl

/-- Outcome (c) of Theorem 8.1.2: the coloring produced is a UPCC coloring in the sense of
Def. 3.2.1 (`Babai.IsUPCCColoring`). -/
theorem isUPCCColoring_upccColoring (α : ℝ) (Y : KAryPartStruct ↥s C m) (hm : 2 ≤ m)
    (hcoh : ((Y.skel2 hm).induced (dominantClass α Y)).IsCoherent)
    (huni : ((Y.skel2 hm).induced (dominantClass α Y)).IsUniprimitive) :
    IsUPCCColoring (upccColoring α Y hm) := by
  refine ⟨upccStruct α Y hm, ?_, ?_, rfl⟩
  · exact PartitionStructure.isCoherent_congr (upccStruct_color_eq_iff α Y hm)
      (PartitionStructure.congrEquiv_isCoherent _ hcoh)
  · exact PartitionStructure.isUniprimitive_congr (upccStruct_color_eq_iff α Y hm)
      (PartitionStructure.congrEquiv_isUniprimitive _ huni)

/-! ### 5. Canonicity of the outcome for a fixed color type -/

/-- A UPCC coloring carried along a bijection of vertex sets is a UPCC coloring. -/
theorem _root_.Babai.isUPCCColoring_congr {Ω : Type} {t₁ t₂ : Set Ω}
    {c₁ : ↥t₁ → ↥t₁ → ℕ} {c₂ : ↥t₂ → ↥t₂ → ℕ} (g : ↥t₁ ≃ ↥t₂)
    (hg : ∀ x y, c₂ (g x) (g y) = c₁ x y) (h : IsUPCCColoring c₁) : IsUPCCColoring c₂ := by
  obtain ⟨S, hcoh, huni, hnat⟩ := h
  refine ⟨S.congrEquiv g, PartitionStructure.congrEquiv_isCoherent _ hcoh,
    PartitionStructure.congrEquiv_isUniprimitive _ huni, ?_⟩
  funext a b
  have h1 : (S.congrEquiv g).natColor a b = S.natColor (g.symm a) (g.symm b) := rfl
  rw [h1, show S.natColor = c₁ from hnat, ← hg (g.symm a) (g.symm b),
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]

section Canonical

variable {t : Set Ω} [Fintype ↥t] [DecidableEq ↥t] {Y : KAryPartStruct ↥s C m}
  {Y' : KAryPartStruct ↥t C m} {f : ↥s ≃ ↥t}

theorem range_vcolor_canonical (hf : f ∈ Iso Y Y') :
    Set.range Y'.vcolor = Set.range Y.vcolor := by
  ext c
  constructor
  · rintro ⟨v', rfl⟩
    exact ⟨f.symm v', by rw [← vcolor_canonical Y Y' hf, Equiv.apply_symm_apply]⟩
  · rintro ⟨v, rfl⟩
    exact ⟨f v, vcolor_canonical Y Y' hf v⟩

/-- The `ℕ`-name of the vertex color is canonical. -/
theorem natVColor_canonical (hf : f ∈ Iso Y Y') (v : ↥s) :
    Y'.natVColor (f v) = Y.natVColor v := by
  rw [natVColor, natVColor, range_vcolor_canonical hf, vcolor_canonical Y Y' hf]

theorem domImageEquiv_symm_val (α : ℝ) (Y : KAryPartStruct ↥s C m)
    (a : ↥(domImage α Y)) :
    ((((domImageEquiv α Y).symm a : ↥(dominantClass α Y)) : ↥s) : Ω) = (a : Ω) := by
  have h := domImageEquiv_val α Y ((domImageEquiv α Y).symm a)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- The bijection of the images of the dominant classes induced by `f`. -/
noncomputable def domImgEquiv (α : ℝ) (hf : f ∈ Iso Y Y') :
    ↥(domImage α Y) ≃ ↥(domImage α Y') :=
  ((domImageEquiv α Y).symm.trans (domEquiv (α := α) hf)).trans (domImageEquiv α Y')

theorem domImgEquiv_val (α : ℝ) (hf : f ∈ Iso Y Y') (a : ↥(domImage α Y)) :
    ((domImgEquiv α hf a : ↥(domImage α Y')) : Ω)
      = ((f ⟨(a : Ω), domImage_subset α Y a.2⟩ : ↥t) : Ω) := by
  have h : (((domImageEquiv α Y).symm a : ↥(dominantClass α Y)) : ↥s)
      = ⟨(a : Ω), domImage_subset α Y a.2⟩ :=
    Subtype.ext (domImageEquiv_symm_val α Y a)
  show ((f (((domImageEquiv α Y).symm a : ↥(dominantClass α Y)) : ↥s) : ↥t) : Ω) = _
  rw [h]

theorem upccPairColor_canonical (α : ℝ) (hm : 2 ≤ m) (hf : f ∈ Iso Y Y')
    (a b : ↥(domImage α Y)) :
    upccPairColor α Y' hm (domImgEquiv α hf a) (domImgEquiv α hf b)
      = upccPairColor α Y hm a b := by
  show Y'.pairColor hm
      (((domImageEquiv α Y').symm (domImgEquiv α hf a) : ↥(dominantClass α Y')) : ↥t)
      (((domImageEquiv α Y').symm (domImgEquiv α hf b) : ↥(dominantClass α Y')) : ↥t)
    = Y.pairColor hm _ _
  have hsymm : ∀ c : ↥(domImage α Y),
      (domImageEquiv α Y').symm (domImgEquiv α hf c)
        = domEquiv (α := α) hf ((domImageEquiv α Y).symm c) := by
    intro c
    show (domImageEquiv α Y').symm
      ((domImageEquiv α Y') (domEquiv (α := α) hf ((domImageEquiv α Y).symm c))) = _
    rw [Equiv.symm_apply_apply]
  rw [hsymm a, hsymm b]
  exact pairColor_canonical hf _ _

theorem natCodes_upccPairColor_canonical (α : ℝ) (hm : 2 ≤ m) (hf : f ∈ Iso Y Y') :
    PartitionStructure.natCodes (upccPairColor α Y' hm)
      = PartitionStructure.natCodes (upccPairColor α Y hm) := by
  ext c
  constructor
  · rintro ⟨⟨a', b'⟩, rfl⟩
    refine ⟨((domImgEquiv α hf).symm a', (domImgEquiv α hf).symm b'), ?_⟩
    show upccPairColor α Y hm ((domImgEquiv α hf).symm a') ((domImgEquiv α hf).symm b')
      = upccPairColor α Y' hm a' b'
    rw [← upccPairColor_canonical α hm hf, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact ⟨(domImgEquiv α hf a, domImgEquiv α hf b),
      upccPairColor_canonical α hm hf a b⟩

/-- Outcome (c) is canonical: the `ℕ`-coloring of the UPCC on the dominant class is
carried by `f` to the `ℕ`-coloring of the UPCC on the dominant class of `Y'`. -/
theorem upccColoring_canonical (α : ℝ) (hm : 2 ≤ m) (hf : f ∈ Iso Y Y')
    (a b : ↥(domImage α Y)) :
    upccColoring α Y' hm (domImgEquiv α hf a) (domImgEquiv α hf b)
      = upccColoring α Y hm a b := by
  show natRank (PartitionStructure.natCodes (upccPairColor α Y' hm))
      (upccPairColor α Y' hm (domImgEquiv α hf a) (domImgEquiv α hf b))
    = natRank (PartitionStructure.natCodes (upccPairColor α Y hm))
      (upccPairColor α Y hm a b)
  rw [natCodes_upccPairColor_canonical α hm hf, upccPairColor_canonical α hm hf]

/-! ### 6. The outcome attached to a string -/

theorem designPart_iso (hf : f ∈ Iso Y Y') (Q : Set (Set ↥s)) (Q' : Set (Set ↥t))
    (hQ : Q' = (fun A : Set ↥s => f '' A) '' Q) :
    f ∈ (ColoredPartitions Ω ℕ).Iso (Y.designPart Q) (Y'.designPart Q') := by
  subst hQ
  refine ⟨fun x => natVColor_canonical hf x, fun x y => ?_⟩
  constructor
  · rintro ⟨hc, hA⟩
    refine ⟨?_, ?_⟩
    · rw [vcolor_canonical Y Y' hf, vcolor_canonical Y Y' hf, hc]
    · rintro _ ⟨A, hA', rfl⟩
      rw [Set.mem_image_equiv, Set.mem_image_equiv, Equiv.symm_apply_apply,
        Equiv.symm_apply_apply]
      exact hA A hA'
  · rintro ⟨hc, hA⟩
    refine ⟨?_, fun A hA' => ?_⟩
    · have h1 := vcolor_canonical Y Y' hf x
      have h2 := vcolor_canonical Y Y' hf y
      rw [h1, h2] at hc
      exact hc
    · have h := hA (f '' A) ⟨A, hA', rfl⟩
      rw [Set.mem_image_equiv, Set.mem_image_equiv, Equiv.symm_apply_apply,
        Equiv.symm_apply_apply] at h
      exact h

/-- The outcome of Theorem 8.1.2 at the `k`-ary coherent configuration `Y = X_x⃗`: a
colored partition of the vertex set, or the UPCC on the dominant class.  It is a function
of `Y` alone, with no choice: the three cases are told apart by whether the canonical
equipartition of the dominant class is nontrivial and by whether the subconfiguration of
`Y^{(2)}` induced on the dominant class is a UPCC. -/
noncomputable def designOutcomeOf (α : ℝ) (Y : KAryPartStruct ↥s C m) :
    (Cat.sub (DesignOutcomes Ω)).Obj s :=
  if hm : 2 ≤ m then
    if _ : (designPartition α Y hm).Nonempty then
      ⟨⟨s, subset_rfl⟩, Sum.inl (Y.designPart (designPartition α Y hm))⟩
    else if hU : IsUPCCColoring (upccColoring α Y hm) then
      ⟨⟨domImage α Y, domImage_subset α Y⟩, Sum.inr ⟨upccColoring α Y hm, hU⟩⟩
    else ⟨⟨s, subset_rfl⟩, Sum.inl (Y.designPart ∅)⟩
  else ⟨⟨s, subset_rfl⟩, Sum.inl (Y.designPart ∅)⟩

/-- *"Canonicity in the above statements is relative to `x⃗`"* (§8.1): an isomorphism
`f : Y → Y'` carries the outcome of `Y` to the outcome of `Y'`. -/
theorem designOutcomeOf_canonical (α : ℝ) (hf : f ∈ Iso Y Y') :
    f ∈ (Cat.sub (DesignOutcomes Ω)).Iso (designOutcomeOf α Y) (designOutcomeOf α Y') := by
  classical
  have hleft : ∀ (Q : Set (Set ↥s)) (Q' : Set (Set ↥t)),
      Q' = (fun A : Set ↥s => f '' A) '' Q →
      f ∈ (Cat.sub (DesignOutcomes Ω)).Iso
        (⟨⟨s, subset_rfl⟩, Sum.inl (Y.designPart Q)⟩ : (Cat.sub (DesignOutcomes Ω)).Obj s)
        (⟨⟨t, subset_rfl⟩, Sum.inl (Y'.designPart Q')⟩) := by
    intro Q Q' hQ
    exact ⟨f, fun _ => rfl, designPart_iso hf Q Q' hQ⟩
  rw [designOutcomeOf, designOutcomeOf]
  by_cases hm : 2 ≤ m
  · rw [dif_pos hm, dif_pos hm]
    have hQ : designPartition α Y' hm = (fun A : Set ↥s => f '' A) '' designPartition α Y hm :=
      designPartition_canonical hf
    have hPiff : (designPartition α Y' hm).Nonempty ↔ (designPartition α Y hm).Nonempty := by
      rw [hQ]
      exact ⟨fun ⟨_, A, hA, _⟩ => ⟨A, hA⟩, fun ⟨A, hA⟩ => ⟨f '' A, A, hA, rfl⟩⟩
    by_cases hP : (designPartition α Y hm).Nonempty
    · rw [dif_pos hP, dif_pos (hPiff.2 hP)]
      exact hleft _ _ hQ
    · rw [dif_neg hP, dif_neg (fun h => hP (hPiff.1 h))]
      have hUiff : IsUPCCColoring (upccColoring α Y' hm)
          ↔ IsUPCCColoring (upccColoring α Y hm) := by
        constructor
        · intro h
          exact isUPCCColoring_congr (domImgEquiv α hf).symm
            (fun x y => by
              rw [← upccColoring_canonical α hm hf ((domImgEquiv α hf).symm x)
                ((domImgEquiv α hf).symm y), Equiv.apply_symm_apply,
                Equiv.apply_symm_apply]) h
        · exact isUPCCColoring_congr (domImgEquiv α hf) (upccColoring_canonical α hm hf)
      by_cases hU : IsUPCCColoring (upccColoring α Y hm)
      · rw [dif_pos hU, dif_pos (hUiff.2 hU)]
        exact ⟨domImgEquiv α hf, domImgEquiv_val α hf, upccColoring_canonical α hm hf⟩
      · rw [dif_neg hU, dif_neg (fun h => hU (hUiff.1 h))]
        exact hleft _ _ (by simp)
  · rw [dif_neg hm, dif_neg hm]
    exact hleft _ _ (by simp)

/-! ### 7. The outcome is one of (a), (b), (c) of Theorem 8.1.2 -/

theorem nonempty_of_isUPCCColoring {t₁ : Set Ω} {c : ↥t₁ → ↥t₁ → ℕ}
    (h : IsUPCCColoring c) : Nonempty ↥t₁ := by
  obtain ⟨S, -, huni, -⟩ := h
  have h3 : 3 ≤ S.rank := huni.2
  obtain ⟨x, -, -⟩ := S.color_surjective ⟨0, by omega⟩
  exact ⟨x⟩

theorem designPartition_eq_empty (α : ℝ) (Y : KAryPartStruct ↥s C m) (hm : 2 ≤ m)
    (hD : dominantClass α Y = ∅) : designPartition α Y hm = ∅ := by
  classical
  have hempty : IsEmpty ↥(dominantClass α Y) := by
    rw [hD]; exact Set.isEmpty_coe_sort.2 rfl
  rcases h : designColor α Y hm with _ | c
  · exact designPartition_of_eq_none h
  · rw [designPartition_of_eq_some h]
    have : (designDigraph α Y hm c).weakComponents = ∅ := by
      rw [Digraph.weakComponents, Set.range_eq_empty_iff]
      exact hempty
    rw [this, Set.image_empty]

theorem designPartition_nonempty (α : ℝ) (Y : KAryPartStruct ↥s C m) (hm : 2 ≤ m)
    (hD : (dominantClass α Y).Nonempty) (hex : ∃ c : C, IsDesignColor α Y hm c) :
    (designPartition α Y hm).Nonempty := by
  obtain ⟨c, hc, -⟩ := designColor_eq_some α Y hm hex
  rw [designPartition_of_eq_some hc]
  obtain ⟨u, hu⟩ := hD
  exact ⟨_, ⟨_, ⟨(⟨u, hu⟩ : ↥(dominantClass α Y)), rfl⟩, rfl⟩⟩

/-- Lines 04–08 of Procedure "Design Lemma" (§8.2), read on the restriction `X_x⃗`
itself: the procedure returns at `x⃗`. -/
def ReturnsAtStruct (α : ℝ) (Y : KAryPartStruct ↥s C m) : Prop :=
  NoDominantColor α Y ∨ ∃ hm : 2 ≤ m, HasDominantClass α Y ∧
    ¬ (Y.skel2 hm).IsCliqueOn (dominantClass α Y)

/-- The kernel of the coloring of `X*[C]` is canonical: `f` carries the color classes of
the subconfiguration induced on the dominant class to those of `Y'`. -/
theorem induced_color_eq_iff_canonical (α : ℝ) (hm : 2 ≤ m) (hf : f ∈ Iso Y Y')
    (a b a' b' : ↥(dominantClass α Y')) :
    (((Y.skel2 hm).induced (dominantClass α Y)).congrEquiv
          (domEquiv (α := α) hf)).color a b
        = (((Y.skel2 hm).induced (dominantClass α Y)).congrEquiv
          (domEquiv (α := α) hf)).color a' b'
      ↔ ((Y'.skel2 hm).induced (dominantClass α Y')).color a b
        = ((Y'.skel2 hm).induced (dominantClass α Y')).color a' b' := by
  have hval : ∀ u' : ↥(dominantClass α Y'),
      f ((((domEquiv (α := α) hf).symm u' : ↥(dominantClass α Y)) : ↥s)) = (u' : ↥t) :=
    fun u' => domEquiv_symm_val (α := α) hf u'
  rw [PartitionStructure.induced_color_eq_iff, skel2_color_eq_iff']
  show ((Y.skel2 hm).induced (dominantClass α Y)).color
        ((domEquiv (α := α) hf).symm a) ((domEquiv (α := α) hf).symm b)
      = ((Y.skel2 hm).induced (dominantClass α Y)).color
        ((domEquiv (α := α) hf).symm a') ((domEquiv (α := α) hf).symm b')
    ↔ _
  rw [PartitionStructure.induced_color_eq_iff, skel2_color_eq_iff']
  rw [← hval a, ← hval b, ← hval a', ← hval b']
  simp only [pairColor_canonical hf]

theorem induced_rank_canonical (α : ℝ) (hm : 2 ≤ m) (hf : f ∈ Iso Y Y') :
    ((Y.skel2 hm).induced (dominantClass α Y)).rank
      = ((Y'.skel2 hm).induced (dominantClass α Y')).rank :=
  PartitionStructure.rank_congr (induced_color_eq_iff_canonical α hm hf)

theorem isCliqueOn_canonical (α : ℝ) (hm : 2 ≤ m) (hf : f ∈ Iso Y Y') :
    (Y.skel2 hm).IsCliqueOn (dominantClass α Y)
      ↔ (Y'.skel2 hm).IsCliqueOn (dominantClass α Y') := by
  unfold PartitionStructure.IsCliqueOn
  rw [induced_rank_canonical α hm hf]

theorem returnsAtStruct_congr (α : ℝ) (hf : f ∈ Iso Y Y') :
    ReturnsAtStruct α Y ↔ ReturnsAtStruct α Y' := by
  constructor
  · rintro (h | ⟨hm, hdom, hclq⟩)
    · exact Or.inl ((noDominantColor_canonical Y Y' hf).1 h)
    · refine Or.inr ⟨hm, ?_, fun hc => hclq ((isCliqueOn_canonical α hm hf).2 hc)⟩
      rw [← not_noDominantColor_iff] at hdom ⊢
      exact fun hcc => hdom ((noDominantColor_canonical Y Y' hf).2 hcc)
  · rintro (h | ⟨hm, hdom, hclq⟩)
    · exact Or.inl ((noDominantColor_canonical Y Y' hf).2 h)
    · refine Or.inr ⟨hm, ?_, fun hc => hclq ((isCliqueOn_canonical α hm hf).1 hc)⟩
      rw [← not_noDominantColor_iff] at hdom ⊢
      exact fun hcc => hdom ((noDominantColor_canonical Y Y' hf).1 hcc)

/-- The three outcomes of Theorem 8.1.2 do not depend on which `Fintype` instance is used
to read Def. 7.1.1. -/
theorem _root_.Babai.ColoredPartition.isAlphaPartition_inst {V : Type} (i₁ i₂ : Fintype V)
    {P : ColoredPartition V ℕ} {α : ℝ}
    (h : @ColoredPartition.IsAlphaPartition V ℕ P i₁ α) :
    @ColoredPartition.IsAlphaPartition V ℕ P i₂ α := by
  rw [Subsingleton.elim i₂ i₁]; exact h

variable [Fintype Ω] [DecidableEq Ω]

/-- Theorem 8.1.2, §8.1: at a string where Procedure "Design Lemma" returns, the outcome
`Babai.KAryPartStruct.designOutcomeOf` is one of the three outcomes (a), (b), (c).

Outcome (a) is the case `NoDominantColor`: every vertex-color class has size `≤ αn`, and
the blocks of the colored partition are the whole color classes.  Outcome (b) is the case
where the dominant class carries a nontrivial canonical equipartition, outcome (c) the
case where it does not, and then the subconfiguration of `(X_x⃗)^{(2)}` induced on it is a
UPCC (`Babai.KAryPartStruct.induced_isUniprimitive`). -/
theorem isDesignOutcome_designOutcomeOf (hα : 1 / 2 ≤ α) (Y : KAryPartStruct ↥s C m)
    (hY : Y.IsCoherent) (hn : 4 ≤ Fintype.card ↥s) (hR : ReturnsAtStruct α Y) :
    IsDesignOutcome α s ⟨(designOutcomeOf α Y).1.1, (designOutcomeOf α Y).2⟩ := by
  classical
  have hcard : Fintype.card ↥s = s.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  rcases hR with hnd | ⟨hm, hdom, hclq⟩
  · -- outcome (a)
    have hD : dominantClass α Y = ∅ := dominantClass_eq_empty_of_noDominantColor Y hnd
    have hout : designOutcomeOf α Y
        = ⟨⟨s, subset_rfl⟩, Sum.inl (Y.designPart ∅)⟩ := by
      rw [designOutcomeOf]
      by_cases hm : 2 ≤ m
      · rw [dif_pos hm,
          dif_neg (by rw [designPartition_eq_empty α Y hm hD]; exact Set.not_nonempty_empty)]
        refine dif_neg (fun hU => ?_)
        obtain ⟨a⟩ := nonempty_of_isUPCCColoring hU
        have hem : domImage α Y = ∅ := by rw [domImage, hD, Set.image_empty]
        exact absurd (hem ▸ a.2) (Set.notMem_empty ((a : Ω)))
      · rw [dif_neg hm]
    rw [hout]
    exact ⟨rfl, ColoredPartition.isAlphaPartition_inst _ _
      (designPart_isAlphaPartition_of_noDominant hα Y hnd)⟩
  · -- there is a dominant class
    have hdom' := hdom
    obtain ⟨i, hi⟩ := hdom'
    have hDi : dominantClass α Y = Y.vclass i := dominantClass_eq hα Y hi
    have hDcard : α * (Fintype.card ↥s : ℝ) < ((dominantClass α Y).ncard : ℝ) := by
      rw [hDi]; exact hi
    have hDne : (dominantClass α Y).Nonempty := dominantClass_nonempty hα Y hdom
    obtain ⟨hZcoh, hZhom⟩ := induced_isCoherent_isHomogeneous hα Y hY hm hdom
    have hnt : (dominantClass α Y).Nontrivial := by
      refine Set.one_lt_ncard_iff_nontrivial.1 ?_
      have h4 : (4 : ℝ) ≤ (Fintype.card ↥s : ℝ) := by exact_mod_cast hn
      have : (2 : ℝ) ≤ α * (Fintype.card ↥s : ℝ) := by nlinarith
      have h1 : (1 : ℝ) < ((dominantClass α Y).ncard : ℝ) := by linarith
      exact_mod_cast h1
    by_cases hP : (designPartition α Y hm).Nonempty
    · -- outcome (b)
      have hout : designOutcomeOf α Y
          = ⟨⟨s, subset_rfl⟩, Sum.inl (Y.designPart (designPartition α Y hm))⟩ := by
        rw [designOutcomeOf, dif_pos hm, dif_pos hP]
      have hex : ∃ c : C, IsDesignColor α Y hm c := by
        by_contra hno
        have hnone : designColor α Y hm = none := by
          unfold designColor firstOf
          rw [dif_neg hno]
        rw [designPartition_of_eq_none hnone] at hP
        exact absurd hP Set.not_nonempty_empty
      obtain ⟨hEq, hNt⟩ := designPartition_isEquipartitionOn α Y hm hZcoh hZhom hex
      rw [hout]
      exact ⟨rfl, ColoredPartition.isAlphaPartition_inst _ _
        (designPart_isAlphaPartition_of_dominant hα Y _ hdom hEq hNt)⟩
    · -- outcome (c)
      have hno : ¬ ∃ c : C, IsDesignColor α Y hm c := fun hex =>
        hP (designPartition_nonempty α Y hm hDne hex)
      have huni := induced_isUniprimitive hα Y hY hm hdom hnt hclq hno
      have hU : IsUPCCColoring (upccColoring α Y hm) :=
        isUPCCColoring_upccColoring α Y hm hZcoh huni
      have hout : designOutcomeOf α Y
          = ⟨⟨domImage α Y, domImage_subset α Y⟩,
            Sum.inr ⟨upccColoring α Y hm, hU⟩⟩ := by
        rw [designOutcomeOf, dif_pos hm, dif_neg hP, dif_pos hU]
      rw [hout]
      refine ⟨domImage_subset α Y, ?_⟩
      rw [ncard_domImage, ← hcard]
      exact hDcard

end Canonical
/-! ### 8. Transport of the outcome along an equality of color types

Across different vertex sets the `k`-WL color type depends on `|Ω|`
(`Workspace/Higher/WLCanonical.lean`), so the outcome has to be moved along an equality of
color types before the canonicity of §5 can be applied.  Since the transported structure
is *equal* to the original one once the equality of color types is substituted, every
object built from it is unchanged. -/

section Cast

variable {C₁ C₂ : Type u} {Ω : Type} {s : Set Ω} [Fintype ↥s] [DecidableEq ↥s] {m : ℕ}
  {α : ℝ} {Y₁ : KAryPartStruct ↥s C₁ m} {Y₂ : KAryPartStruct ↥s C₂ m}

theorem returnsAtStruct_cast (hC : C₁ = C₂)
    (hcol : ∀ x, Y₂.color x = cast hC (Y₁.color x)) :
    ReturnsAtStruct α Y₂ ↔ ReturnsAtStruct α Y₁ := by
  subst hC
  obtain rfl : Y₂ = Y₁ := eq_of_color_cast hcol
  exact Iff.rfl

theorem designOutcomeOf_cast (hC : C₁ = C₂)
    (hcol : ∀ x, Y₂.color x = cast hC (Y₁.color x)) :
    designOutcomeOf α Y₂ = designOutcomeOf α Y₁ := by
  subst hC
  obtain rfl : Y₂ = Y₁ := eq_of_color_cast hcol
  rfl

end Cast

end KAryPartStruct

/-! ### 9. Theorem 8.1.2 as a reduction at a multiplicative cost -/

section Reduction

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {k : ℕ} {α : ℝ}

/-! #### The admissible inputs of Theorem 8.1.2

Theorem 8.1.2 (version 2.5, line 3694) reads *"Let `1/2 ≤ α < 1` be a threshold
parameter.  Let `X = (Ω, R)` be a `k`-ary relational structure with `n = |Ω|` vertices,
`2 ≤ k ≤ n/2`, and symmetry defect `≥ 1 − α`."*  Its admissible inputs are therefore the
`k`-ary relational structures with `2 ≤ k`, `2k ≤ n` and symmetry defect `≥ 1 − α`, and
that is the category `Babai.DesignInputs` below.

The category `Babai.KAryInputs` (`Workspace/SplitOrJohnson/Main.lean`) is the admissible
inputs of **Theorem 9.2.3**, which asks for more (`2 ≤ k`, `4k ≤ n`, symmetry defect
`> 1 − α`).  It is a full subcategory of `Babai.DesignInputs`
(`Babai.kAryToDesignInputs`), and the reduction stated for `Babai.KAryInputs`, which is
what §9.2 uses, is recovered from the one on `Babai.DesignInputs` through that inclusion
(`Babai.designLemma_finds`). -/

/-- §8.1.  The admissible inputs of **Theorem 8.1.2** for the arity `k` and the threshold
parameter `α`: a `k`-ary relational structure with `n` vertices, *"`2 ≤ k ≤ n/2`, and
symmetry defect `≥ 1 − α`"*.

The defect is written with `Babai.structDefect`, the relative symmetry defect of a
relational structure (Def. 2.3.13/2.3.16); it is the same number as the `Babai.defect` of
the automorphism group of the `k`-ary relational structure of §5.1.2, by
`Babai.RelStructure.defect_toKAry`. -/
def DesignInputs (Ω : Type) [Fintype Ω] [DecidableEq Ω] (k : ℕ) (α : ℝ) : Cat.{0, 0} Ω :=
  (KAryStructures Ω k).full fun s X =>
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    2 ≤ k ∧ 2 * k ≤ s.ncard ∧ 1 - α ≤ (structDefect X.1 : ℝ)

namespace DesignInputs

/-- Theorem 8.1.2: *"`2 ≤ k`"*. -/
theorem two_le (X : Pt (DesignInputs Ω k α)) : 2 ≤ k := X.obj.2.1

/-- Theorem 8.1.2: *"`k ≤ n/2`"*. -/
theorem two_mul_le_card (X : Pt (DesignInputs Ω k α)) (inst : Fintype ↥X.car) :
    2 * k ≤ @Fintype.card ↥X.car inst := by
  have h := X.obj.2.2.1
  have hc : @Fintype.card ↥X.car inst = X.car.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  omega

/-- Theorem 8.1.2: *"symmetry defect `≥ 1 − α`"*, read through the bridge
`Babai.RelStructure.toKAry`, which does not change the automorphism group. -/
theorem defect_ge (X : Pt (DesignInputs Ω k α)) :
    (1 : ℝ) - α ≤ ((@defect _ (Fintype.ofFinite _) (Classical.decEq _)
      (X.obj.1.1.toKAry X.obj.1.2).Aut : ℚ) : ℝ) := by
  have h : (1 : ℝ) - α ≤
      ((@structDefect _ _ _ (Fintype.ofFinite _) (Classical.decEq _) X.obj.1.1 : ℚ) : ℝ) :=
    X.obj.2.2.2
  rw [@RelStructure.defect_toKAry _ _ (Fintype.ofFinite _) (Classical.decEq _)]
  exact h

end DesignInputs

/-- The inputs of Theorem 9.2.3 are inputs of Theorem 8.1.2: *"Theorem 8.1.2 asks for
`1/2 ≤ α < 1`, `2 ≤ k ≤ n/2` and symmetry defect `≥ 1 − α`; Theorem 9.2.3 gives
`3/4 ≤ α < 1`, `2 ≤ k ≤ n/4` and symmetry defect `> 1 − α`, which is more."*  Both
categories are full subcategories of `Babai.KAryStructures Ω k`, so the inclusion is the
identity on objects and on morphisms; it is `Babai.FindsAtMultCost.reindex` that carries a
reduction back along it. -/
def kAryToDesignInputs {s : Set Ω} (X : (KAryInputs Ω k α).Obj s) :
    (DesignInputs Ω k α).Obj s :=
  ⟨X.1, X.2.1, by
    have := X.2.2.1
    have hk := X.2.1
    omega, le_of_lt X.2.2.2⟩

/-- The input of Theorem 8.1.2 read as a `k`-ary relational structure in the sense of
§5.1.2 (`Babai.RelStructure.toKAry`). -/
def karyOf (X : Pt (DesignInputs Ω k α)) : KAryRelStruct ↥X.car ℕ k :=
  X.obj.1.1.toKAry X.obj.1.2

/-- The restriction `X_x⃗` of `kWL(X)` at the string `x⃗` (§8.2, lines 01 and 03). -/
noncomputable def designRestr (X : Pt (DesignInputs Ω k α)) {l : ℕ} (hl : l ≤ k)
    (x : Str ↥X.car l) :=
  letI : Fintype ↥X.car := Fintype.ofFinite _
  (karyOf X).kWL.restrTo hl x

/-- Lines 04–08 of Procedure "Design Lemma": the procedure returns at the string `x⃗`. -/
def DesignReturns (X : Pt (DesignInputs Ω k α)) {l : ℕ} (hl : l ≤ k)
    (x : Str ↥X.car l) : Prop :=
  letI : Fintype ↥X.car := Fintype.ofFinite _
  letI : DecidableEq ↥X.car := Classical.decEq _
  KAryPartStruct.ReturnsAtStruct α (designRestr X hl x)

/-- The outcome of Theorem 8.1.2 at the string `x⃗`. -/
noncomputable def designOutcome (X : Pt (DesignInputs Ω k α)) {l : ℕ} (hl : l ≤ k)
    (x : Str ↥X.car l) : (Cat.sub (DesignOutcomes Ω)).Obj X.car :=
  letI : Fintype ↥X.car := Fintype.ofFinite _
  letI : DecidableEq ↥X.car := Classical.decEq _
  KAryPartStruct.designOutcomeOf α (designRestr X hl x)

/-- Theorem 8.1.2, §8.1: the family of outcomes attached to the input `X`, one for each
string of at most `k − 1` distinct vertices at which Procedure "Design Lemma" returns. -/
def designOut (X : Pt (DesignInputs Ω k α)) :
    Set ((Cat.sub (DesignOutcomes Ω)).Obj X.car) :=
  {Z | ∃ (l : ℕ) (hl : l < k) (x : Str ↥X.car l), Str.Distinct x ∧
    DesignReturns X hl.le x ∧ Z = designOutcome X hl.le x}

theorem four_le_card (X : Pt (DesignInputs Ω k α)) (inst : Fintype ↥X.car) :
    4 ≤ @Fintype.card ↥X.car inst := by
  have h1 := DesignInputs.two_le X
  have h2 := DesignInputs.two_mul_le_card X inst
  omega

/-- Theorem 8.1.5 (§8.2, lines 02–08): the procedure returns at some string of at most
`k − 1` distinct vertices, so the family of outcomes is not empty. -/
theorem designOut_nonempty (hα : 1 / 2 ≤ α) (hα1 : α < 1)
    (X : Pt (DesignInputs Ω k α)) : (designOut X).Nonempty := by
  letI : Fintype ↥X.car := Fintype.ofFinite _
  letI : DecidableEq ↥X.car := Classical.decEq _
  obtain ⟨l, hl, x, hx⟩ := KAryRelStruct.theorem_8_1_5 hα hα1 (karyOf X)
    (DesignInputs.two_le X) (DesignInputs.two_mul_le_card X _) (DesignInputs.defect_ge X)
  have hk2 := DesignInputs.two_le X
  have hlk : l < k := by omega
  refine ⟨designOutcome X hlk.le x, l, hlk, x, hx.1, ?_, rfl⟩
  show KAryPartStruct.ReturnsAtStruct α ((karyOf X).kWL.restrTo hlk.le x)
  rcases hx.2 with h | ⟨h2, hdom, hclq⟩
  · exact Or.inl h
  · exact Or.inr ⟨by omega, hdom, hclq⟩

/-- Theorem 8.1.2: every member of the family is one of the outcomes (a), (b), (c). -/
theorem designOut_good (hα : 1 / 2 ≤ α) (X : Pt (DesignInputs Ω k α)) :
    ∀ Z ∈ designOut X, IsDesignOutcome α X.car ⟨Z.1.1, Z.2⟩ := by
  letI : Fintype ↥X.car := Fintype.ofFinite _
  letI : DecidableEq ↥X.car := Classical.decEq _
  rintro Z ⟨l, hl, x, -, hret, rfl⟩
  have hcoh : ((karyOf X).kWL.restrTo hl.le x).IsCoherent :=
    (karyOf X).kWL.restrTo_isCoherent (karyOf X).kWL_isCoherent _ x
  exact KAryPartStruct.isDesignOutcome_designOutcomeOf hα _ hcoh (four_le_card X _) hret

/-- The multiplicative cost of Theorem 8.1.2: the family of outcomes has at most one
member per string of at most `k − 1` distinct vertices, and there are at most `n^k` of
those (`Babai.card_shortDistinctStrings_le`). -/
theorem designOut_ncard_le (X : Pt (DesignInputs Ω k α)) :
    (designOut X).ncard ≤ X.car.ncard ^ k := by
  classical
  letI : Fintype ↥X.car := Fintype.ofFinite _
  letI : DecidableEq ↥X.car := Classical.decEq _
  set g : ShortDistinctStrings ↥X.car k → (Cat.sub (DesignOutcomes Ω)).Obj X.car :=
    fun p => designOutcome X (le_of_lt p.1.isLt) p.2.1 with hg
  have hsub : designOut X ⊆ Set.range g := by
    rintro Z ⟨l, hl, x, hdist, -, rfl⟩
    exact ⟨⟨⟨l, hl⟩, ⟨x, hdist⟩⟩, rfl⟩
  have hcard : Fintype.card ↥X.car = X.car.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have h2 : 2 ≤ Fintype.card ↥X.car := by
    have := four_le_card X inferInstance
    omega
  calc (designOut X).ncard
      ≤ (Set.range g).ncard := Set.ncard_le_ncard hsub (Set.finite_range _)
    _ = (g '' Set.univ).ncard := by rw [Set.image_univ]
    _ ≤ (Set.univ : Set (ShortDistinctStrings ↥X.car k)).ncard :=
        Set.ncard_image_le (Set.finite_univ)
    _ = Fintype.card (ShortDistinctStrings ↥X.car k) := by
        rw [Set.ncard_univ, Nat.card_eq_fintype_card]
    _ ≤ Fintype.card ↥X.car ^ k := card_shortDistinctStrings_le _ h2
    _ = X.car.ncard ^ k := by rw [hcard]

/-- *"Canonicity in the above statements is relative to `x⃗`"* (§8.1), in the form
Definition 6.0.1 (ii) asks for: an isomorphism `f : X → Y` carries the outcome at `x⃗` to
the outcome at `x⃗^f`. -/
theorem designOut_equiv {X Y : Pt (DesignInputs Ω k α)} {f : ↥X.car ≃ ↥Y.car}
    (hf : f ∈ (DesignInputs Ω k α).IsoP X Y) :
    ∀ Z ∈ designOut X, ∃ Z' ∈ designOut Y,
      f ∈ (Cat.sub (DesignOutcomes Ω)).Iso Z Z' := by
  classical
  letI : Fintype ↥X.car := Fintype.ofFinite _
  letI : DecidableEq ↥X.car := Classical.decEq _
  letI : Fintype ↥Y.car := Fintype.ofFinite _
  letI : DecidableEq ↥Y.car := Classical.decEq _
  have hiso : f ∈ KAryRelStruct.Iso (karyOf X) (karyOf Y) :=
    RelStructure.toKAry_iso X.obj.1.2 Y.obj.1.2 hf
  rintro Z ⟨l, hl, x, hdist, hret, rfl⟩
  have hN : Fintype.card (Str ↥X.car k × Str ↥X.car k)
      = Fintype.card (Str ↥Y.car k × Str ↥Y.car k) :=
    KAryPartStruct.card_str_prod_eq f
  have hstep1 : f ∈ KAryPartStruct.Iso ((karyOf X).kWL.restrTo hl.le x)
      (((karyOf Y).F1.F2.wlIter (Fintype.card (Str ↥X.car k × Str ↥X.car k))).restrTo
        hl.le (tupleMap f x)) :=
    KAryRelStruct.kWL_iso_restrTo (karyOf X) (karyOf Y) hiso hl.le x
  have hcol := fun y =>
    KAryRelStruct.kWL_restrTo_color_cast (Ω := ↥X.car) (karyOf Y) hN hl.le
      (tupleMap f x) y
  have hcast := KAryPartStruct.designOutcomeOf_cast (α := α) _ hcol
  have hrcast := KAryPartStruct.returnsAtStruct_cast (α := α) _ hcol
  refine ⟨designOutcome Y hl.le (tupleMap f x), ⟨l, hl, tupleMap f x, ?_, ?_, rfl⟩, ?_⟩
  · exact fun i j h => hdist (f.injective h)
  · show KAryPartStruct.ReturnsAtStruct α
      ((karyOf Y).kWL.restrTo hl.le (tupleMap f x))
    rw [hrcast]
    exact (KAryPartStruct.returnsAtStruct_congr α hstep1).1 hret
  · show f ∈ (Cat.sub (DesignOutcomes Ω)).Iso
      (KAryPartStruct.designOutcomeOf α ((karyOf X).kWL.restrTo hl.le x))
      (KAryPartStruct.designOutcomeOf α
        ((karyOf Y).kWL.restrTo hl.le (tupleMap f x)))
    rw [hcast]
    exact KAryPartStruct.designOutcomeOf_canonical α hstep1

theorem designOut_finite (X : Pt (DesignInputs Ω k α)) : (designOut X).Finite := by
  classical
  letI : Fintype ↥X.car := Fintype.ofFinite _
  letI : DecidableEq ↥X.car := Classical.decEq _
  refine Set.Finite.subset (Set.finite_range (fun p : ShortDistinctStrings ↥X.car k =>
    designOutcome X (le_of_lt p.1.isLt) p.2.1)) ?_
  rintro Z ⟨l, hl, x, hdist, -, rfl⟩
  exact ⟨⟨⟨l, hl⟩, ⟨x, hdist⟩⟩, rfl⟩

/-- **Theorem 8.1.2 (Design Lemma) as a reduction at a multiplicative cost**, §8.1 read
through §6.

*"Let `1/2 ≤ α < 1` be a threshold parameter.  Let `X = (Ω, R)` be a `k`-ary relational
structure with `n = |Ω|` vertices, `2 ≤ k ≤ n/2`, and symmetry defect `≥ 1 − α`.  Then in
time `n^{O(k)}` we can find a value `ℓ ≤ k − 1` and a string `x⃗ = x₁ … x_ℓ ∈ Ω^⟨ℓ⟩` of `ℓ`
distinct vertices such that by individualizing each `x_j` we obtain either (a) a canonical
coloring of `Ω` with no dominant color, or (b) a canonical coloring of `Ω` and a
nontrivial canonical equipartition of the dominant color class, or (c) a canonical
coloring of `Ω` and a canonically embedded uniprimitive coherent configuration (UPCC)
whose vertex set is the dominant color class.  Canonicity in the above statements is
relative to `x⃗`."*

The family of "versions" of the input (Def. 6.0.1) is the family of admissible strings
at which Procedure "Design Lemma" returns; the multiplicative cost is their number, at
most `n^k` (`Babai.designOut_ncard_le`).  The outcome at a string is
`Babai.designOutcome`, a function of the input and the string with no choice, and it is
one of (a), (b), (c) (`Babai.designOut_good`).  *"Canonicity relative to `x⃗`"* is
condition (ii) of Definition 6.0.1, `Babai.designOut_equiv`.

The running-time clause *"in time `n^{O(k)}`"* is a separate, pending matter; see
the corrected paper. -/
theorem designLemma_finds_designInputs (hα : 1 / 2 ≤ α) (hα1 : α < 1) :
    FindsAtMultCost (DesignInputs Ω k α) (DesignOutcomes Ω) (fun X => X.car.ncard ^ k)
      (fun X Z => IsDesignOutcome α X.car Z) :=
  FindsAtMultCost.of_outcomes_sub designOut (designOut_nonempty hα hα1) designOut_finite
    designOut_ncard_le (fun hf => designOut_equiv hf) (fun X => designOut_good hα X)

/-- **Theorem 8.1.2 (Design Lemma) as a reduction at a multiplicative cost**, on the
admissible inputs of **Theorem 9.2.3**.

This is `Babai.designLemma_finds_designInputs` restricted along the inclusion
`Babai.kAryToDesignInputs` of the inputs of Theorem 9.2.3 into those of Theorem 8.1.2.
Both are full subcategories of `Babai.KAryStructures Ω k`, so the inclusion is the
identity on underlying sets and on morphisms, and neither the cost `n^k` nor the outcome
property changes. -/
theorem designLemma_finds (hα : 1 / 2 ≤ α) (hα1 : α < 1) :
    FindsAtMultCost (KAryInputs Ω k α) (DesignOutcomes Ω) (fun X => X.car.ncard ^ k)
      (fun X Z => IsDesignOutcome α X.car Z) :=
  FindsAtMultCost.reindex (C := KAryInputs Ω k α) (D := DesignInputs Ω k α)
    (fun {_} X => kAryToDesignInputs X) (fun _ _ _ hf => hf)
    (designLemma_finds_designInputs hα hα1)

end Reduction

end Babai
