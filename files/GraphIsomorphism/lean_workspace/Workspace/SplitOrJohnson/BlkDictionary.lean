/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sections 9.4-9.8: the dictionary between the `ℕ`-coloring of an input of the recursion and
the coherent configuration of the field `coherent` of the `Case`, and the Claim on
Procedure Reduce-by-UPCC (§9.8) read through it.
-/
import Workspace.SplitOrJohnson.Imprimitive

/-!
# §9.4-§9.8  The dictionary of the `Case`, and the Claim of §9.8 on an abstract vertex set

The inputs of the recursion of §9.4-§9.8 carry an `ℕ`-valued coloring `c` of a vertex set
split into two parts `V₁`, `V₂`, and the `Case` heading asserts (field `coherent` of
`Babai.IsBipartiteCase`) that `c` is the coloring of a coherent configuration in which the
two parts are the two vertex-color classes.  The results of §3.1-§3.4 are stated for a
`Babai.PartitionStructure` with its own `Fin`-indexed colors, so using them on an input
means translating back and forth.  This file does that translation once and for all, for
an arbitrary `Case` extending `Babai.IsBipartiteCase`:

* `Babai.BipCaseData` is the field `coherent` unpacked, and `Babai.IsBipartiteCase.data`
  picks one such unpacking;
* `Babai.BipCaseData.color_eq_iff`, `.mem_part₁_iff`, `.mem_part₂_iff`,
  `.notMem_part₂_of_mem_part₁` read the two parts and the kernel of the coloring;
* `Babai.BipCaseData.tail_mem_part₁_iff`, `.head_mem_part₁_iff` are Observation 3.3.4: the
  color of an edge determines in which part its tail, resp. its head, lies;
* `Babai.BipCaseData.ncard_nbhd_eq` is Observation 3.3.5: two vertices of the same part
  have the same number of neighbors in each color;
* `Babai.PartitionStructure.isPrimitive_equiv_congr`,
  `.isUniprimitive_equiv_congr`, `.isUniprimitive_of_natColor_map` transport Def. 3.2.1
  along a bijection of vertex sets that matches the colorings, and
  `Babai.BipCaseData.induced_isPrimitive₁`, `.induced_isUniprimitive₁` (and the `₂`
  versions) apply this to the configurations *"`X₁`"*, *"`X₂`"* of the `Case`, which live
  on the parts, giving the primitivity of the induced subconfiguration `X[Vᵢ]` that §3.4
  asks for.

The last section is the Claim of §9.8 in this language: `Babai.upcc_local_twins` is
`Babai.claim_9_8` for an input of the UPCC case.
-/

namespace Babai

/-! ### Transport of connectivity and of uniprimitivity along a bijection

Definitions 2.4.21 and 3.2.1 read the same on two vertex sets identified by a bijection
that matches the colorings; the paper uses this silently when it calls the configuration
induced on the second vertex class "`X₂`". -/

namespace PartitionStructure

variable {α β : Type*}

/-- Definition 3.1.1.  The rank is invariant under a bijection of vertex sets matching the
color classes. -/
theorem rank_equiv_congr {Y : PartitionStructure α} {Y' : PartitionStructure β} (e : α ≃ β)
    (hker : ∀ x y u v : α,
      Y.color x y = Y.color u v ↔ Y'.color (e x) (e y) = Y'.color (e u) (e v)) :
    Y.rank = Y'.rank := by
  classical
  have hbij : Function.Bijective
      (fun i : Fin Y.rank => Y'.color (e (Y.colorWitness i).1) (e (Y.colorWitness i).2)) := by
    constructor
    · intro i j hij
      have h := (hker (Y.colorWitness i).1 (Y.colorWitness i).2
        (Y.colorWitness j).1 (Y.colorWitness j).2).2 hij
      rwa [Y.color_colorWitness, Y.color_colorWitness] at h
    · intro i'
      set p := Y'.colorWitness i' with hp
      set i := Y.color (e.symm p.1) (e.symm p.2) with hi
      refine ⟨i, ?_⟩
      have h : Y.color (Y.colorWitness i).1 (Y.colorWitness i).2
          = Y.color (e.symm p.1) (e.symm p.2) := by rw [Y.color_colorWitness]
      have h' := (hker _ _ _ _).1 h
      show Y'.color (e (Y.colorWitness i).1) (e (Y.colorWitness i).2) = i'
      rw [h', Equiv.apply_symm_apply, Equiv.apply_symm_apply, hp, Y'.color_colorWitness]
  have h := Fintype.card_of_bijective hbij
  simpa using h

/-- Definition 3.2.1.  Primitivity transports along a bijection of vertex sets matching the
color classes. -/
theorem isPrimitive_equiv_congr {Y : PartitionStructure α} {Y' : PartitionStructure β}
    (e : α ≃ β)
    (hker : ∀ x y u v : α,
      Y.color x y = Y.color u v ↔ Y'.color (e x) (e y) = Y'.color (e u) (e v))
    (h : Y.IsPrimitive) : Y'.IsPrimitive := by
  obtain ⟨hhom, hconn⟩ := h
  refine ⟨fun x' y' => ?_, fun i' hoff => ?_⟩
  · have := (hker (e.symm x') (e.symm x') (e.symm y') (e.symm y')).1 (hhom _ _)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact this
  · set p := Y'.colorWitness i' with hp
    set i := Y.color (e.symm p.1) (e.symm p.2) with hi
    -- the color `i` of `Y` named by the color `i'` of `Y'`
    have hcol : ∀ a b : α, Y.color a b = i ↔ Y'.color (e a) (e b) = i' := by
      intro a b
      rw [hi]
      constructor
      · intro hab
        have := (hker a b (e.symm p.1) (e.symm p.2)).1 hab
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hp,
          Y'.color_colorWitness] at this
        exact this
      · intro hab
        refine (hker a b (e.symm p.1) (e.symm p.2)).2 ?_
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hp, Y'.color_colorWitness]
        exact hab
    have hoff' : Y.IsOffDiagonalColor i := by
      rw [IsOffDiagonalColor, Set.eq_empty_iff_forall_notMem]
      rintro ⟨a, b⟩ ⟨hab, hdg⟩
      have hab' : Y.color a b = i := hab
      have hd : a = b := hdg
      have : (e a, e a) ∈ Y'.rel i' ∩ diag β := by
        refine ⟨?_, rfl⟩
        have := (hcol a b).1 hab'
        rw [← hd] at this
        exact this
      rw [hoff] at this
      exact this
    have hadj : ∀ a b : α,
        (Y'.extConstituent i').Adj (e a) (e b) ↔ (Y.extConstituent i).Adj a b := by
      intro a b
      exact (hcol a b).symm
    exact (Digraph.isWeaklyConnected_map e hadj).2 (hconn i hoff')

/-- Definition 3.2.1, Notation 3.2.2.  Uniprimitivity transports along a bijection of
vertex sets matching the color classes. -/
theorem isUniprimitive_equiv_congr {Y : PartitionStructure α} {Y' : PartitionStructure β}
    (e : α ≃ β)
    (hker : ∀ x y u v : α,
      Y.color x y = Y.color u v ↔ Y'.color (e x) (e y) = Y'.color (e u) (e v))
    (h : Y.IsUniprimitive) : Y'.IsUniprimitive :=
  ⟨isPrimitive_equiv_congr e hker h.1, by rw [← rank_equiv_congr e hker]; exact h.2⟩

/-- Definition 3.2.1.  The form of `isUniprimitive_equiv_congr` used in §9.8: the
bijection matches the `ℕ`-valued colorings (Obs. 3.3.4's reading of the colors as
labels). -/
theorem isUniprimitive_of_natColor_map {Y : PartitionStructure α}
    {Y' : PartitionStructure β} (e : α ≃ β)
    (hnat : ∀ x y : α, Y.natColor x y = Y'.natColor (e x) (e y))
    (h : Y.IsUniprimitive) : Y'.IsUniprimitive := by
  refine isUniprimitive_equiv_congr e (fun x y u v => ?_) h
  rw [← Y.natColor_eq_iff, ← Y'.natColor_eq_iff, hnat x y, hnat u v]

end PartitionStructure

/-! ### The dictionary of the `Case`

The field `coherent` of `Babai.IsBipartiteCase` is an existential statement; every use of
it in §9.4-§9.8 unpacks it and then reads the `ℕ`-colors of the input as the `Fin`-colors
of the configuration.  `Babai.BipCaseData` is that unpacking, and the lemmas below are the
readings that §9.6-§9.8 use. -/

/-- §9.4-§9.8.  The field `coherent` of the `Case` unpacked: the coherent configuration
whose coloring is `c`, together with the two vertex colors naming the two parts.  *"both
`V₁` and `V₂` are vertex-color classes in `X`"* (Claim of §9.8). -/
structure BipCaseData {V : Type} (c : V → V → ℕ) (V₁ V₂ : Set V) where
  /-- The coherent configuration `X` of the `Case`. -/
  P : PartitionStructure V
  /-- `X` is coherent. -/
  isCoherent : P.IsCoherent
  /-- Its coloring is the coloring of the input. -/
  natColor_eq : P.natColor = c
  /-- The vertex color of the first part. -/
  i : Fin P.rank
  /-- The vertex color of the second part. -/
  j : Fin P.rank
  /-- The two parts are different vertex-color classes. -/
  color_ne : i ≠ j
  /-- *"`V₁` is a vertex-color class in `X`"*. -/
  part₁_eq : V₁ = P.vertexClass i
  /-- *"`V₂` is a vertex-color class in `X`"*. -/
  part₂_eq : V₂ = P.vertexClass j
  /-- The two parts cover the vertex set. -/
  cover : ∀ x : V, x ∈ V₁ ∨ x ∈ V₂

namespace BipCaseData

variable {V : Type} {c : V → V → ℕ} {V₁ V₂ : Set V} (D : BipCaseData c V₁ V₂)

include D

/-- The `ℕ`-color of a pair is the label of its `Fin`-color. -/
theorem color_val (x y : V) : c x y = (D.P.color x y : ℕ) :=
  (congrFun (congrFun D.natColor_eq x) y).symm

/-- Two pairs have the same `ℕ`-color exactly when they have the same `Fin`-color. -/
theorem color_eq_iff (x y u v : V) :
    c x y = c u v ↔ D.P.color x y = D.P.color u v := by
  rw [D.color_val x y, D.color_val u v]
  exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩

/-- A vertex lies in the first part exactly when its vertex color is `i`. -/
theorem mem_part₁_iff (x : V) : x ∈ V₁ ↔ D.P.vcolor x = D.i :=
  Set.ext_iff.1 D.part₁_eq x

/-- A vertex lies in the second part exactly when its vertex color is `j`. -/
theorem mem_part₂_iff (x : V) : x ∈ V₂ ↔ D.P.vcolor x = D.j :=
  Set.ext_iff.1 D.part₂_eq x

/-- The two parts are disjoint: they are different vertex-color classes. -/
theorem notMem_part₂_of_mem_part₁ {x : V} (hx : x ∈ V₁) : x ∉ V₂ := by
  intro hx₂
  exact D.color_ne (((D.mem_part₁_iff x).1 hx).symm.trans ((D.mem_part₂_iff x).1 hx₂))

/-- The neighborhood of a vertex in an `ℕ`-color, as a constituent neighborhood. -/
theorem setOf_eq_nbr {x y₀ : V} : {y | c x y = c x y₀} = D.P.nbr (D.P.color x y₀) x := by
  ext y
  exact D.color_eq_iff x y x y₀

/-- Observation 3.3.4.  The color of an edge determines in which part its tail lies. -/
theorem tail_mem_part₁_iff {x y u v : V} (h : c x y = c u v) : x ∈ V₁ ↔ u ∈ V₁ := by
  have hc : D.P.color x y = D.P.color u v := (D.color_eq_iff x y u v).1 h
  have h1 : D.P.vcolor x = D.P.tailColor (D.P.color x y) :=
    D.P.vcolor_fst_eq D.isCoherent rfl
  have h2 : D.P.vcolor u = D.P.tailColor (D.P.color u v) :=
    D.P.vcolor_fst_eq D.isCoherent rfl
  rw [D.mem_part₁_iff, D.mem_part₁_iff, h1, h2, hc]

/-- Observation 3.3.4.  The color of an edge determines in which part its head lies. -/
theorem head_mem_part₁_iff {x y u v : V} (h : c x y = c u v) : y ∈ V₁ ↔ v ∈ V₁ := by
  have hc : D.P.color x y = D.P.color u v := (D.color_eq_iff x y u v).1 h
  have h1 : D.P.vcolor y = D.P.headColor (D.P.color x y) :=
    D.P.vcolor_snd_eq D.isCoherent rfl
  have h2 : D.P.vcolor v = D.P.headColor (D.P.color u v) :=
    D.P.vcolor_snd_eq D.isCoherent rfl
  rw [D.mem_part₁_iff, D.mem_part₁_iff, h1, h2, hc]

/-- Observation 3.3.4, for the second part. -/
theorem tail_mem_part₂_iff {x y u v : V} (h : c x y = c u v) : x ∈ V₂ ↔ u ∈ V₂ := by
  have hc : D.P.color x y = D.P.color u v := (D.color_eq_iff x y u v).1 h
  have h1 : D.P.vcolor x = D.P.tailColor (D.P.color x y) :=
    D.P.vcolor_fst_eq D.isCoherent rfl
  have h2 : D.P.vcolor u = D.P.tailColor (D.P.color u v) :=
    D.P.vcolor_fst_eq D.isCoherent rfl
  rw [D.mem_part₂_iff, D.mem_part₂_iff, h1, h2, hc]

/-- Observation 3.3.4, for the second part. -/
theorem head_mem_part₂_iff {x y u v : V} (h : c x y = c u v) : y ∈ V₂ ↔ v ∈ V₂ := by
  have hc : D.P.color x y = D.P.color u v := (D.color_eq_iff x y u v).1 h
  have h1 : D.P.vcolor y = D.P.headColor (D.P.color x y) :=
    D.P.vcolor_snd_eq D.isCoherent rfl
  have h2 : D.P.vcolor v = D.P.headColor (D.P.color u v) :=
    D.P.vcolor_snd_eq D.isCoherent rfl
  rw [D.mem_part₂_iff, D.mem_part₂_iff, h1, h2, hc]

/-- Observation 3.3.5.  Two vertices of the same part have the same number of neighbors in
each color: the out-degree `deg⁺_k(x)` depends only on the vertex color of `x`. -/
theorem ncard_nbhd_eq [Finite V] {x u : V} (hxu : D.P.vcolor x = D.P.vcolor u) (k : ℕ) :
    {y | c x y = k}.ncard = {y | c u y = k}.ncard := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hset : ∀ w : V, {y | c w y = k} = {y | D.P.natColor w y = k} := by
    intro w; ext y; simp only [Set.mem_setOf_eq, D.color_val w y]; exact Iff.rfl
  rw [hset x, hset u]
  by_cases hk : k < D.P.rank
  · rw [D.P.setOf_natColor_eq_nbr hk, D.P.setOf_natColor_eq_nbr hk,
      ← PartitionStructure.outDegC_eq_ncard, ← PartitionStructure.outDegC_eq_ncard]
    exact D.P.outDegC_eq_of_vcolor_eq D.isCoherent _ hxu
  · rw [D.P.setOf_natColor_eq_empty hk, D.P.setOf_natColor_eq_empty hk]

/-- Definition 3.2.1.  *"`X₁` is a UPCC"*, stated in the `Case` for a configuration on the
first part, gives the primitivity of the induced subconfiguration `X[V₁]` that §3.4 uses
(Theorem 3.4.11, Theorem 3.4.19). -/
theorem induced_isPrimitive₁ [Fintype V] [Fintype ↥(D.P.vertexClass D.i)]
    {Q : PartitionStructure ↥V₁} (hQ : Q.IsPrimitive)
    (hnat : ∀ x y x' y' : ↥V₁,
      Q.natColor x y = Q.natColor x' y' ↔ c (x : V) (y : V) = c (x' : V) (y' : V)) :
    (D.P.induced (D.P.vertexClass D.i)).IsPrimitive := by
  refine PartitionStructure.isPrimitive_equiv_congr (Equiv.setCongr D.part₁_eq)
    (fun x y u v => ?_) hQ
  have hcoe : ∀ w : ↥V₁,
      ((Equiv.setCongr D.part₁_eq w : ↥(D.P.vertexClass D.i)) : V) = (w : V) := fun _ => rfl
  rw [D.P.induced_color_eq_iff, hcoe, hcoe, hcoe, hcoe, ← D.color_eq_iff,
    ← Q.natColor_eq_iff]
  exact hnat x y u v

/-- Definition 3.2.1, Notation 3.2.2, for the first part. -/
theorem induced_isUniprimitive₁ [Fintype V] [Fintype ↥(D.P.vertexClass D.i)]
    {Q : PartitionStructure ↥V₁} (hQ : Q.IsUniprimitive)
    (hnat : ∀ x y x' y' : ↥V₁,
      Q.natColor x y = Q.natColor x' y' ↔ c (x : V) (y : V) = c (x' : V) (y' : V)) :
    (D.P.induced (D.P.vertexClass D.i)).IsUniprimitive := by
  refine PartitionStructure.isUniprimitive_equiv_congr (Equiv.setCongr D.part₁_eq)
    (fun x y u v => ?_) hQ
  have hcoe : ∀ w : ↥V₁,
      ((Equiv.setCongr D.part₁_eq w : ↥(D.P.vertexClass D.i)) : V) = (w : V) := fun _ => rfl
  rw [D.P.induced_color_eq_iff, hcoe, hcoe, hcoe, hcoe, ← D.color_eq_iff,
    ← Q.natColor_eq_iff]
  exact hnat x y u v

/-- Definition 3.2.1, for the second part: *"`X₂` is a UPCC"* (§9.8). -/
theorem induced_isPrimitive₂ [Fintype V] [Fintype ↥(D.P.vertexClass D.j)]
    {Q : PartitionStructure ↥V₂} (hQ : Q.IsPrimitive)
    (hnat : ∀ x y x' y' : ↥V₂,
      Q.natColor x y = Q.natColor x' y' ↔ c (x : V) (y : V) = c (x' : V) (y' : V)) :
    (D.P.induced (D.P.vertexClass D.j)).IsPrimitive := by
  refine PartitionStructure.isPrimitive_equiv_congr (Equiv.setCongr D.part₂_eq)
    (fun x y u v => ?_) hQ
  have hcoe : ∀ w : ↥V₂,
      ((Equiv.setCongr D.part₂_eq w : ↥(D.P.vertexClass D.j)) : V) = (w : V) := fun _ => rfl
  rw [D.P.induced_color_eq_iff, hcoe, hcoe, hcoe, hcoe, ← D.color_eq_iff,
    ← Q.natColor_eq_iff]
  exact hnat x y u v

/-- Definition 3.2.1, Notation 3.2.2, for the second part. -/
theorem induced_isUniprimitive₂ [Fintype V] [Fintype ↥(D.P.vertexClass D.j)]
    {Q : PartitionStructure ↥V₂} (hQ : Q.IsUniprimitive)
    (hnat : ∀ x y x' y' : ↥V₂,
      Q.natColor x y = Q.natColor x' y' ↔ c (x : V) (y : V) = c (x' : V) (y' : V)) :
    (D.P.induced (D.P.vertexClass D.j)).IsUniprimitive := by
  refine PartitionStructure.isUniprimitive_equiv_congr (Equiv.setCongr D.part₂_eq)
    (fun x y u v => ?_) hQ
  have hcoe : ∀ w : ↥V₂,
      ((Equiv.setCongr D.part₂_eq w : ↥(D.P.vertexClass D.j)) : V) = (w : V) := fun _ => rfl
  rw [D.P.induced_color_eq_iff, hcoe, hcoe, hcoe, hcoe, ← D.color_eq_iff,
    ← Q.natColor_eq_iff]
  exact hnat x y u v

end BipCaseData

/-- §9.4-§9.8.  An unpacking of the field `coherent` of the `Case`. -/
noncomputable def IsBipartiteCase.data {V : Type} {c : V → V → ℕ} {V₁ V₂ : Set V}
    (h : IsBipartiteCase c V₁ V₂) : BipCaseData c V₁ V₂ :=
  let P := h.coherent.choose
  let hP := h.coherent.choose_spec
  { P := P
    isCoherent := hP.1
    natColor_eq := hP.2.1
    i := hP.2.2.choose
    j := hP.2.2.choose_spec.choose
    color_ne := hP.2.2.choose_spec.choose_spec.1
    part₁_eq := hP.2.2.choose_spec.choose_spec.2.1
    part₂_eq := hP.2.2.choose_spec.choose_spec.2.2.1
    cover := hP.2.2.choose_spec.choose_spec.2.2.2 }

/-! ### The Claim of §9.8, read on an `ℕ`-colored input

Version 2.5, lines 4337-4345.  `Babai.claim_9_8` is the Claim for the `Fin`-colored
configuration; `Babai.upcc_local_twins` below is the same statement for an input of the
UPCC case, whose colors are natural numbers.  The individualized vertex `x ∈ V₂` of
step 1 of Procedure Reduce-by-UPCC is `b₀` here, `m` is the dominant color of the link and
`ℓ` the first non-dominant off-diagonal color of `X₂`. -/

open scoped Classical in
/-- Claim of §9.8 (version 2.5, lines 4337-4345), for an input of the UPCC case whose
coloring takes values in `ℕ`.  *"Summarizing, `Y` is a nontrivial semiregular bipartite
graph; therefore its symmetry defect is `≥ 1/2` (Prop. 2.4.30)"*, read on the part
`R_m⁻(b₀)` of the local constituent `Y = X_m[R_m⁻(b₀), R_ℓ(b₀)]`: a set `T` of points of
`R_m⁻(b₀)` whose members have the same `m`-neighborhood inside `R_ℓ(b₀)` — a set of twins
of `Y` — has at most `|R_m⁻(b₀)|/2` points.

This is `Babai.claim_9_8` for the configuration of the field `coherent` of the `Case`; the
hypotheses are its hypotheses, read through `Babai.BipCaseData`:

* `hm` is *"`m` is `α`-dominant and therefore dominant"*, read at `b₀`: it is `hhalf`,
  `n₁/2 < |R_m⁻(b₀)|`;
* `hl₁` and `hl₂` are *"`ℓ` is the first non-dominant off-diagonal color in `X₂`"*: the
  color occurs at `b₀` toward another vertex of `V₂` (which gives `hlne` and the
  off-diagonality of `ℓ`) and covers at most half of `V₂` (which gives `hlnd`, by
  `Babai.PartitionStructure.ncard_rel_eq`);
* `hlt`, `|R_m⁻(b₀)| < n₁`, *"is equivalent to the nontriviality of the link `X₁₂`"*: if
  every point of `V₁` had color `m` from `b₀` then, the in-degree of `m` being the same at
  every vertex of `V₂` (Obs. 3.3.5), every pair of `V₂ × V₁` — hence every pair of
  `V₁ × V₂` — would have one and the same color;
* `hupcc₂` is *"`X₂` is a UPCC"*, and gives `huni` by
  `Babai.BipCaseData.induced_isUniprimitive₂`. -/
theorem upcc_local_twins {V : Type} [Finite V] {c : V → V → ℕ} {V₁ V₂ : Set V}
    (hbip : IsBipartiteCase c V₁ V₂)
    (hupcc₂ : ∃ Q : PartitionStructure ↥V₂, Q.IsCoherent ∧ Q.IsUniprimitive ∧
      ∀ x y x' y' : ↥V₂,
        Q.natColor x y = Q.natColor x' y' ↔ c (x : V) (y : V) = c (x' : V) (y' : V))
    {b₀ : V} (hb₀ : b₀ ∈ V₂) {m l : ℕ}
    (hm : V₁.ncard < 2 * {x | x ∈ V₁ ∧ c b₀ x = m}.ncard)
    (hl₁ : ∃ b ∈ V₂, b ≠ b₀ ∧ c b₀ b = l)
    (hl₂ : 2 * {b | b ∈ V₂ ∧ c b₀ b = l}.ncard ≤ V₂.ncard)
    {T : Set V} (hT : T ⊆ {x | x ∈ V₁ ∧ c b₀ x = m})
    (htwin : ∀ x ∈ T, ∀ y ∈ T, ∀ b, b ∈ V₂ → c b₀ b = l → (c b x = m ↔ c b y = m)) :
    2 * T.ncard ≤ {x | x ∈ V₁ ∧ c b₀ x = m}.ncard := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have D : BipCaseData c V₁ V₂ := hbip.data
  obtain ⟨b', hb'₂, hb'ne, hb'l⟩ := hl₁
  -- `R_m⁻(b₀)` is nonempty: it covers more than half of `V₁`
  have hSne : {x | x ∈ V₁ ∧ c b₀ x = m}.Nonempty := by
    rcases Set.eq_empty_or_nonempty {x | x ∈ V₁ ∧ c b₀ x = m} with he | h
    · rw [he, Set.ncard_empty] at hm; omega
    · exact h
  obtain ⟨x₀, hx₀₁, hx₀m⟩ := hSne
  have hb₀j : D.P.vcolor b₀ = D.j := (D.mem_part₂_iff b₀).1 hb₀
  have hb'j : D.P.vcolor b' = D.j := (D.mem_part₂_iff b').1 hb'₂
  have hx₀i : D.P.vcolor x₀ = D.i := (D.mem_part₁_iff x₀).1 hx₀₁
  set M : Fin D.P.rank := D.P.color b₀ x₀ with hMdef
  set L : Fin D.P.rank := D.P.color b₀ b' with hLdef
  have hMval : (M : ℕ) = m := by rw [hMdef, ← D.color_val b₀ x₀]; exact hx₀m
  have hLval : (L : ℕ) = l := by rw [hLdef, ← D.color_val b₀ b']; exact hb'l
  have hmemM : ∀ y : V, D.P.color b₀ y = M ↔ c b₀ y = m := by
    intro y
    rw [D.color_val b₀ y, ← hMval]
    exact ⟨fun h => by rw [h], fun h => Fin.ext h⟩
  have hmemL : ∀ y : V, D.P.color b₀ y = L ↔ c b₀ y = l := by
    intro y
    rw [D.color_val b₀ y, ← hLval]
    exact ⟨fun h => by rw [h], fun h => Fin.ext h⟩
  -- the two constituent neighborhoods of `b₀`
  have hnbrM : D.P.nbr M b₀ = {x | x ∈ V₁ ∧ c b₀ x = m} := by
    ext v
    rw [PartitionStructure.mem_nbr, hmemM v]
    refine ⟨fun hv => ⟨?_, hv⟩, fun h => h.2⟩
    exact (D.head_mem_part₁_iff (show c b₀ v = c b₀ x₀ by rw [hv, hx₀m])).2 hx₀₁
  have hnbrL : D.P.nbr L b₀ = {b | b ∈ V₂ ∧ c b₀ b = l} := by
    ext v
    rw [PartitionStructure.mem_nbr, hmemL v]
    refine ⟨fun hv => ⟨?_, hv⟩, fun h => h.2⟩
    exact (D.head_mem_part₂_iff (show c b₀ v = c b₀ b' by rw [hv, hb'l])).2 hb'₂
  have hSfull : {y | c b₀ y = m} = {x | x ∈ V₁ ∧ c b₀ x = m} := by
    rw [← hnbrM]; ext y; exact (hmemM y).symm
  -- the hypotheses of Theorem 3.4.19 and of the Claim
  have hidiag : D.P.IsDiagonalColor D.j := by
    rw [← hb₀j]
    exact D.P.isDiagonalColor_vcolor_aux b₀ D.isCoherent.toIsConfiguration
  have hjdiag : D.P.IsDiagonalColor D.i := by
    rw [← hx₀i]
    exact D.P.isDiagonalColor_vcolor_aux x₀ D.isCoherent.toIsConfiguration
  have hlm : L ≠ M := by
    intro hLM
    have hb' : b' ∈ D.P.nbr M b₀ := by rw [← hLM]; exact hLdef.symm
    rw [hnbrM] at hb'
    exact D.notMem_part₂_of_mem_part₁ hb'.1 hb'₂
  have hmoff : D.P.IsOffDiagonalColor M := by
    rw [PartitionStructure.IsOffDiagonalColor, Set.eq_empty_iff_forall_notMem]
    rintro ⟨z, w⟩ ⟨hzw, hdg⟩
    have hzw' : D.P.color z w = M := hzw
    have hd : z = w := hdg
    have hzz : D.P.color z z = M := by nth_rewrite 2 [hd]; exact hzw'
    have hb : b₀ = x₀ := by
      refine D.isCoherent.toIsConfiguration.diag b₀ x₀ z ?_
      rw [hzz, hMdef]
    exact D.notMem_part₂_of_mem_part₁ (hb ▸ hx₀₁) hb₀
  have hloff : D.P.IsOffDiagonalColor L := by
    rw [PartitionStructure.IsOffDiagonalColor, Set.eq_empty_iff_forall_notMem]
    rintro ⟨z, w⟩ ⟨hzw, hdg⟩
    have hzw' : D.P.color z w = L := hzw
    have hd : z = w := hdg
    have hzz : D.P.color z z = L := by nth_rewrite 2 [hd]; exact hzw'
    exact hb'ne (D.isCoherent.toIsConfiguration.diag b₀ b' z (by rw [hzz, hLdef])).symm
  have hx : b₀ ∈ D.P.vertexClass D.j := hb₀j
  have hlx : D.P.nbr L b₀ ⊆ D.P.vertexClass D.j := by
    rw [hnbrL]; rintro v ⟨hv2, -⟩; exact (D.mem_part₂_iff v).1 hv2
  have hmx : D.P.nbr M b₀ ⊆ D.P.vertexClass D.i := by
    rw [hnbrM]; rintro v ⟨hv1, -⟩; exact (D.mem_part₁_iff v).1 hv1
  have hlne : (D.P.nbr L b₀).Nonempty := ⟨b', by rw [hnbrL]; exact ⟨hb'₂, hb'l⟩⟩
  have hVi : (D.P.vertexClass D.i).ncard = V₁.ncard := congrArg Set.ncard D.part₁_eq.symm
  have hVj : (D.P.vertexClass D.j).ncard = V₂.ncard := congrArg Set.ncard D.part₂_eq.symm
  have hhalf : (D.P.vertexClass D.i).ncard < 2 * (D.P.nbr M b₀).ncard := by
    rw [hVi, hnbrM]; exact hm
  -- `|R_m⁻(b₀)| < n₁`: otherwise the link is trivial
  have hlt : (D.P.nbr M b₀).ncard < (D.P.vertexClass D.i).ncard := by
    rw [hnbrM, hVi]
    have hsub : {x | x ∈ V₁ ∧ c b₀ x = m} ⊆ V₁ := fun x hx => hx.1
    rcases lt_or_eq_of_le (Set.ncard_le_ncard hsub (Set.toFinite _)) with h | h
    · exact h
    · exfalso
      have hSeq : {x | x ∈ V₁ ∧ c b₀ x = m} = V₁ :=
        Set.eq_of_subset_of_ncard_le hsub (le_of_eq h.symm) (Set.toFinite _)
      -- every vertex of `V₂` sees all of `V₁` in the color `m`
      have hall : ∀ b ∈ V₂, ∀ x ∈ V₁, c b x = m := by
        intro b hb x hx
        have hdeg : {y | c b y = m}.ncard = {y | c b₀ y = m}.ncard :=
          D.ncard_nbhd_eq (by rw [(D.mem_part₂_iff b).1 hb, hb₀j]) m
        have hbsub : {y | c b y = m} ⊆ V₁ := by
          intro y hy
          exact (D.head_mem_part₁_iff (show c b y = c b₀ x₀ by rw [hy, hx₀m])).2 hx₀₁
        have hcard : V₁.ncard ≤ {y | c b y = m}.ncard := by
          rw [hdeg, hSfull, hSeq]
        have hbfull : {y | c b y = m} = V₁ :=
          Set.eq_of_subset_of_ncard_le hbsub hcard (Set.toFinite _)
        rw [← hbfull] at hx
        exact hx
      obtain ⟨x₁, y₁, x₂, y₂, hne⟩ := hbip.link_nontrivial
      refine hne ?_
      have e1 : c (y₁ : V) (x₁ : V) = m := hall _ y₁.2 _ x₁.2
      have e2 : c (y₂ : V) (x₂ : V) = m := hall _ y₂.2 _ x₂.2
      have f1 : D.P.color (x₁ : V) (y₁ : V) = D.P.conv (D.P.color (y₁ : V) (x₁ : V)) :=
        D.P.color_comm D.isCoherent.toIsConfiguration _ _
      have f2 : D.P.color (x₂ : V) (y₂ : V) = D.P.conv (D.P.color (y₂ : V) (x₂ : V)) :=
        D.P.color_comm D.isCoherent.toIsConfiguration _ _
      rw [D.color_val (x₁ : V) (y₁ : V), D.color_val (x₂ : V) (y₂ : V), f1, f2]
      exact congrArg (fun k : Fin D.P.rank => ((D.P.conv k : Fin D.P.rank) : ℕ))
        ((D.color_eq_iff _ _ _ _).1 (e1.trans e2.symm))
  -- `ℓ` is not dominant in `X₂`
  have htail : D.P.tailColor L = D.j :=
    (D.P.vcolor_fst_eq D.isCoherent hLdef.symm).symm.trans hb₀j
  have hdegL : D.P.outDegOf L = (D.P.nbr L b₀).ncard := by
    rw [← D.P.outDegC_eq_outDegOf D.isCoherent L
      (show b₀ ∈ D.P.vertexClass (D.P.tailColor L) by rw [htail]; exact hb₀j),
      PartitionStructure.outDegC_eq_ncard]
  have hrelL : (D.P.rel L).ncard = V₂.ncard * (D.P.nbr L b₀).ncard := by
    rw [D.P.ncard_rel_eq D.isCoherent L, htail, hVj, hdegL]
  have hlnd : ¬ D.P.IsDominant D.j D.j L := by
    intro hdom
    simp only [PartitionStructure.IsDominant, PartitionStructure.IsAlphaDominant] at hdom
    rw [hVj, hrelL] at hdom
    have h2 : 2 * (D.P.nbr L b₀).ncard ≤ V₂.ncard := by rw [hnbrL]; exact hl₂
    have h2' : 2 * ((D.P.nbr L b₀).ncard : ℝ) ≤ (V₂.ncard : ℝ) := by exact_mod_cast h2
    have hn : (0 : ℝ) ≤ (V₂.ncard : ℝ) := by positivity
    push_cast at hdom
    nlinarith
  -- *"`X₂` is a UPCC"*
  obtain ⟨Q, hQcoh, hQuni, hQnat⟩ := hupcc₂
  have huni : (D.P.induced (D.P.vertexClass D.j)).IsUniprimitive :=
    D.induced_isUniprimitive₂ hQuni hQnat
  obtain ⟨-, -, -, hd₂, -⟩ := claim_9_8 D.P D.isCoherent hidiag hjdiag hlm hloff hmoff
    hlnd hx hlx hmx hlne hhalf hlt huni
  -- Prop. 2.4.30 for the second part of `Y`, read on `T`
  have key : ∀ (iA : DecidableEq ↥(D.P.nbr L b₀)) (iB : DecidableEq ↥(D.P.nbr M b₀))
      (iF : Fintype ↥(D.P.nbr M b₀)),
      (1 : ℚ) / 2 ≤ @BipGraph.defect₂ _ _ iA iB iF (D.P.localConstituentBip M L M b₀) →
      2 * T.ncard ≤ (D.P.nbr M b₀).ncard := by
    intro iA iB iF hdef
    letI := iA
    letI := iB
    letI := iF
    set Y := D.P.localConstituentBip M L M b₀ with hY
    have hEiff : ∀ (a : ↥(D.P.nbr L b₀)) (u : ↥(D.P.nbr M b₀)),
        ((a, u) ∈ Y.E) ↔ c (a : V) (u : V) = m := by
      intro a u
      have hrfl : ((a, u) ∈ Y.E) ↔ D.P.color (a : V) (u : V) = M := Iff.rfl
      rw [hrfl, D.color_val (a : V) (u : V), ← hMval]
      exact ⟨fun h => by rw [h], fun h => Fin.ext h⟩
    have hTsub : T ⊆ D.P.nbr M b₀ := by rw [hnbrM]; exact hT
    set T' : Finset ↥(D.P.nbr M b₀) :=
      {u : ↥(D.P.nbr M b₀) | (u : V) ∈ T}.toFinset with hT'
    have hmemT' : ∀ u : ↥(D.P.nbr M b₀), u ∈ T' ↔ (u : V) ∈ T := by
      intro u; rw [hT', Set.mem_toFinset]; exact Iff.rfl
    have hTcard : T'.card = T.ncard := by
      have himg : Subtype.val '' {u : ↥(D.P.nbr M b₀) | (u : V) ∈ T} = T := by
        ext v
        simp only [Set.mem_image, Set.mem_setOf_eq]
        exact ⟨by rintro ⟨u, hu, rfl⟩; exact hu, fun hv => ⟨⟨v, hTsub hv⟩, hv, rfl⟩⟩
      have h1 : T'.card = {u : ↥(D.P.nbr M b₀) | (u : V) ∈ T}.ncard := by
        rw [hT', ← Set.ncard_coe_finset, Set.coe_toFinset]
      rw [h1, ← Set.ncard_image_of_injective _ Subtype.val_injective, himg]
    have htwinset :
        IsTwinSet Y.Aut ((fun u => Sum.inr u) '' (↑T' : Set ↥(D.P.nbr M b₀))) := by
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ hne
      have huT : (u : V) ∈ T := (hmemT' u).1 hu
      have hvT : (v : V) ∈ T := (hmemT' v).1 hv
      have hne' : u ≠ v := fun h => hne (by rw [h])
      refine (BipGraph.isTwin_inr_iff_aux Y u v hne').2 ?_
      ext a
      simp only [Set.mem_setOf_eq]
      rw [hEiff a u, hEiff a v]
      have ha : (a : V) ∈ {b | b ∈ V₂ ∧ c b₀ b = l} := (Set.ext_iff.1 hnbrL (a : V)).1 a.2
      exact htwin _ huT _ hvT (a : V) ha.1 ha.2
    have hle : T'.card ≤ Y.symmetricity₂ := by
      refine Finset.le_sup (f := Finset.card) ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact htwinset
    have hcardB : Fintype.card ↥(D.P.nbr M b₀) = (D.P.nbr M b₀).ncard := by
      rw [← Nat.card_eq_fintype_card]; rfl
    have hBpos : 0 < Fintype.card ↥(D.P.nbr M b₀) := by
      rw [hcardB]
      exact (Set.ncard_pos (Set.toFinite _)).2 ⟨x₀, by rw [hnbrM]; exact ⟨hx₀₁, hx₀m⟩⟩
    have hsym : 2 * Y.symmetricity₂ ≤ Fintype.card ↥(D.P.nbr M b₀) := by
      have h := hdef
      rw [BipGraph.defect₂, BipGraph.relSymmetricity₂] at h
      have hnQ : (0 : ℚ) < (Fintype.card ↥(D.P.nbr M b₀) : ℚ) := by exact_mod_cast hBpos
      have hle2 : (Y.symmetricity₂ : ℚ) / (Fintype.card ↥(D.P.nbr M b₀) : ℚ) ≤ 1 / 2 := by
        linarith
      rw [div_le_iff₀ hnQ] at hle2
      have hfin : 2 * (Y.symmetricity₂ : ℚ) ≤ (Fintype.card ↥(D.P.nbr M b₀) : ℚ) := by
        linarith
      exact_mod_cast hfin
    omega
  have hfinal := key _ _ _ hd₂
  rw [hnbrM] at hfinal
  exact hfinal


/-! ### The `Case` of the paper builds the `Case` of this file

The paper's `Case` headings of §9.6-§9.8 speak of the configurations `X₁ = X[V₁]` and
`X₂ = X[V₂]` induced by the ambient coherent configuration `X` on its two vertex-color
classes.  The two lemmas below, and `Babai.isBlockDesignCase_induced`,
`Babai.isUPCCCase_induced` in `Workspace/SplitOrJohnson/BlkCases.lean`, build the `Case`
structures from exactly that data.  Together with `Babai.BipCaseData.induced_isPrimitive₁`
and its companions, which read the fields back as statements about `X[V₁]` and `X[V₂]`,
they say that the paper's `Case` and ours are the same condition. -/

/-- The color classes of `X[Δ]` are the color classes of `X` on `Δ`: this is what the
part fields of a `Case` of §9.6-§9.8 ask for, for `Δ` a vertex-color class. -/
theorem PartitionStructure.natColor_induced_eq_iff {V : Type} [Fintype V]
    (X : PartitionStructure V) (Δ : Set V) [Fintype ↥Δ] (x y x' y' : ↥Δ) :
    (X.induced Δ).natColor x y = (X.induced Δ).natColor x' y' ↔
      X.natColor (x : V) (y : V) = X.natColor (x' : V) (y' : V) := by
  rw [PartitionStructure.natColor_eq_iff, PartitionStructure.natColor_eq_iff,
    X.induced_color_eq_iff]

/-- §9.6-§9.8.  The `Case` heading of §9.4 step 9, in the paper's own words: `X` is a
coherent configuration whose vertex set is the union of two vertex-color classes `V₁` and
`V₂`, the induced configuration `X₁ = X[V₁]` is a UPCC, and the link `X₁₂` is nontrivial
(two pairs of `V₁ × V₂` get different colors). -/
theorem isBipartiteCase_induced {V : Type} [Fintype V] (X : PartitionStructure V)
    (hX : X.IsCoherent) {i j : Fin X.rank} [Fintype ↥(X.vertexClass i)]
    (hij : i ≠ j) (hcover : ∀ x : V, x ∈ X.vertexClass i ∨ x ∈ X.vertexClass j)
    (huni₁ : (X.induced (X.vertexClass i)).IsUniprimitive)
    {x₁ x₂ : ↥(X.vertexClass i)} {y₁ y₂ : ↥(X.vertexClass j)}
    (hlink : X.natColor (x₁ : V) (y₁ : V) ≠ X.natColor (x₂ : V) (y₂ : V)) :
    IsBipartiteCase X.natColor (X.vertexClass i) (X.vertexClass j) where
  coherent := ⟨X, hX, rfl, i, j, hij, rfl, rfl, hcover⟩
  upcc₁ := ⟨X.induced (X.vertexClass i),
    X.induced_isCoherent hX (X.isStable_vertexClass i), huni₁,
    X.natColor_induced_eq_iff (X.vertexClass i)⟩
  link_nontrivial := ⟨x₁, y₁, x₂, y₂, hlink⟩

/-- §9.6.  The `Case` of §9.6 in the paper's own words: the `Case` of §9.4 step 9, and in
addition the induced configuration `X₂ = X[V₂]` is homogeneous and imprimitive. -/
theorem isImprimitiveCase_induced {V : Type} [Fintype V] (X : PartitionStructure V)
    (hX : X.IsCoherent) {i j : Fin X.rank}
    [Fintype ↥(X.vertexClass i)] [Fintype ↥(X.vertexClass j)]
    (hij : i ≠ j) (hcover : ∀ x : V, x ∈ X.vertexClass i ∨ x ∈ X.vertexClass j)
    (huni₁ : (X.induced (X.vertexClass i)).IsUniprimitive)
    (hhom₂ : (X.induced (X.vertexClass j)).IsHomogeneous)
    (hprim₂ : ¬ (X.induced (X.vertexClass j)).IsPrimitive)
    {x₁ x₂ : ↥(X.vertexClass i)} {y₁ y₂ : ↥(X.vertexClass j)}
    (hlink : X.natColor (x₁ : V) (y₁ : V) ≠ X.natColor (x₂ : V) (y₂ : V)) :
    IsImprimitiveCase X.natColor (X.vertexClass i) (X.vertexClass j) where
  toIsBipartiteCase := isBipartiteCase_induced X hX hij hcover huni₁ hlink
  imprimitive₂ := ⟨X.induced (X.vertexClass j),
    X.induced_isCoherent hX (X.isStable_vertexClass j), hhom₂, hprim₂,
    X.natColor_induced_eq_iff (X.vertexClass j)⟩

end Babai
