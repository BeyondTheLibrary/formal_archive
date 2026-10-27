/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.3: the facts about a UPCC that the proof of Lemma 9.3.1 uses, restated for the
`ℕ`-valued edge coloring, which is what an object of `Babai.UPCCs` is.
-/
import Workspace.Coherent.Diameter
import Workspace.SplitOrJohnson.Defs

/-!
# UPCC facts at the level of `ℕ`-valued edge colorings

An object of the category `Babai.UPCCs Ω` on a set `s` is an edge coloring
`c : ↥s → ↥s → ℕ` together with the *proposition* `Babai.IsUPCCColoring c`, which says
that some `Babai.PartitionStructure` with those color classes is a UPCC.  A structure
taken out of that proposition by choice is not natural in the object: for an isomorphism
`f : X → Y` of two such colorings there is no link between the structure chosen for `X`
and the one chosen for `Y`.  So every construction inside the proof of Lemma 9.3.1 has to
be written in terms of `c` alone, and every fact it uses has to be available for `c`.

This file provides those facts.  Each one is proved by choosing a structure `P` from the
hypothesis and translating along `P.natColor = c`.  The translation is easy because
`natColor` is the `Fin`-valued color read as a number, so it has the same kernel:

* `Babai.PartitionStructure.natColor_eq_iff` — the two colorings have the same kernel;
* `Babai.PartitionStructure.setOf_natColor_eq_nbr` — a color class of `c` at a point is a
  constituent neighbourhood, when the color is below the rank;
* `Babai.PartitionStructure.setOf_natColor_eq_empty` — and is empty otherwise.

## Numbering map

| Paper | Lean |
|---|---|
| homogeneity (Def. 3.1.6) | `Babai.natColor_diag_eq` |
| Observation 3.3.5 (degree awareness) | `Babai.natColor_outDeg_eq` |
| Definition 3.1.11, Eq. (17) (intersection numbers) | `Babai.natColor_interNum` |
| Corollary 3.3.7(i) (homogeneous constituents are eulerian) | `Babai.natColor_inDeg_eq_outDeg` |
| *"`(V,R₂)` is undirected since `d₂ ≥ n/2`"* (§9.3) | `Babai.natColor_symm_of_large` |
| the diameter-2 step of §9.3 | `Babai.natColor_exists_mid` |
| Observation 3.3.5, in-degree form (the `d_j` of §9.6) | `Babai.natColor_inDeg_eq_of_diag_eq` |
-/

namespace Babai

namespace PartitionStructure

variable {Ω : Type*} (X : PartitionStructure Ω)

/-- The `ℕ`-valued coloring has the same kernel as the `Fin`-valued one. -/
theorem natColor_eq_iff (x y u v : Ω) :
    X.natColor x y = X.natColor u v ↔ X.color x y = X.color u v := by
  rw [natColor, natColor, Fin.val_eq_val]

/-- Every color of `natColor` is below the rank. -/
theorem natColor_lt_rank (x y : Ω) : X.natColor x y < X.rank := (X.color x y).isLt

/-- A color of `natColor` below the rank names a color of `X`. -/
theorem natColor_eq_iff_color_eq {k : ℕ} (h : k < X.rank) (x y : Ω) :
    X.natColor x y = k ↔ X.color x y = ⟨k, h⟩ :=
  ⟨fun hk => Fin.ext hk, fun hk => by rw [natColor, hk]⟩

/-- A color class of `natColor` at a point is a constituent neighbourhood. -/
theorem setOf_natColor_eq_nbr {k : ℕ} (h : k < X.rank) (u : Ω) :
    {y | X.natColor u y = k} = X.nbr ⟨k, h⟩ u :=
  Set.ext fun y => X.natColor_eq_iff_color_eq h u y

/-- Above the rank there is no color class. -/
theorem setOf_natColor_eq_empty {k : ℕ} (h : ¬ k < X.rank) (u : Ω) :
    {y | X.natColor u y = k} = ∅ := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hy
  exact h (hy ▸ X.natColor_lt_rank u y)

/-- Above the rank there is no color class, on the other side. -/
theorem setOf_natColor_left_eq_empty {k : ℕ} (h : ¬ k < X.rank) (v : Ω) :
    {y | X.natColor y v = k} = ∅ := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hy
  exact h (hy ▸ X.natColor_lt_rank y v)

/-- An off-diagonal color is not the color of a vertex. -/
theorem ne_vcolor_of_isOffDiagonalColor {i : Fin X.rank} (hi : X.IsOffDiagonalColor i)
    (x : Ω) : i ≠ X.vcolor x := by
  intro h
  exact Set.eq_empty_iff_forall_notMem.1 hi (x, x) ⟨h ▸ rfl, rfl⟩

end PartitionStructure

/-! ### The facts, for a UPCC coloring -/

variable {Ω : Type} [Fintype Ω] {s : Set Ω} {c : ↥s → ↥s → ℕ}

omit [Fintype Ω] in
/-- (N1)  A UPCC is homogeneous (Def. 3.1.6), so all vertices have the same color. -/
theorem natColor_diag_eq (hc : IsUPCCColoring c) (u v : ↥s) : c u u = c v v := by
  obtain ⟨P, -, huni, rfl⟩ := hc
  exact congrArg Fin.val (huni.1.1 u v)

/-- (N2)  Observation 3.3.5 (degree awareness) for a homogeneous coherent configuration:
the out-degree in a given color does not depend on the vertex. -/
theorem natColor_outDeg_eq (hc : IsUPCCColoring c) (u v : ↥s) (k : ℕ) :
    {y | c u y = k}.ncard = {y | c v y = k}.ncard := by
  obtain ⟨P, hcoh, huni, rfl⟩ := hc
  by_cases h : k < P.rank
  · letI : Fintype ↥s := Fintype.ofFinite _
    rw [P.setOf_natColor_eq_nbr h u, P.setOf_natColor_eq_nbr h v,
      ← P.outDegC_eq_ncard, ← P.outDegC_eq_ncard]
    exact P.outDegC_eq_of_vcolor_eq hcoh _ (huni.1.1 u v)
  · rw [P.setOf_natColor_eq_empty h u, P.setOf_natColor_eq_empty h v]

omit [Fintype Ω] in
/-- (N3)  Definition 3.1.11, Eq. (17): the number of `(a,b)`-paths from `u` to `v` depends
only on the color of `(u,v)`. -/
theorem natColor_interNum (hc : IsUPCCColoring c) {u v u' v' : ↥s}
    (h : c u v = c u' v') (a b : ℕ) :
    {y | c u y = a ∧ c y v = b}.ncard = {y | c u' y = a ∧ c y v' = b}.ncard := by
  obtain ⟨P, hcoh, -, rfl⟩ := hc
  by_cases ha : a < P.rank
  · by_cases hb : b < P.rank
    · have hcol : P.color u v = P.color u' v' := (P.natColor_eq_iff _ _ _ _).1 h
      have e : ∀ x y : ↥s, {z : ↥s | P.natColor x z = a ∧ P.natColor z y = b}
          = {z : ↥s | P.color x z = ⟨a, ha⟩ ∧ P.color z y = ⟨b, hb⟩} := by
        intro x y
        ext z
        exact and_congr (P.natColor_eq_iff_color_eq ha x z)
          (P.natColor_eq_iff_color_eq hb z y)
      rw [e u v, e u' v', P.interNum_eq hcoh ⟨a, ha⟩ ⟨b, hb⟩ (P.color u v) rfl,
        P.interNum_eq hcoh ⟨a, ha⟩ ⟨b, hb⟩ (P.color u v) hcol.symm]
    · have e : ∀ x y : ↥s, {z : ↥s | P.natColor x z = a ∧ P.natColor z y = b} = ∅ := by
        intro x y
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        rintro - hz
        exact hb (hz ▸ P.natColor_lt_rank z y)
      rw [e u v, e u' v']
  · have e : ∀ x y : ↥s, {z : ↥s | P.natColor x z = a ∧ P.natColor z y = b} = ∅ := by
      intro x y
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      rintro hz -
      exact ha (hz ▸ P.natColor_lt_rank x z)
    rw [e u v, e u' v']

/-- (N4)  Corollary 3.3.7(i): a homogeneous constituent is eulerian, so in-degree and
out-degree agree in every color. -/
theorem natColor_inDeg_eq_outDeg (hc : IsUPCCColoring c) (u : ↥s) (k : ℕ) :
    {y | c y u = k}.ncard = {y | c u y = k}.ncard := by
  obtain ⟨P, hcoh, huni, rfl⟩ := hc
  by_cases h : k < P.rank
  · letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    have heul : P.outDegC ⟨k, h⟩ u = P.inDegC ⟨k, h⟩ u :=
      P.extConstituent_isEulerian hcoh ⟨k, h⟩
        (P.tailColor_eq_headColor_of_isHomogeneous huni.1.1 ⟨k, h⟩) u
    have hin : {y : ↥s | P.natColor y u = k} = {y : ↥s | P.color y u = ⟨k, h⟩} :=
      Set.ext fun y => P.natColor_eq_iff_color_eq h y u
    rw [hin, P.setOf_natColor_eq_nbr h u, ← P.outDegC_eq_ncard]
    exact (P.inDegC_eq_ncard ⟨k, h⟩ u ▸ heul).symm
  · rw [P.setOf_natColor_left_eq_empty h u, P.setOf_natColor_eq_empty h u]

/-- (N5)  *"`(V, R₂)` is an undirected graph (since `d₂ ≥ n/2`)"* (§9.3, proof of
Lemma 9.3.1): a color whose class at one vertex has more than half the vertices is
symmetric.

The size of the vertex set is written `Nat.card ↥s`, which is `s.ncard`; writing
`Fintype.card ↥s` would force a `Fintype` instance argument on a statement that does not
need one. -/
theorem natColor_symm_of_large (hc : IsUPCCColoring c) {k : ℕ} {x : ↥s}
    (hd : Nat.card ↥s < 2 * {y | c x y = k}.ncard) {u v : ↥s} (h : c u v = k) :
    c v u = k := by
  obtain ⟨P, hcoh, huni, rfl⟩ := hc
  by_cases hk : k < P.rank
  · letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    have hcard : Fintype.card ↥s < 2 * (P.nbr ⟨k, hk⟩ x).ncard := by
      rw [← P.setOf_natColor_eq_nbr hk x, ← Nat.card_eq_fintype_card]
      exact hd
    have hconv : P.conv ⟨k, hk⟩ = ⟨k, hk⟩ :=
      P.conv_eq_self_of_two_mul_outDeg_gt hcoh huni.1.1 hcard
    have huv : P.color u v = ⟨k, hk⟩ := (P.natColor_eq_iff_color_eq hk u v).1 h
    refine (P.natColor_eq_iff_color_eq hk v u).2 ?_
    rw [P.color_comm hcoh.toIsConfiguration u v, huv, hconv]
  · rw [P.setOf_natColor_eq_empty hk x, Set.ncard_empty] at hd
    omega

/-- (N6)  The diameter-2 step of the proof of Lemma 9.3.1 (§9.3): *"Let `(x, z) ∈ R₂` and
let `y ∈ V` be such that `(x, y) ∈ Rᵢ` and `(z, y) ∈ R_j` where `i, j ≥ 3`."*

*"`i, j ≥ 3`"* means: not the vertex color, and not the color `k` of the pair `(x,z)`.
The proof is `Babai.PartitionStructure.exists_mid_of_undirected_constituent`. -/
theorem natColor_exists_mid (hc : IsUPCCColoring c) {k : ℕ}
    (hsymm : ∀ u v : ↥s, c u v = k → c v u = k) {x z : ↥s} (hxz : c x z = k)
    (hk : k ≠ c x x) :
    ∃ y : ↥s, c x y ≠ c x x ∧ c x y ≠ k ∧ c z y ≠ c x x ∧ c z y ≠ k := by
  obtain ⟨P, hcoh, huni, rfl⟩ := hc
  have hkr : k < P.rank := hxz ▸ P.natColor_lt_rank x z
  set k' : Fin P.rank := ⟨k, hkr⟩ with hk'
  -- `k'` is off-diagonal: it is not the vertex color.
  have hoff : P.IsOffDiagonalColor k' := by
    refine P.isOffDiagonalColor_of_ne_vcolor hcoh.toIsConfiguration huni.1.1 x ?_
    intro hcon
    exact hk (congrArg Fin.val hcon)
  -- `k'` is undirected: `hsymm` says exactly that `R_{k'}` is symmetric.
  have hconv : P.conv k' = k' := by
    obtain ⟨a, b, hab⟩ := P.color_surjective k'
    have hnat : P.natColor a b = k := congrArg Fin.val hab
    have hba : P.color b a = k' := (P.natColor_eq_iff_color_eq hkr b a).1 (hsymm a b hnat)
    have := P.color_comm hcoh.toIsConfiguration a b
    rw [hba, hab] at this
    exact this.symm
  have hxz' : P.color x z = k' := (P.natColor_eq_iff_color_eq hkr x z).1 hxz
  obtain ⟨y, h1, h2, h3, h4⟩ :=
    P.exists_mid_of_undirected_constituent hcoh huni hoff hconv hxz'
  refine ⟨y, ?_, ?_, ?_, ?_⟩
  · intro hcon
    exact P.ne_vcolor_of_isOffDiagonalColor h1 x ((P.natColor_eq_iff _ _ _ _).1 hcon)
  · exact fun hcon => h2 ((P.natColor_eq_iff_color_eq hkr x y).1 hcon)
  · intro hcon
    -- `c x x = c z z` by homogeneity, so the vertex color is the same one.
    have hxx : P.color x x = P.color z z := huni.1.1 x z
    have : P.color z y = P.color x x := (P.natColor_eq_iff _ _ _ _).1 hcon
    exact P.ne_vcolor_of_isOffDiagonalColor h3 z (this.trans hxx)
  · exact fun hcon => h4 ((P.natColor_eq_iff_color_eq hkr z y).1 hcon)

omit [Fintype Ω] in
/-- (N3′)  The out-form of (N3), which is what the semiregularity of the bipartite graph
`X̄ = (C₂, Cᵢ; R_j)` of §9.3 needs: the number of common out-neighbours of `u` and `v` in
the colors `a` and `b` depends only on the color of `(u,v)`.

This is Eq. (17) again, read through `c(v,y) = b ↔ c(y,v) = b⁻`. -/
theorem natColor_interNum_out (hc : IsUPCCColoring c) {u v u' v' : ↥s}
    (h : c u v = c u' v') (a b : ℕ) :
    {y | c u y = a ∧ c v y = b}.ncard = {y | c u' y = a ∧ c v' y = b}.ncard := by
  obtain ⟨P, hcoh, -, rfl⟩ := hc
  by_cases hb : b < P.rank
  · by_cases ha : a < P.rank
    · -- rewrite `c v y = b` as `c y v = b⁻`, then apply Eq. (17)
      have key : ∀ w z : ↥s, {y : ↥s | P.natColor w y = a ∧ P.natColor z y = b}
          = {y : ↥s | P.color w y = ⟨a, ha⟩ ∧ P.color y z = P.conv ⟨b, hb⟩} := by
        intro w z
        ext y
        refine and_congr (P.natColor_eq_iff_color_eq ha w y) ?_
        rw [P.natColor_eq_iff_color_eq hb z y,
          P.color_conv_iff hcoh.toIsConfiguration ⟨b, hb⟩ z y]
      have hcol : P.color u v = P.color u' v' := (P.natColor_eq_iff _ _ _ _).1 h
      rw [key u v, key u' v',
        P.interNum_eq hcoh ⟨a, ha⟩ (P.conv ⟨b, hb⟩) (P.color u v) rfl,
        P.interNum_eq hcoh ⟨a, ha⟩ (P.conv ⟨b, hb⟩) (P.color u v) hcol.symm]
    · have e : ∀ w z : ↥s, {y : ↥s | P.natColor w y = a ∧ P.natColor z y = b} = ∅ := by
        intro w z
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hy
        exact absurd (hy ▸ P.natColor_lt_rank w y) ha
      rw [e u v, e u' v']
  · have e : ∀ w z : ↥s, {y : ↥s | P.natColor w y = a ∧ P.natColor z y = b} = ∅ := by
      intro w z
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      rintro - hy
      exact hb (hy ▸ P.natColor_lt_rank z y)
    rw [e u v, e u' v']

omit [Fintype Ω] in
/-- A vertex is the only out-neighbour of itself in its own color: `c x y = c x x` forces
`y = x` (axiom (i) of Def. 3.1.2). -/
theorem natColor_eq_diag_imp_eq (hc : IsUPCCColoring c) {x y : ↥s} (h : c x y = c x x) :
    x = y := by
  obtain ⟨P, hcoh, -, rfl⟩ := hc
  exact hcoh.toIsConfiguration.diag x y x ((P.natColor_eq_iff _ _ _ _).1 h)

omit [Fintype Ω] in
/-- A UPCC has at least two vertices: its rank is at least `3`, and on a one-point set
every pair of vertices is the same pair, so the rank would be `1`. -/
theorem natColor_nontrivial (hc : IsUPCCColoring c) : ∃ u v : ↥s, u ≠ v := by
  obtain ⟨P, -, huni, -⟩ := hc
  by_contra hcon
  push_neg at hcon
  have h3 : 3 ≤ P.rank := huni.2
  have hall : ∀ i : Fin P.rank, i = ⟨0, by omega⟩ := by
    intro i
    obtain ⟨u, v, huv⟩ := P.color_surjective i
    obtain ⟨u', v', huv'⟩ := P.color_surjective ⟨0, by omega⟩
    rw [← huv, ← huv', hcon u u', hcon v v']
  have h1 := hall ⟨1, by omega⟩
  have : (1 : ℕ) = 0 := congrArg Fin.val h1
  omega

/-! ### §9.6: the in-degrees `d_j` of the link -/

/-- The coloring `c` is the coloring of a *coherent* configuration.  This is what §9.6 has
after step 3 of Procedure Bipartite Split-or-Johnson (*"Apply WL refinement to `X`"*); it is
weaker than `Babai.IsUPCCColoring`, which also asks for uniprimitivity. -/
def IsCoherentColoring {Ω : Type*} {s : Set Ω} (c : ↥s → ↥s → ℕ) : Prop :=
  ∃ P : PartitionStructure ↥s, P.IsCoherent ∧ P.natColor = c

/-- (N7)  Observation 3.3.5 (degree awareness), in-degree form, for an arbitrary finite
vertex set.  This is the form §9.6 uses: its vertex set is *"points of `V₁` plus blocks"*,
which is not a set of points of the ambient type.  See
`Babai.natColor_inDeg_eq_of_diag_eq` for the wording of the paper's hypothesis. -/
theorem natColor_inDeg_eq_of_diag_eq' {V : Type*} [Finite V] {cc : V → V → ℕ}
    (hc : ∃ P : PartitionStructure V, P.IsCoherent ∧ P.natColor = cc) {u v : V}
    (huv : cc u u = cc v v) (k : ℕ) :
    {x | cc x u = k}.ncard = {x | cc x v = k}.ncard := by
  classical
  obtain ⟨P, hcoh, rfl⟩ := hc
  by_cases h : k < P.rank
  · letI : Fintype V := Fintype.ofFinite _
    letI : DecidableEq V := Classical.decEq _
    have hset : ∀ w : V, {x : V | P.natColor x w = k} = {x : V | P.color x w = ⟨k, h⟩} :=
      fun w => Set.ext fun x => P.natColor_eq_iff_color_eq h x w
    have hvc : P.vcolor u = P.vcolor v := (P.natColor_eq_iff _ _ _ _).1 huv
    rw [hset u, hset v, ← P.inDegC_eq_ncard ⟨k, h⟩ u, ← P.inDegC_eq_ncard ⟨k, h⟩ v]
    exact P.inDegC_eq_of_vcolor_eq hcoh ⟨k, h⟩ hvc
  · rw [P.setOf_natColor_left_eq_empty h u, P.setOf_natColor_left_eq_empty h v]

/-- (N7)  Observation 3.3.5 (degree awareness), in-degree form, for a coherent
configuration that need not be homogeneous: two vertices of the same vertex color have the
same in-degree in every color.

This is what makes the `d_j` of §9.6 well defined.  The paper says *"`d_j` does not depend
on `y` because of the homogeneity of `X₂`"*; homogeneity of `X₂` is not needed, and is not
what is used: `V₂` is a **vertex-color class of `X`** (the `Case` of §9.6 is a bihomogeneous
configuration, Def. 3.4.24), so all its points already have the same vertex color in `X`,
which is the hypothesis `c u u = c v v` here. -/
theorem natColor_inDeg_eq_of_diag_eq (hc : IsCoherentColoring c) {u v : ↥s}
    (huv : c u u = c v v) (k : ℕ) :
    {x | c x u = k}.ncard = {x | c x v = k}.ncard := by
  obtain ⟨P, hcoh, rfl⟩ := hc
  by_cases h : k < P.rank
  · letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    have hset : ∀ w : ↥s, {x : ↥s | P.natColor x w = k} = {x : ↥s | P.color x w = ⟨k, h⟩} :=
      fun w => Set.ext fun x => P.natColor_eq_iff_color_eq h x w
    have hvc : P.vcolor u = P.vcolor v := (P.natColor_eq_iff _ _ _ _).1 huv
    rw [hset u, hset v, ← P.inDegC_eq_ncard ⟨k, h⟩ u, ← P.inDegC_eq_ncard ⟨k, h⟩ v]
    exact P.inDegC_eq_of_vcolor_eq hcoh ⟨k, h⟩ hvc
  · rw [P.setOf_natColor_left_eq_empty h u, P.setOf_natColor_left_eq_empty h v]

end Babai
