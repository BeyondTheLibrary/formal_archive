/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sections 3.1.1 and 8.1: naming the colors of a canonical coloring by natural numbers.
-/
import Mathlib.Data.Set.Card
import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Naming abstract colors by natural numbers

Definition 3.1.1 numbers the colors of a partition structure by `[r]`, and the categories
of §9 (`Babai.UPCCs`, `Babai.ColoredPartitions`) take colorings by `ℕ`: a morphism there
is a bijection that preserves the color **labels**.  The colorings that §5 and §8 produce
(`k`-ary WL, the `2`-skeleton) take values in an abstract type `K`, so §9 needs a way to
turn a `K`-coloring into an `ℕ`-coloring.

The naming has to commute with isomorphisms.  Two isomorphic inputs get *equal* WL colors
(§5.4.1), so the only thing the naming may use is the color itself and the set `R ⊆ K` of
colors that actually occur — and that set is the same for the two inputs.  So we fix a
well-ordering of `K` (the canonical one, `WellOrderingRel`, as in
`Babai.firstOf`; see the corrected paper entry on "the first disconnected constituent")
and name a color `c` by the number of colors of `R` below it:

  `natRank R c = |{d ∈ R | d ≺ c}|`.

This is a function of `R` and `c` alone, so it commutes with isomorphisms, and it is
injective on `R` (`natRank_injOn`), so the `ℕ`-coloring it produces has exactly the color
classes of the original coloring.

The chosen well-ordering is not computable; the machine layer will replace it by the
lexicographic order that WL refinement uses.  See the "Owed" note of the the corrected paper
entry on outcome (b) of Theorem 8.1.2.
-/

namespace Babai

variable {K : Type*}

/-- The name in `ℕ` of the color `c`, relative to the set `R` of colors that occur: the
number of colors of `R` strictly below `c` in the canonical well-ordering of the color
type. -/
noncomputable def natRank (R : Set K) (c : K) : ℕ :=
  {d ∈ R | WellOrderingRel d c}.ncard

/-- The naming is a function of the set of occurring colors and of the color, so equal
data give equal names.  (This is the form in which the canonicity of §6 uses it.) -/
theorem natRank_congr {R R' : Set K} {c c' : K} (hR : R = R') (hc : c = c') :
    natRank R c = natRank R' c' := by rw [hR, hc]

/-- The set of colors of `R` below `c` grows strictly when `c` moves up past a color of
`R`. -/
theorem natRank_lt {R : Set K} (hR : R.Finite) {c c' : K} (hc : c ∈ R)
    (hlt : WellOrderingRel c c') : natRank R c < natRank R c' := by
  classical
  have hsub : {d ∈ R | WellOrderingRel d c} ⊆ {d ∈ R | WellOrderingRel d c'} := by
    rintro d ⟨hdR, hdc⟩
    exact ⟨hdR, _root_.trans hdc hlt⟩
  have hmem : c ∈ {d ∈ R | WellOrderingRel d c'} := ⟨hc, hlt⟩
  have hnot : c ∉ {d ∈ R | WellOrderingRel d c} := fun h => irrefl_of _ c h.2
  have hssub : {d ∈ R | WellOrderingRel d c} ⊂ {d ∈ R | WellOrderingRel d c'} :=
    ⟨hsub, fun h => hnot (h hmem)⟩
  exact Set.ncard_lt_ncard hssub (hR.subset fun d hd => hd.1)

/-- The naming is injective on the colors that occur: it has the same kernel as the
original coloring. -/
theorem natRank_injOn {R : Set K} (hR : R.Finite) :
    Set.InjOn (natRank R) R := by
  intro c hc c' hc' h
  rcases trichotomous_of (WellOrderingRel : K → K → Prop) c c' with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (natRank_lt hR hc hlt))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (natRank_lt hR hc' hgt))

/-- The kernel of the naming, on the colors that occur. -/
theorem natRank_eq_iff {R : Set K} (hR : R.Finite) {c c' : K} (hc : c ∈ R) (hc' : c' ∈ R) :
    natRank R c = natRank R c' ↔ c = c' :=
  ⟨fun h => natRank_injOn hR hc hc' h, fun h => by rw [h]⟩

end Babai
