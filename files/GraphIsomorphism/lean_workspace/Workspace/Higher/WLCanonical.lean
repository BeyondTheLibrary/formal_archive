/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 5.4.1 (Eq. (26)): canonicity of `k`-ary WL across *different* vertex sets.
-/
import Workspace.Higher.WL

/-!
# §5.4.1, Eq. (26): canonicity of `k`-ary WL across different vertex sets

`iso_F3` (§5.2) compares `X.F3` with `Y.wlIter (Fintype.card (Str Ω k × Str Ω k))`, that is,
it runs on `Y` the number of rounds computed from `Ω`, not from `Ω'`.  The reason is that
the color type of `F3` is `wlColorType C k (Fintype.card (Str Ω k × Str Ω k))`, which
depends on `|Ω|`, so for `f : Ω ≃ Ω'` the two color types are only *propositionally* equal
and `Iso X.F3 Y.F3` does not typecheck.

This file closes that gap.  The two round counts are equal (`f` is a bijection), so the
two color types are equal, and the colors of `Y.F3` are the colors of `X.F3` transported
along that equality (`wlStable_color_cast`).  Three forms are provided:

* `wlIter_color_cast`: changing the number of rounds along an equality of naturals
  transports the colors by `cast`;
* `wlStable_color_cast`: the equality of colors of `F3(X)` and `F3(Y)` under an
  isomorphism `f : X → Y`, transported along the equality of the two color types;
* `wlStable_color_eq_iff`: the kernel form, `f` preserves the color classes.

The cast form is the one that makes *ordered* data canonical: a relation or an order on
the color type is carried along `cast` (`cast_rel_cast`), so a choice such as "the first
color with a given property" (Thm. 8.1.2, outcome (b)) is the same on both sides.

| Paper | Lean |
|---|---|
| §5.4.1, Eq. (26), across vertex sets | `Babai.KAryPartStruct.wlStable_color_cast`, `.wlStable_color_eq_iff` |
-/

namespace Babai

namespace KAryPartStruct

variable {Ω Ω' : Type*} {C : Type} {k : ℕ}

/-- Changing the number of rounds along an equality `m = n` of naturals: the color after
`n` rounds is the color after `m` rounds, transported along the induced equality of color
types. -/
theorem wlIter_color_cast (X : KAryPartStruct Ω C k) {m n : ℕ} (h : m = n) (x : Str Ω k) :
    (X.wlIter n).color x = cast (congrArg (wlColorType C k) h) ((X.wlIter m).color x) := by
  subst h; rfl

/-- §5.4.1, Eq. (26), applied to a single string: an isomorphism `f : X → Y` carries the
color of `x⃗` after `n` rounds to the color of `x⃗^f` after `n` rounds. -/
theorem iso_wlIter_color {X : KAryPartStruct Ω C k} {Y : KAryPartStruct Ω' C k}
    {f : Ω ≃ Ω'} (hf : f ∈ Iso X Y) (n : ℕ) (x : Str Ω k) :
    (Y.wlIter n).color (tupleMap f x) = (X.wlIter n).color x := by
  have h : f ∈ Iso (X.wlIter n) (Y.wlIter n) := by rw [iso_wlIter X Y n]; exact hf
  exact h x

variable [Fintype Ω] [Fintype Ω']

/-- The two numbers of rounds agree: `f : Ω ≃ Ω'` gives `|Ω^k × Ω^k| = |Ω'^k × Ω'^k|`. -/
theorem card_str_prod_eq (f : Ω ≃ Ω') :
    Fintype.card (Str Ω k × Str Ω k) = Fintype.card (Str Ω' k × Str Ω' k) :=
  Fintype.card_congr (Equiv.prodCongr (Equiv.arrowCongr (Equiv.refl _) f)
    (Equiv.arrowCongr (Equiv.refl _) f))

/-- §5.4.1, Eq. (26), across different vertex sets.  Let `f : X → Y` be an isomorphism of
`k`-ary partition structures on vertex sets `Ω` and `Ω'`.  The two runs of `k`-ary WL use
the same number of rounds (`card_str_prod_eq`), so their color types are equal, and the
color of `x⃗^f` in `F3(Y)` is the color of `x⃗` in `F3(X)` transported along that
equality. -/
theorem wlStable_color_cast {X : KAryPartStruct Ω C k} {Y : KAryPartStruct Ω' C k}
    {f : Ω ≃ Ω'} (hf : f ∈ Iso X Y)
    (hN : Fintype.card (Str Ω k × Str Ω k) = Fintype.card (Str Ω' k × Str Ω' k))
    (x : Str Ω k) :
    Y.wlStable.color (tupleMap f x)
      = cast (congrArg (wlColorType C k) hN) (X.wlStable.color x) := by
  show (Y.wlIter (Fintype.card (Str Ω' k × Str Ω' k))).color (tupleMap f x) = _
  rw [Y.wlIter_color_cast hN (tupleMap f x), iso_wlIter_color hf _ x]
  rfl

/-- §5.4.1, Eq. (26), across different vertex sets, kernel form: an isomorphism
`f : X → Y` carries the color classes of `F3(X)` to the color classes of `F3(Y)`. -/
theorem wlStable_color_eq_iff {X : KAryPartStruct Ω C k} {Y : KAryPartStruct Ω' C k}
    {f : Ω ≃ Ω'} (hf : f ∈ Iso X Y) (u v : Str Ω k) :
    Y.wlStable.color (tupleMap f u) = Y.wlStable.color (tupleMap f v)
      ↔ X.wlStable.color u = X.wlStable.color v := by
  have hN : Fintype.card (Str Ω k × Str Ω k) = Fintype.card (Str Ω' k × Str Ω' k) :=
    card_str_prod_eq f
  rw [wlStable_color_cast hf hN, wlStable_color_cast hf hN]
  exact cast_inj _

end KAryPartStruct

end Babai
