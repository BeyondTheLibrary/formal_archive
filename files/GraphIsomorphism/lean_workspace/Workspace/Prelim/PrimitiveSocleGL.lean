/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Background used by the proof of Lemma 10.2.5, Case 1 (the affine case): the automorphism
group of an elementary abelian group of order `p^s` is `GL(s, p)`.
-/
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Algebra.Group.End

/-!
# `Aut(ℤ_p^s) ≅ GL(s, p)`

The proof of Lemma 10.2.5, Case 1, says: "`N ≅ ℤ_p^s` and `G/N ≤ GL(s, p)`".  The
embedding is the conjugation action of `G` on `N`, whose kernel is `C_G(N) = N`; so what
is needed is that the automorphism group of an elementary abelian group of order `p^s` is
`GL(s, p)`.  The paper cites nothing for this (it is Dixon–Mortimer, *Permutation Groups*,
GTM 163, Theorem 4.3B (i), p. 114), so it is proved here.

Over `ZMod n` every additive map is linear (`ZMod.map_smul`), so the argument needs no
primality of `p`.
-/

namespace Babai

open Matrix

variable (n : ℕ) (M : Type*) [AddCommGroup M] [Module (ZMod n) M]

/-- Over `ZMod n` the additive automorphisms of a module are exactly its linear
automorphisms (every additive map is `ZMod n`-linear). -/
def addAutEquivLinearEquiv : AddAut M ≃* (M ≃ₗ[ZMod n] M) where
  toFun f := f.toLinearEquiv (fun c x => ZMod.map_smul (f : M →+ M) c x)
  invFun g := { g with map_add' := g.map_add }
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- `Aut(ℤ_p^s) ≅ GL(s, p)`, in the form used by the proof of Lemma 10.2.5, Case 1: the
automorphism group of the elementary abelian group `ℤ_p^s`, written multiplicatively, is
the matrix group `GL(s, ZMod p)`. -/
def mulAutEquivGL (p s : ℕ) :
    MulAut (Multiplicative (Fin s → ZMod p)) ≃* Matrix.GeneralLinearGroup (Fin s) (ZMod p) :=
  (MulAutMultiplicative (Fin s → ZMod p)).trans <|
    (addAutEquivLinearEquiv p (Fin s → ZMod p)).trans <|
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Fin s → ZMod p)).symm.trans
        (Matrix.GeneralLinearGroup.toLin (n := Fin s) (R := ZMod p)).symm)

end Babai
