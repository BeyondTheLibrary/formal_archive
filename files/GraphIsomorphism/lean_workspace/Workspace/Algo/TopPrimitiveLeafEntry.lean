import Workspace.Algo.TopPrimitiveLeafCost
import Workspace.Algo.TopFourPrimitive

/-! # The computed line 4a test supplies the direct leaf
The standard-block test identifies the point labels. At `t = 1` its
singleton labels imply precisely the giant hypothesis used by the leaf.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

theorem primitiveLeaf_test_spec {n m : ℕ} {p : RawAction}
    {ϕ : decGroup n p.1.2 →* Perm (Fin m)} (hp : RawAction.WF n m p ϕ)
    (hG : IsTransitive (decGroup n p.1.2)) (hϕ : IsGiantRep ϕ)
    (hm : HugeM m (Nat.card (Fin n))) (ht : primitiveCaseTest (p, 1) = true)
    {x y : RawStr} (hx : x.length = n) (hy : y.length = n) :
    decCoset n (primitiveLeaf (p.1.2, x, y)) =
      strIso (decGroup n p.1.2 : Set (Perm (Fin n))) (decStrN n x) (decStrN n y) :=
  primitiveLeaf_spec hp.2.2.1 hx hy
    (primitiveCase_one_giant (top4PrimitiveId hp hG hϕ hm ht) hϕ)

theorem primitiveLeaf_test_loop (a b : ℕ) {n m : ℕ} {p : RawAction}
    {ϕ : decGroup n p.1.2 →* Perm (Fin m)} (hp : RawAction.WF n m p ϕ)
    (hG : IsTransitive (decGroup n p.1.2)) (hϕ : IsGiantRep ϕ)
    (hm : HugeM m (Nat.card (Fin n))) (ht : primitiveCaseTest (p, 1) = true)
    {x y : RawStr} (hx : x.length = n) (hy : y.length = n) :
    LoopMatch (primitiveLeafRound a b) (primitiveLeafInstance n) (decCoset n) (p.1.2, x, y) 0 0 0
      (line4aReduction (primitiveLeafInstance n (p.1.2, x, y))) :=
  primitiveLeaf_loop a b hp.2.2.1 hx hy
    (primitiveCase_one_giant (top4PrimitiveId hp hG hϕ hm ht) hϕ)

end Algo
