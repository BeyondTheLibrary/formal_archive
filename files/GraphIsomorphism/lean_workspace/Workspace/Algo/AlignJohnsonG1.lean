/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align (§14.1), line 2 (iv) — the group
`G₁ = ϕ⁻¹(Aut(X(x)))` when `X(x)` is a Johnson scheme, on the unit-cost RAM.
-/
import Workspace.Algo.AlignJohnsonAut
import Workspace.Algo.AlignG1

/-!
# §14.1, Procedure Align, line 2 (iv) for Johnson schemes: `G₁ = ϕ⁻¹(Aut(X(x)))`

This is the Johnson half of `Workspace/Algo/AlignG1.lean`, with the same three steps:

1. generators of `Aut(X(x))` (`Algo.alignJAutGens`, `Workspace/Algo/AlignJohnsonAut.lean`);
2. generators of `Aut(X(x)) ∩ G^ϕ`.  The giant `G^ϕ` is `S(Γ)` or `A(Γ)`, and which one it
   is, is decided by `Algo.topAllEven`: in the alternating case the even part is taken
   (`Algo.rawEvenGens`);
3. the preimage, `Algo.actLiftGens`, shortened by `Algo.tidyGens`.

## Main definitions

* `Algo.alignJAutGensK` — generators of `Aut(X(x)) ∩ G^ϕ`;
* `Algo.alignJG1` — **line 2 (iv)** for Johnson schemes.

## Main results

* `Algo.decGroup_alignJAutGensK` — `decGroup m (alignJAutGensK …) = Aut(X(x)) ⊓ G^ϕ`;
* `Algo.decGroup_alignJG1` — **`decGroup n (alignJG1 …) = ϕ⁻¹(Aut(X(x)))`**;
* `Algo.alignJG1_image` — **Eq. (70), second clause**: the image of the computed `G₁` is
  `Aut(X(x)) ∩ G^ϕ`;
* `Algo.alignJG1_wf` — well formed, at most `n²` generators;
* `Algo.polyFun_alignJG1` — **the running time**.

No axiom, no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

/-- §14.1, line 2 (iv).  **Generators of `Aut(X(x)) ∩ G^ϕ`** for a Johnson scheme: the
generators of `Aut(X(x))`, and their even part when the giant `G^ϕ` is the alternating
group. -/
def alignJAutGensK (p : RawAction × RawJohnson) : RawGens :=
  if topAllEven p.1 then rawEvenGens (alignJAutGens (p.1.2.1, p.2))
  else alignJAutGens (p.1.2.1, p.2)

/-- §14.1, **line 2 (iv)**: `G₁ = ϕ⁻¹(Aut(X(x)))`, in the Johnson case. -/
def alignJG1 (p : RawAction × RawJohnson) : RawGens :=
  tidyGens (p.1.1.1, actLiftGens (p.1, alignJAutGensK p))

section Spec

variable {n m ms ts : ℕ} {dom gdom : List ℕ} {gens : List (Perm (Fin n))}
  {imgs : List (Perm (Fin m))} {r : RawJohnson}

theorem alignJAutGensK_wf {p : RawAction} (hm : p.2.1.length = m)
    (h : RawJohnson.WF m ms ts r) : RawGens.WF m (alignJAutGensK (p, r)) := by
  show RawGens.WF m (if topAllEven p then _ else _)
  split
  · exact rawEvenGens_wf (alignJAutGens_wf hm h)
  · exact alignJAutGens_wf hm h

/-- §14.1, line 2 (iv).  **The computed list generates `Aut(X(x)) ∩ G^ϕ`** for a Johnson
scheme. -/
theorem decGroup_alignJAutGensK {ϕ : genGroup gens →* Perm (Fin m)} (hI : ImgsOf gens imgs ϕ)
    (hgiant : Babai.IsGiantRep ϕ) (hm : gdom.length = m) (h : RawJohnson.WF m ms ts r) :
    decGroup m
        (alignJAutGensK (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), r)) =
      Babai.structAut (decJohnson m r) ⊓ ϕ.range := by
  by_cases hc : topAllEven ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))) = true
  · have hrange : ϕ.range = alternatingGroup (Fin m) :=
      le_antisymm ((topAllEven_spec dom gdom hI).1 hc) hgiant
    show decGroup m (if topAllEven ((dom, gens.map (encPerm n)),
      (gdom, imgs.map (encPerm m))) = true then _ else _) = _
    rw [if_pos hc, decGroup_rawEvenGens (alignJAutGens_wf hm h),
      decGroup_alignJAutGens hm h, hrange]
  · have hnot : ¬ ϕ.range ≤ alternatingGroup (Fin m) :=
      fun hh => hc ((topAllEven_spec dom gdom hI).2 hh)
    have hrange : ϕ.range = ⊤ := by
      rcases (Babai.isGiant_iff_alternating_le ϕ.range).2 hgiant with h1 | h1
      · exact h1
      · exact absurd (le_of_eq h1) hnot
    show decGroup m (if topAllEven ((dom, gens.map (encPerm n)),
      (gdom, imgs.map (encPerm m))) = true then _ else _) = _
    rw [if_neg hc, decGroup_alignJAutGens hm h, hrange, inf_top_eq]

/-- §14.1, **line 2 (iv)** for Johnson schemes: the computed generators describe
`G₁ = ϕ⁻¹(Aut(X(x)))`. -/
theorem decGroup_alignJG1 {ϕ : genGroup gens →* Perm (Fin m)} (hd : dom.length = n)
    (hm : gdom.length = m) (hI : ImgsOf gens imgs ϕ) (hgiant : Babai.IsGiantRep ϕ)
    (h : RawJohnson.WF m ms ts r) :
    decGroup n (alignJG1 (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), r)) =
      Babai.preimageSubgroup ϕ (Babai.structAut (decJohnson m r)) := by
  have hts : RawGens.WF m
      (alignJAutGensK (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), r)) :=
    alignJAutGensK_wf hm h
  have htop := decGroup_alignJAutGensK (dom := dom) (gdom := gdom) hI hgiant hm h
  have hsub : genGroup
      ((alignJAutGensK (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), r)).map
        (decPerm m)) ≤ ϕ.range := by
    change decGroup m _ ≤ _
    rw [htop]
    exact fun _ hx => hx.2
  have hcr : Subgroup.comap ϕ ϕ.range = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact Subgroup.mem_comap.2 ⟨g, rfl⟩
  rw [alignJG1, decGroup_tidyGens hd]
  change decGroup n (actLiftGens (_, alignJAutGensK (_, r))) = _
  conv_lhs => rw [← map_encPerm_decPerm hts]
  rw [decGroup_actLiftGens hd hm hI _ hsub]
  change (Subgroup.comap ϕ (decGroup m (alignJAutGensK (_, r)))).map _ = _
  rw [htop, Subgroup.comap_inf, hcr, inf_top_eq]
  rfl

/-- The answer uses at most `n²` well-formed generators. -/
theorem alignJG1_wf {p : RawAction × RawJohnson} (hd : p.1.1.1.length = n) :
    RawGens.WF n (alignJG1 p) ∧ (alignJG1 p).length ≤ n * n :=
  ⟨wf_tidyGens hd _, length_tidyGens hd _⟩

/-! ### Against Eq. (70) -/

variable {A : Type*} {X : (Fin n → A) → Babai.ColStruct (Fin m) ℕ} {x : Fin n → A}

/-- §14.1, **line 2 (iv)** for Johnson schemes: the computed group is the `G₁` of
Eq. (70). -/
theorem alignJG1_eq_G1 {ϕ : genGroup gens →* Perm (Fin m)} (hd : dom.length = n)
    (hm : gdom.length = m) (hI : ImgsOf gens imgs ϕ) (hgiant : Babai.IsGiantRep ϕ)
    (h : RawJohnson.WF m ms ts r) (hXx : X x = decJohnson m r) :
    decGroup n (alignJG1 (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), r)) =
      Babai.preimageSubgroup ϕ (Babai.structAut (X x)) := by
  rw [hXx]
  exact decGroup_alignJG1 hd hm hI hgiant h

/-- §14.1, **Eq. (70), second clause** for the computed `G₁`: `G₁^ϕ = Aut(X(x)) ∩ G^ϕ`.
(The printed clause `G₁^ϕ = Aut(X(x))` is false; see `Babai.not_Align_G1_image_as_printed`
and the corrected paper.) -/
theorem alignJG1_image {ϕ : genGroup gens →* Perm (Fin m)} (hd : dom.length = n)
    (hm : gdom.length = m) (hI : ImgsOf gens imgs ϕ) (hgiant : Babai.IsGiantRep ϕ)
    (h : RawJohnson.WF m ms ts r) (hXx : X x = decJohnson m r) :
    Babai.homImage ϕ
        ((decGroup n (alignJG1 (((dom, gens.map (encPerm n)),
          (gdom, imgs.map (encPerm m))), r)) : Subgroup (Perm (Fin n))) :
            Set (Perm (Fin n))) =
      (Babai.structAut (Γ := Fin m) (X x) : Set (Perm (Fin m))) ∩
        (ϕ.range : Set (Perm (Fin m))) := by
  rw [alignJG1_eq_G1 hd hm hI hgiant h hXx]
  exact Babai.Align_G1_image ϕ x

end Spec

/-! ## The running time -/

theorem polyFun_alignJAutGensK : PolyFun alignJAutGensK := by
  have htest : PolyFun (fun p : RawAction × RawJohnson => topAllEven p.1) :=
    polyFun_fst.comp polyFun_topAllEven
  have hA : PolyFun (fun p : RawAction × RawJohnson => alignJAutGens (p.1.2.1, p.2)) :=
    ((((polyFun_fst.comp polyFun_snd).comp polyFun_fst)).pair polyFun_snd).comp
      polyFun_alignJAutGens
  exact (PolyFun.ite htest (hA.comp polyFun_rawEvenGens) hA).of_eq (fun _ => rfl)

/-- §14.1, line 2 (iv) for Johnson schemes **runs in polynomial time**. -/
theorem polyFun_alignJG1 : PolyFun alignJG1 :=
  ((((polyFun_fst.comp polyFun_fst).comp polyFun_fst)).pair
    ((polyFun_fst.pair polyFun_alignJAutGensK).comp polyFun_actLiftGens)).comp polyFun_tidyGens

end Algo
