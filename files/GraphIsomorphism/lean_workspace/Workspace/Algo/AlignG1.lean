/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align (§14.1), line 2 (iv) — the group
`G₁ = ϕ⁻¹(Aut(X(x)))`, on the unit-cost RAM.
-/
import Workspace.Algo.AlignAut
import Workspace.Algo.AlignAutEven

/-!
# §14.1, Procedure Align, line 2 (iv): `G₁ = ϕ⁻¹(Aut(X(x)))`

> 2. Else, let
>    ...
>    (iv) `G₁ = ϕ⁻¹(Aut(X(x)))`

The input is the action `(G, ϕ)` as an `Algo.RawAction` and the colored partition `X(x)` as
an `Algo.RawColPart`.  Three steps:

1. generators of `Aut(X(x))` (`Algo.cpAutGens`, `Workspace/Algo/AlignAut.lean`);
2. generators of `Aut(X(x)) ∩ G^ϕ`.  The giant `G^ϕ` is `S(Γ)` or `A(Γ)`
   (`Babai.IsGiantRep`), and which one it is, is decided by `Algo.topAllEven`: in the
   alternating case the even part is taken (`Algo.rawEvenGens`), in the symmetric case
   nothing is done.  The intersection has to be taken **before** the lift, because
   `Algo.decGroup_actLiftGens` asks for generators of a subgroup of `ϕ.range`;
3. the preimage, `Algo.actLiftGens` (lifts of the generators together with generators of the
   kernel of `ϕ`), shortened by `Algo.tidyGens`.

The answer is the group `G₁` of Eq. (70), whose image is `Aut(X(x)) ∩ G^ϕ`
(`Babai.Align_G1_image`; the printed clause `G₁^ϕ = Aut(X(x))` is false).

## Main definitions

* `Algo.alignAutGens` — generators of `Aut(X(x)) ∩ G^ϕ`;
* `Algo.alignG1` — **line 2 (iv)**.

## Main results

* `Algo.decGroup_alignAutGens` — `decGroup m (alignAutGens …) = Aut(X(x)) ⊓ G^ϕ`;
* `Algo.decGroup_alignG1` — **`decGroup n (alignG1 …) = ϕ⁻¹(Aut(X(x)))`**;
* `Algo.alignG1_image` — **Eq. (70), second clause**: the image of the computed `G₁` is
  `Aut(X(x)) ∩ G^ϕ`;
* `Algo.alignG1_wf` — well formed, at most `n²` generators;
* `Algo.polyFun_alignG1` — **the running time**.

No axiom, no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

/-- §14.1, line 2 (iv).  **Generators of `Aut(X(x)) ∩ G^ϕ`**: the generators of `Aut(X(x))`,
and their even part when the giant `G^ϕ` is the alternating group. -/
def alignAutGens (p : RawAction × RawColPart) : RawGens :=
  if topAllEven p.1 then rawEvenGens (cpAutGens p.2) else cpAutGens p.2

/-- §14.1, **line 2 (iv)**: `G₁ = ϕ⁻¹(Aut(X(x)))`, in the colored-partition case. -/
def alignG1 (p : RawAction × RawColPart) : RawGens :=
  tidyGens (p.1.1.1, actLiftGens (p.1, alignAutGens p))

section Spec

variable {n m : ℕ} {dom gdom : List ℕ} {gens : List (Perm (Fin n))}
  {imgs : List (Perm (Fin m))} {P : RawColPart}

theorem alignAutGens_wf {p : RawAction} (hP : P.1.length = m) :
    RawGens.WF m (alignAutGens (p, P)) := by
  rw [alignAutGens]
  split
  · exact rawEvenGens_wf (cpAutGens_wf hP)
  · exact cpAutGens_wf hP

/-- §14.1, line 2 (iv).  **The computed list generates `Aut(X(x)) ∩ G^ϕ`.** -/
theorem decGroup_alignAutGens {ϕ : genGroup gens →* Perm (Fin m)} (hI : ImgsOf gens imgs ϕ)
    (hgiant : Babai.IsGiantRep ϕ) (hP : P.1.length = m) :
    decGroup m
        (alignAutGens (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), P)) =
      Babai.structAut (decColStruct m P) ⊓ ϕ.range := by
  by_cases h : topAllEven ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))) = true
  · have hrange : ϕ.range = alternatingGroup (Fin m) :=
      le_antisymm ((topAllEven_spec dom gdom hI).1 h) hgiant
    show decGroup m (if topAllEven ((dom, gens.map (encPerm n)),
      (gdom, imgs.map (encPerm m))) = true then _ else _) = _
    rw [if_pos h, decGroup_rawEvenGens (cpAutGens_wf hP), decGroup_cpAutGens hP, hrange]
  · have hnot : ¬ ϕ.range ≤ alternatingGroup (Fin m) :=
      fun hh => h ((topAllEven_spec dom gdom hI).2 hh)
    have hrange : ϕ.range = ⊤ := by
      rcases (Babai.isGiant_iff_alternating_le ϕ.range).2 hgiant with h1 | h1
      · exact h1
      · exact absurd (le_of_eq h1) hnot
    show decGroup m (if topAllEven ((dom, gens.map (encPerm n)),
      (gdom, imgs.map (encPerm m))) = true then _ else _) = _
    rw [if_neg h, decGroup_cpAutGens hP, hrange, inf_top_eq]

/-- §14.1, **line 2 (iv)**: the computed generators describe `G₁ = ϕ⁻¹(Aut(X(x)))`. -/
theorem decGroup_alignG1 {ϕ : genGroup gens →* Perm (Fin m)} (hd : dom.length = n)
    (hm : gdom.length = m) (hI : ImgsOf gens imgs ϕ) (hgiant : Babai.IsGiantRep ϕ)
    (hP : P.1.length = m) :
    decGroup n (alignG1 (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), P)) =
      Babai.preimageSubgroup ϕ (Babai.structAut (decColStruct m P)) := by
  have hts : RawGens.WF m
      (alignAutGens (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), P)) :=
    alignAutGens_wf hP
  have htop := decGroup_alignAutGens (dom := dom) (gdom := gdom) hI hgiant hP
  have hsub : genGroup
      ((alignAutGens (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), P)).map
        (decPerm m)) ≤ ϕ.range := by
    change decGroup m _ ≤ _
    rw [htop]
    exact fun _ hx => hx.2
  have hcr : Subgroup.comap ϕ ϕ.range = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact Subgroup.mem_comap.2 ⟨g, rfl⟩
  rw [alignG1, decGroup_tidyGens hd]
  change decGroup n (actLiftGens (_, alignAutGens (_, P))) = _
  conv_lhs => rw [← map_encPerm_decPerm hts]
  rw [decGroup_actLiftGens hd hm hI _ hsub]
  change (Subgroup.comap ϕ (decGroup m (alignAutGens (_, P)))).map _ = _
  rw [htop, Subgroup.comap_inf, hcr, inf_top_eq]
  rfl

/-- The answer uses at most `n²` well-formed generators. -/
theorem alignG1_wf {p : RawAction × RawColPart} (hd : p.1.1.1.length = n) :
    RawGens.WF n (alignG1 p) ∧ (alignG1 p).length ≤ n * n :=
  ⟨wf_tidyGens hd _, length_tidyGens hd _⟩

/-! ### Against Eq. (70) -/

variable {A : Type*} {X : (Fin n → A) → Babai.ColStruct (Fin m) ℕ} {x : Fin n → A}

/-- §14.1, **line 2 (iv)**: the computed group is the `G₁` of Eq. (70). -/
theorem alignG1_eq_G1 {ϕ : genGroup gens →* Perm (Fin m)} (hd : dom.length = n)
    (hm : gdom.length = m) (hI : ImgsOf gens imgs ϕ) (hgiant : Babai.IsGiantRep ϕ)
    (hP : P.1.length = m) (hXx : X x = decColStruct m P) :
    decGroup n (alignG1 (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), P)) =
      Babai.preimageSubgroup ϕ (Babai.structAut (X x)) := by
  rw [hXx]
  exact decGroup_alignG1 hd hm hI hgiant hP

/-- §14.1, **Eq. (70), second clause** for the computed `G₁`: `G₁^ϕ = Aut(X(x)) ∩ G^ϕ`.
(The printed clause `G₁^ϕ = Aut(X(x))` is false; see `Babai.not_Align_G1_image_as_printed`
and the corrected paper.) -/
theorem alignG1_image {ϕ : genGroup gens →* Perm (Fin m)} (hd : dom.length = n)
    (hm : gdom.length = m) (hI : ImgsOf gens imgs ϕ) (hgiant : Babai.IsGiantRep ϕ)
    (hP : P.1.length = m) (hXx : X x = decColStruct m P) :
    Babai.homImage ϕ
        ((decGroup n (alignG1 (((dom, gens.map (encPerm n)),
          (gdom, imgs.map (encPerm m))), P)) : Subgroup (Perm (Fin n))) :
            Set (Perm (Fin n))) =
      (Babai.structAut (Γ := Fin m) (X x) : Set (Perm (Fin m))) ∩
        (ϕ.range : Set (Perm (Fin m))) := by
  rw [alignG1_eq_G1 hd hm hI hgiant hP hXx]
  exact Babai.Align_G1_image ϕ x

end Spec

/-! ## The running time -/

theorem polyFun_alignAutGens : PolyFun alignAutGens := by
  have htest : PolyFun (fun p : RawAction × RawColPart => topAllEven p.1) :=
    polyFun_fst.comp polyFun_topAllEven
  have hA : PolyFun (fun p : RawAction × RawColPart => cpAutGens p.2) :=
    polyFun_snd.comp polyFun_cpAutGens
  exact (PolyFun.ite htest (hA.comp polyFun_rawEvenGens) hA).of_eq (fun _ => rfl)

/-- §14.1, line 2 (iv) **runs in polynomial time**. -/
theorem polyFun_alignG1 : PolyFun alignG1 :=
  ((((polyFun_fst.comp polyFun_fst).comp polyFun_fst)).pair
    ((polyFun_fst.pair polyFun_alignAutGens).comp polyFun_actLiftGens)).comp polyFun_tidyGens

end Algo
