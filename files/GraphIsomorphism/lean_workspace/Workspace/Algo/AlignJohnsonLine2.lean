/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align (§14.1), line 2 (i) for Johnson schemes — the
aligning permutation with the parity correction.
-/
import Workspace.Algo.AlignJohnsonTest
import Workspace.Algo.AlignJohnsonParity
import Workspace.Algo.AlignParity

/-!
# §14.1, Procedure Align, line 2 (i) for Johnson schemes

> 1. If `X(x)` and `X(y)` are not `G^ϕ`-isomorphic then reject isomorphism, exit.
> 2. Else, let (i) `σ̄ ∈ Iso_{G^ϕ}(X(x), X(y))`

This is the Johnson analogue of `Algo.alignColPartIso` and `Algo.Align_line2_colPart`
(`Workspace/Algo/AlignParity.lean`), with the same statement shape.  The three ingredients
are already proved:

* `Algo.alignJTest` decides line 1 (`Workspace/Algo/AlignJohnsonTest.lean`);
* `Algo.alignJPerm` is the `σ̄` for `K = S(Γ)` (`Workspace/Algo/AlignJohnsonIso.lean`);
* `Algo.alignJHasOddAut` and `Algo.alignJOddAut` are the parity correction
  (`Workspace/Algo/AlignJohnsonParity.lean`).

## Main definitions

* `Algo.alignJIso` — **line 2 (i) with the parity correction** for Johnson schemes.

## Main results

* `Algo.alignJIso_some`, `Algo.alignJIso_eq_none` — **the routine decides
  `Iso_K(X(x), X(y)) ≠ ∅` for `K = S(Γ)` and for `K = A(Γ)`, and returns a witness**;
* `Algo.alignJIso_mem_structIso`, `Algo.alignJIso_none_structIso`,
  `Algo.alignJIso_none_structIso_univ` — the same against the `S(Γ)`-set the procedure acts
  on;
* `Algo.Align_line2_johnson` — **Eq. (70)** (`Babai.Align_eq70`, `Babai.Align_G1_image`) for
  a lift of the computed `σ̄`;
* `Algo.polyFun_alignJIso` — **the running time**.

No axiom, no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)
open scoped Pointwise

/-- §14.1, **line 2 (i)**, in the Johnson case.

The Boolean says which giant `G^ϕ` is: `true` for the alternating group `A(Γ)`, `false` for
the symmetric group `S(Γ)`.  The list is the domain witness of `Γ`, whose length is `m`.  The
answer is a `σ̄ ∈ Iso_{G^ϕ}(X(x), X(y))`, or `none` when there is none — which is the reject
exit of line 1. -/
def alignJIso (p : Bool × (List ℕ × (RawJohnson × RawJohnson))) : Option RawPerm :=
  if alignJTest p.2.2 then
    (if p.1 = false then some (alignJPerm p.2)
      else if topEven (alignJPerm p.2) then some (alignJPerm p.2)
      else if alignJHasOddAut (p.2.1, p.2.2.1) then
        some (rawMul (alignJPerm p.2, alignJOddAut (p.2.1, p.2.2.1)))
      else none)
  else none

section Spec

variable {m : ℕ} {dom : List ℕ} {r r' : RawJohnson} {g : Bool} {s : RawPerm}

/-- §14.1, **line 2 (i)**: the answer is a well-formed permutation of `Γ`, it carries the
first Johnson structure to the second, and in the alternating case it is even. -/
theorem alignJIso_some (hd : dom.length = m) (h : RawJohnson.WF m (rawJDeg r) r.2.1 r)
    (h' : RawJohnson.WF m (rawJDeg r') r'.2.1 r')
    (hs : alignJIso (g, (dom, (r, r'))) = some s) :
    RawPerm.WF m s ∧ decPerm m s • decJohnson m r = decJohnson m r' ∧
      (g = true → Equiv.Perm.sign (decPerm m s) = 1) := by
  simp only [alignJIso] at hs
  by_cases htest : alignJTest (r, r') = true
  · rw [if_pos htest] at hs
    have h'' : RawJohnson.WF m (rawJDeg r) r.2.1 r' := alignJTest_wf_right h' htest
    have hwf : RawPerm.WF m (alignJPerm (dom, (r, r'))) := alignJPerm_wf hd h h''
    have hsmul : decPerm m (alignJPerm (dom, (r, r'))) • decJohnson m r = decJohnson m r' :=
      alignJPerm_smul hd h h''
    by_cases hg : g = false
    · rw [if_pos hg] at hs
      obtain rfl : s = alignJPerm (dom, (r, r')) := (Option.some.inj hs).symm
      exact ⟨hwf, hsmul, fun hgt => absurd (hg ▸ hgt) (by simp)⟩
    · rw [if_neg hg] at hs
      by_cases heven : topEven (alignJPerm (dom, (r, r'))) = true
      · rw [if_pos heven] at hs
        obtain rfl : s = alignJPerm (dom, (r, r')) := (Option.some.inj hs).symm
        exact ⟨hwf, hsmul, fun _ =>
          (Equiv.Perm.mem_alternatingGroup).1 ((topEven_of_wf hwf).1 heven)⟩
      · rw [if_neg heven] at hs
        by_cases hodd : alignJHasOddAut (dom, r) = true
        · rw [if_pos hodd] at hs
          obtain ⟨hwfA, hautA, hsignA⟩ := alignJOddAut_spec hd h hodd
          obtain rfl : s = rawMul (alignJPerm (dom, (r, r')), alignJOddAut (dom, r)) :=
            (Option.some.inj hs).symm
          have hwfs : RawPerm.WF m (rawMul (alignJPerm (dom, (r, r')), alignJOddAut (dom, r))) :=
            wf_rawMul hwf hwfA
          have hdec : decPerm m (rawMul (alignJPerm (dom, (r, r')), alignJOddAut (dom, r)))
              = decPerm m (alignJPerm (dom, (r, r'))) * decPerm m (alignJOddAut (dom, r)) := by
            rw [rawMul_of_wf hwf hwfA, decPerm_encPerm]
          have hsignS : Equiv.Perm.sign (decPerm m (alignJPerm (dom, (r, r')))) = -1 := by
            rcases Int.units_eq_one_or
              (Equiv.Perm.sign (decPerm m (alignJPerm (dom, (r, r'))))) with hh | hh
            · exact absurd ((topEven_of_wf hwf).2
                ((Equiv.Perm.mem_alternatingGroup).2 hh)) heven
            · exact hh
          refine ⟨hwfs, ?_, fun _ => ?_⟩
          · rw [hdec, mul_smul, Babai.mem_structAut.1 hautA, hsmul]
          · rw [hdec, map_mul, hsignA, hsignS]
            decide
        · rw [if_neg hodd] at hs
          exact absurd hs (by simp)
  · rw [if_neg htest] at hs
    exact absurd hs (by simp)

/-- §14.1, **line 1 / line 2 (i)**: when the routine reports `none` there is no isomorphism
at all in the giant `G^ϕ` — every isomorphism of the two Johnson structures is odd, and the
giant is the alternating group. -/
theorem alignJIso_eq_none (hd : dom.length = m) (h : RawJohnson.WF m (rawJDeg r) r.2.1 r)
    (h' : RawJohnson.WF m (rawJDeg r') r'.2.1 r')
    (hs : alignJIso (g, (dom, (r, r'))) = none) (f : Perm (Fin m))
    (hf : f • decJohnson m r = decJohnson m r') :
    g = true ∧ Equiv.Perm.sign f = -1 := by
  simp only [alignJIso] at hs
  have htest : alignJTest (r, r') = true := (alignJTest_iff h h').2 ⟨f, hf⟩
  rw [if_pos htest] at hs
  have h'' : RawJohnson.WF m (rawJDeg r) r.2.1 r' := alignJTest_wf_right h' htest
  have hg : ¬ (g = false) := by
    intro hg; rw [if_pos hg] at hs; exact absurd hs (by simp)
  have hgt : g = true := by cases g <;> simp_all
  rw [if_neg hg] at hs
  have heven : ¬ (topEven (alignJPerm (dom, (r, r'))) = true) := by
    intro hh; rw [if_pos hh] at hs; exact absurd hs (by simp)
  rw [if_neg heven] at hs
  have hodd : ¬ (alignJHasOddAut (dom, r) = true) := by
    intro hh; rw [if_pos hh] at hs; exact absurd hs (by simp)
  rw [if_neg hodd] at hs
  refine ⟨hgt, ?_⟩
  have hwf : RawPerm.WF m (alignJPerm (dom, (r, r'))) := alignJPerm_wf hd h h''
  have hsmul : decPerm m (alignJPerm (dom, (r, r'))) • decJohnson m r = decJohnson m r' :=
    alignJPerm_smul hd h h''
  have hsignS : Equiv.Perm.sign (decPerm m (alignJPerm (dom, (r, r')))) = -1 := by
    rcases Int.units_eq_one_or
      (Equiv.Perm.sign (decPerm m (alignJPerm (dom, (r, r'))))) with hh | hh
    · exact absurd ((topEven_of_wf hwf).2 ((Equiv.Perm.mem_alternatingGroup).2 hh)) heven
    · exact hh
  rcases Int.units_eq_one_or (Equiv.Perm.sign f) with hh | hh
  · exfalso
    refine hodd ((alignJHasOddAut_iff hd h).2
      ⟨f⁻¹ * decPerm m (alignJPerm (dom, (r, r'))), ?_, ?_⟩)
    · rw [Babai.mem_structAut, mul_smul, hsmul, ← hf, inv_smul_smul]
    · rw [map_mul, map_inv, hh, hsignS]
      decide
  · exact hh

/-! ### Against the `S(Γ)`-set the procedure acts on -/

/-- §14.1, **line 2 (i)**: the answer is a `σ̄ ∈ Iso_{G^ϕ}(X(x), X(y))`.

`Babai.IsGiantRep ϕ` (`A(Γ) ≤ G^ϕ`) is the standing hypothesis of Sec. 14, and the flag
`true` says that `G^ϕ` is the alternating group, so an even answer lies in `G^ϕ` in either
case. -/
theorem alignJIso_mem_structIso {Ω : Type*} {G : Subgroup (Perm Ω)}
    (ϕ : G →* Perm (Fin m)) (hϕ : Babai.IsGiantRep ϕ) (hd : dom.length = m)
    (h : RawJohnson.WF m (rawJDeg r) r.2.1 r) (h' : RawJohnson.WF m (rawJDeg r') r'.2.1 r')
    (hs : alignJIso (true, (dom, (r, r'))) = some s) :
    decPerm m s ∈
      Babai.structIso (ϕ.range : Set (Perm (Fin m))) (decJohnson m r) (decJohnson m r') := by
  obtain ⟨-, hsmul, hsign⟩ := alignJIso_some hd h h' hs
  exact ⟨hϕ ((Equiv.Perm.mem_alternatingGroup).2 (hsign rfl)), hsmul⟩

/-- §14.1, **line 2 (i)** for `G^ϕ = S(Γ)`: the answer is an isomorphism, with no condition
on the group. -/
theorem alignJIso_false_mem_structIso (hd : dom.length = m)
    (h : RawJohnson.WF m (rawJDeg r) r.2.1 r) (h' : RawJohnson.WF m (rawJDeg r') r'.2.1 r')
    (hs : alignJIso (false, (dom, (r, r'))) = some s) (K : Set (Perm (Fin m)))
    (hK : Set.univ ⊆ K) :
    decPerm m s ∈ Babai.structIso K (decJohnson m r) (decJohnson m r') := by
  obtain ⟨-, hsmul, -⟩ := alignJIso_some hd h h' hs
  exact ⟨hK (Set.mem_univ _), hsmul⟩

/-- §14.1, **line 1**, the reject exit in the alternating case:
`Iso_{A(Γ)}(X(x), X(y)) = ∅`.  This is the case the printed Eq. (70) overlooks; see
`Babai.Align_G1_image` and the corrected paper. -/
theorem alignJIso_none_structIso (hd : dom.length = m)
    (h : RawJohnson.WF m (rawJDeg r) r.2.1 r) (h' : RawJohnson.WF m (rawJDeg r') r'.2.1 r')
    (hs : alignJIso (true, (dom, (r, r'))) = none) :
    Babai.structIso ((alternatingGroup (Fin m) : Subgroup (Perm (Fin m))) :
      Set (Perm (Fin m))) (decJohnson m r) (decJohnson m r') = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro f ⟨hfA, hf⟩
  obtain ⟨-, hsign⟩ := alignJIso_eq_none hd h h' hs f hf
  rw [(Equiv.Perm.mem_alternatingGroup).1 hfA] at hsign
  exact absurd hsign (by decide)

/-- §14.1, **line 1**, the reject exit in the symmetric case:
`Iso_{S(Γ)}(X(x), X(y)) = ∅`. -/
theorem alignJIso_none_structIso_univ (hd : dom.length = m)
    (h : RawJohnson.WF m (rawJDeg r) r.2.1 r) (h' : RawJohnson.WF m (rawJDeg r') r'.2.1 r')
    (hs : alignJIso (false, (dom, (r, r'))) = none) :
    Babai.structIso (Set.univ : Set (Perm (Fin m))) (decJohnson m r)
      (decJohnson m r') = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro f ⟨-, hf⟩
  obtain ⟨hgt, -⟩ := alignJIso_eq_none hd h h' hs f hf
  exact absurd hgt (by simp)

end Spec

/-! ### Eq. (70) for the computed `σ̄` -/

/-- §14.1, **Eq. (70)** for the `σ̄` computed by `Algo.alignJIso`: with `y' = y^{σ⁻¹}` and
`G₁ = ϕ⁻¹(Aut(X(x)))`,

* `Iso_G(x,y) = Iso_{G₁}(x,y')σ`  (`Babai.Align_eq70`), and
* `G₁^ϕ = Aut(X(x)) ∩ G^ϕ`  (`Babai.Align_G1_image`, the corrected second clause). -/
theorem Align_line2_johnson {Ω : Type*} {A : Type*} {m : ℕ} {G : Subgroup (Perm Ω)}
    {ϕ : G →* Perm (Fin m)} {X : (Ω → A) → Babai.ColStruct (Fin m) ℕ}
    (hcan : Babai.IsCanonicalStructure ϕ X) (x y : Ω → A) {dom : List ℕ}
    {r r' : RawJohnson} {g : Bool} {s : RawPerm} (hd : dom.length = m)
    (h : RawJohnson.WF m (rawJDeg r) r.2.1 r) (h' : RawJohnson.WF m (rawJDeg r') r'.2.1 r')
    (hXx : X x = decJohnson m r) (hXy : X y = decJohnson m r')
    (hs : alignJIso (g, (dom, (r, r'))) = some s) (σ : G) (hσ : ϕ σ = decPerm m s) :
    Babai.strIso (G : Set (Perm Ω)) x y =
      (σ : Perm Ω) • Babai.strIso
        ((Babai.preimageSubgroup ϕ (Babai.structAut (X x)) : Subgroup (Perm Ω)) :
          Set (Perm Ω)) x (Babai.strAct y (σ : Perm Ω)⁻¹) ∧
      Babai.homImage ϕ
          ((Babai.preimageSubgroup ϕ (Babai.structAut (X x)) : Subgroup (Perm Ω)) :
            Set (Perm Ω)) =
        (Babai.structAut (Γ := Fin m) (X x) : Set (Perm (Fin m))) ∩
          (ϕ.range : Set (Perm (Fin m))) := by
  obtain ⟨-, hsmul, -⟩ := alignJIso_some hd h h' hs
  have hsm : ϕ σ • X x = X y := by rw [hXx, hXy, hσ]; exact hsmul
  exact ⟨Babai.Align_eq70 hcan x y σ hsm, Babai.Align_G1_image ϕ x⟩

/-! ## The running time -/

/-- §14.1, line 2 (i) with the parity correction, in the Johnson case, **runs in polynomial
time**. -/
theorem polyFun_alignJIso : PolyFun alignJIso := by
  have hperm : PolyFun (fun p : Bool × (List ℕ × (RawJohnson × RawJohnson)) =>
      alignJPerm p.2) := polyFun_snd.comp polyFun_alignJPerm
  have hr : PolyFun (fun p : Bool × (List ℕ × (RawJohnson × RawJohnson)) =>
      (p.2.1, p.2.2.1)) :=
    (polyFun_snd.comp polyFun_fst).pair ((polyFun_snd.comp polyFun_snd).comp polyFun_fst)
  have htest : PolyFun (fun p : Bool × (List ℕ × (RawJohnson × RawJohnson)) =>
      alignJTest p.2.2) := (polyFun_snd.comp polyFun_snd).comp polyFun_alignJTest
  have hflag : PolyFun (fun p : Bool × (List ℕ × (RawJohnson × RawJohnson)) =>
      decide (p.1 = false)) := by
    refine (PolyFun.ite polyFun_fst (polyFun_const false) (polyFun_const true)).of_eq
      (fun p => ?_)
    cases hh : p.1 <;> simp [hh]
  have heven : PolyFun (fun p : Bool × (List ℕ × (RawJohnson × RawJohnson)) =>
      topEven (alignJPerm p.2)) := hperm.comp polyFun_topEven
  have hodd : PolyFun (fun p : Bool × (List ℕ × (RawJohnson × RawJohnson)) =>
      alignJHasOddAut (p.2.1, p.2.2.1)) := hr.comp polyFun_alignJHasOddAut
  have hmul : PolyFun (fun p : Bool × (List ℕ × (RawJohnson × RawJohnson)) =>
      rawMul (alignJPerm p.2, alignJOddAut (p.2.1, p.2.2.1))) :=
    (hperm.pair (hr.comp polyFun_alignJOddAut)).comp polyFun_rawMul
  refine (PolyFun.ite htest
    (PolyFun.ite hflag (hperm.comp polyFun_some)
      (PolyFun.ite heven (hperm.comp polyFun_some)
        (PolyFun.ite hodd (hmul.comp polyFun_some) polyFun_none)))
    polyFun_none).of_eq (fun p => ?_)
  rw [alignJIso]
  by_cases h1 : alignJTest p.2.2 = true
  · simp only [h1, if_true]
    by_cases h2 : p.1 = false
    · simp [h2]
    · simp only [h2, decide_false, Bool.false_eq_true, if_false]
      by_cases h3 : topEven (alignJPerm p.2) = true
      · simp [h3]
      · simp only [h3, Bool.false_eq_true, if_false]
        by_cases h4 : alignJHasOddAut (p.2.1, p.2.2.1) = true <;> simp [h4]
  · simp [h1]

end Algo
