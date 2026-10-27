/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align, lines 7–11 (§14.1), case 1 of the
repair — the group `ker ϕ*` on the machine, and its orbits in the dominant window.
-/
import Workspace.Algo.AlignDomWindows

/-!
# `ker ϕ*` on the machine

Line 8 of Procedure Align defines `ϕ* : G* → S(Γ*)`, the composition of `ϕ` with the natural
map `ψ : Aut(X') → S(Γ*)`. In case 1 of the repair (`m*` small) the round on the dominant
window is the strong descent to `ker ϕ*`, so the machine needs generators of `ker ϕ*`.

An element of `Aut(X')` is in `ker ψ` exactly when it fixes every point of `Γ*`:

* case (A) of line 7, an equipartition of `Δ_j`: `Γ*` is the set of blocks inside `Δ_j`, so
  `ker ψ` consists of the automorphisms that map every block inside `Δ_j` to itself;
* case (B), a Johnson scheme `Δ_j ≅ (Γ* choose t*)`: an automorphism fixes every `t*`-subset
  of `Γ*` exactly when it fixes `Δ_j` pointwise.

Both groups are the automorphism group of a colored partition of `Γ` (`Algo.alignKerPart`),
so `ker ϕ* = ϕ⁻¹(ker ψ)` has generators `Algo.alignG1` of that colored partition
(`Algo.alignKerGens`, `Algo.decGroup_alignKerGens`):

* in case (A) the points of `Δ_j` are recolored by their block, the other points keep their
  color, and the blocks stay;
* in case (B) the points of `Δ_j` get one color each and the other points one common color.

`Algo.alignKerOrbits` lists the orbits of `ker ϕ*` in the dominant window.

The identification of this group with the Master side's `kerSubgroup D.phis` depends on the
data `D` the Master side chooses (its `ψ` is a field of `Babai.AlignDominant`), so it is a
hypothesis of the users of this file.
-/

namespace Algo
open RAM RAM.Targets Babai Equiv MulAction

/-- Case (A): the new color of the point `u` of `Γ`. A point of the dominant class (label
`dc`) gets its block `(color, block label)`, tagged `1`; any other point keeps its color,
tagged `0`. -/
def alignKerColA (z : ((RawLab × ℕ) × RawColPart) × ℕ) : ℕ :=
  if labAt z.1.1.1 z.2 = z.1.1.2 then
    Nat.pair 1 (Nat.pair (labAt z.1.2.1 z.2) (labAt z.1.2.2 z.2))
  else Nat.pair 0 (labAt z.1.2.1 z.2)

/-- Case (B): the new color of the point `u` of `Γ`: `u + 1` on the dominant class, `0`
elsewhere. -/
def alignKerColB (z : (RawLab × ℕ) × ℕ) : ℕ :=
  if labAt z.1.1 z.2 = z.1.2 then z.2 + 1 else 0

/-- Case (A): the colored partition whose automorphisms are the automorphisms of `X'` that
map every block inside `Δ_j` to itself. The input is the labels of line 4 with the dominant
label, the points of `Γ` and the partition `X'`. -/
def alignKerPartA (p : (RawLab × ℕ) × (List ℕ × RawColPart)) : RawColPart :=
  ((rawOne p.2.1).map (fun u => alignKerColA ((p.1, p.2.2), u)),
    (rawOne p.2.1).map (fun u => labAt p.2.2.2 u))

/-- Case (B): the colored partition whose automorphisms fix `Δ_j` pointwise. -/
def alignKerPartB (p : (RawLab × ℕ) × List ℕ) : RawColPart :=
  ((rawOne p.2).map (fun u => alignKerColB (p.1, u)), (rawOne p.2).map (fun _ => 0))

/-- §14.1, line 8: **the colored partition of `ker ψ`** for the fixed version `X'`. -/
def alignKerPart (p : RawAction × RawAlignOutcome) : RawColPart :=
  p.2.1.elim
    (alignKerPartB (((alignRColorOf p).2, alignRDomColor (alignRColorOf p)), p.1.2.1))
    (fun P => alignKerPartA (((alignRColorOf p).2, alignRDomColor (alignRColorOf p)),
      (p.1.2.1, P)))

/-- §14.1, lines 8–11: **generators of `ker ϕ* = ϕ⁻¹(ker ψ)`**. -/
def alignKerGens (p : RawAction × RawAlignOutcome) : RawGens :=
  alignG1 (p.1, alignKerPart p)

/-- §14.1, lines 9–11, case 1 of the repair: **the orbits of `ker ϕ*` in the dominant
window**, in the order of the orbit routine. -/
def alignKerOrbits (p : RawAction × RawAlignOutcome) : List (List ℕ) :=
  winOrbits (alignKerGens p,
    alignRDomWindow (alignRColorOf p, alignRDomColor (alignRColorOf p)))

/-! ## What the machine computes -/

section Spec

variable {n m : ℕ} {A : RawAction} {ϕ : decGroup n A.1.2 →* Perm (Fin m)}

theorem alignKerPart_length {o : RawAlignOutcome} (hdm : A.2.1.length = m) :
    (alignKerPart (A, o)).1.length = m := by
  rcases o with ⟨_ | P, J⟩ <;> simp [alignKerPart, alignKerPartA, alignKerPartB, rawOne, hdm]

/-- The generators of `ker ϕ*` are permutations of `Ω`. -/
theorem alignKerGens_wf (hd : A.1.1.length = n) (o : RawAlignOutcome) :
    RawGens.WF n (alignKerGens (A, o)) :=
  (alignG1_wf (p := (A, alignKerPart (A, o))) hd).1

/-- §14.1, lines 8–11: **the machine's `ker ϕ*`** is the preimage under `ϕ` of the
automorphism group of the colored partition `Algo.alignKerPart`. -/
theorem decGroup_alignKerGens (hA : RawAction.WF n m A ϕ) (hgiant : IsGiantRep ϕ)
    (o : RawAlignOutcome) :
    decGroup n (alignKerGens (A, o)) =
      preimageSubgroup ϕ (structAut (decColStruct m (alignKerPart (A, o)))) :=
  decGroup_alignG1_raw hA hgiant (alignKerPart_length hA.2.1)

/-- The labels of the colored partition of case (B), read on `Fin m`. -/
theorem labAt_alignKerPartB (hdm : A.2.1.length = m) (lab : RawLab) (dc : ℕ) (u : Fin m) :
    labAt (alignKerPartB ((lab, dc), A.2.1)).1 u =
      if labAt lab u = dc then (u : ℕ) + 1 else 0 :=
  labAt_rawOne_map hdm _ u

/-- **Case (B), read**: an automorphism of the colored partition of case (B) is a permutation
of `Γ` that fixes every point of the dominant class, and conversely. -/
theorem mem_structAut_alignKerPartB (hdm : A.2.1.length = m) (lab : RawLab) (dc : ℕ)
    (f : Perm (Fin m)) :
    f ∈ structAut (decColStruct m (alignKerPartB ((lab, dc), A.2.1))) ↔
      ∀ u : Fin m, labAt lab u = dc → f u = u := by
  rw [mem_structAut, ← colPartIso_iff_smul]
  set P := alignKerPartB ((lab, dc), A.2.1) with hP
  have hcol : ∀ u : Fin m, labAt P.1 u = if labAt lab u = dc then (u : ℕ) + 1 else 0 :=
    labAt_alignKerPartB hdm lab dc
  have hcell : ∀ u : Fin m, labAt P.2 u = 0 := fun u => labAt_rawOne_map hdm _ u
  constructor
  · rintro ⟨hc, -⟩ u hu
    have h := hc u
    rw [hcol, hcol, if_pos hu] at h
    by_cases hfu : labAt lab (f u) = dc
    · rw [if_pos hfu] at h
      exact Fin.ext (by omega)
    · rw [if_neg hfu] at h
      omega
  · intro hfix
    -- the colors are preserved
    have hc : ∀ u : Fin m, labAt P.1 (f u) = labAt P.1 u := by
      intro u
      rw [hcol, hcol]
      by_cases hu : labAt lab u = dc
      · rw [hfix u hu, if_pos hu]
      · -- `f u` is not in the dominant class: otherwise `f` fixes it, so `f u = u`
        have hfu : ¬ labAt lab (f u) = dc := by
          intro h'
          have h2 := hfix (f u) h'
          have : f u = u := f.injective h2
          rw [this] at h'
          exact hu h'
        rw [if_neg hfu, if_neg hu]
    refine ⟨hc, fun u v => ?_⟩
    simp only [cellOf, hc, hcell]

end Spec

/-! ## Running time -/

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd
private theorem pelim {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → Option β}
    {g : α → γ} {h : β × α → γ} (hf : PolyFun f) (hg : PolyFun g) (hh : PolyFun h) :
    PolyFun (fun a => (f a).elim (g a) (fun b => h (b, a))) :=
  (hf.pair polyFun_id).comp (PolyFun.optionElim hg hh)

private theorem polyFun_natPair' : PolyFun (fun z : ℕ × ℕ => Nat.pair z.1 z.2) := by
  have hlt : PolyFun (fun z : ℕ × ℕ => decide (z.1 < z.2)) :=
    ((polyFun_fst.add (polyFun_const 1)).le polyFun_snd).of_eq (fun z => by simp)
  exact (PolyFun.ite hlt ((polyFun_snd.mul polyFun_snd).add polyFun_fst)
    (((polyFun_fst.mul polyFun_fst).add polyFun_fst).add polyFun_snd)).of_eq
      (fun z => by simp [Nat.pair])

theorem polyFun_alignKerColA : PolyFun alignKerColA := by
  have i : PolyFun (fun z : ((RawLab × ℕ) × RawColPart) × ℕ => z) := polyFun_id
  have hl : PolyFun (fun z : ((RawLab × ℕ) × RawColPart) × ℕ => labAt z.1.1.1 z.2) :=
    ((pfst (pfst (pfst i))).pair (psnd i)).comp polyFun_labAt
  have hc : PolyFun (fun z : ((RawLab × ℕ) × RawColPart) × ℕ => labAt z.1.2.1 z.2) :=
    ((pfst (psnd (pfst i))).pair (psnd i)).comp polyFun_labAt
  have hb : PolyFun (fun z : ((RawLab × ℕ) × RawColPart) × ℕ => labAt z.1.2.2 z.2) :=
    ((psnd (psnd (pfst i))).pair (psnd i)).comp polyFun_labAt
  have hin : PolyFun (fun z : ((RawLab × ℕ) × RawColPart) × ℕ =>
      Nat.pair 1 (Nat.pair (labAt z.1.2.1 z.2) (labAt z.1.2.2 z.2))) :=
    ((polyFun_const 1).pair ((hc.pair hb).comp polyFun_natPair')).comp polyFun_natPair'
  have hout : PolyFun (fun z : ((RawLab × ℕ) × RawColPart) × ℕ =>
      Nat.pair 0 (labAt z.1.2.1 z.2)) :=
    ((polyFun_const 0).pair hc).comp polyFun_natPair'
  exact (PolyFun.ite (hl.natEq (psnd (pfst (pfst i)))) hin hout).of_eq (fun z => by
    by_cases h : labAt z.1.1.1 z.2 = z.1.1.2 <;> simp [alignKerColA, h])

theorem polyFun_alignKerColB : PolyFun alignKerColB := by
  have i : PolyFun (fun z : (RawLab × ℕ) × ℕ => z) := polyFun_id
  have hl : PolyFun (fun z : (RawLab × ℕ) × ℕ => labAt z.1.1 z.2) :=
    ((pfst (pfst i)).pair (psnd i)).comp polyFun_labAt
  exact (PolyFun.ite (hl.natEq (psnd (pfst i))) ((psnd i).add (polyFun_const 1))
    (polyFun_const 0)).of_eq (fun z => by
      by_cases h : labAt z.1.1 z.2 = z.1.2 <;> simp [alignKerColB, h])

theorem polyFun_alignKerPartA : PolyFun alignKerPartA := by
  have i : PolyFun (fun p : (RawLab × ℕ) × (List ℕ × RawColPart) => p) := polyFun_id
  have hone := (pfst (psnd i)).comp polyFun_rawOne
  have h1 : PolyFun (fun p : (RawLab × ℕ) × (List ℕ × RawColPart) =>
      (rawOne p.2.1).map (fun u => alignKerColA ((p.1, p.2.2), u))) :=
    (((pfst i).pair (psnd (psnd i))).pair hone).comp (PolyFun.mapParam polyFun_alignKerColA)
  have h2 : PolyFun (fun p : (RawLab × ℕ) × (List ℕ × RawColPart) =>
      (rawOne p.2.1).map (fun u => labAt p.2.2.2 u)) :=
    ((psnd (psnd (psnd i))).pair hone).comp (PolyFun.mapParam polyFun_labAt)
  exact h1.pair h2

theorem polyFun_alignKerPartB : PolyFun alignKerPartB := by
  have i : PolyFun (fun p : (RawLab × ℕ) × List ℕ => p) := polyFun_id
  have hone := (psnd i).comp polyFun_rawOne
  have h1 : PolyFun (fun p : (RawLab × ℕ) × List ℕ =>
      (rawOne p.2).map (fun u => alignKerColB (p.1, u))) :=
    ((pfst i).pair hone).comp (PolyFun.mapParam polyFun_alignKerColB)
  have h2 : PolyFun (fun p : (RawLab × ℕ) × List ℕ => (rawOne p.2).map (fun _ => 0)) :=
    ((polyFun_const (0 : ℕ)).pair hone).comp (PolyFun.mapParam (f := fun _ : ℕ × ℕ => 0)
      (polyFun_const 0)) |>.of_eq (fun _ => rfl)
  exact h1.pair h2

set_option maxHeartbeats 1000000 in
theorem polyFun_alignKerPart : PolyFun alignKerPart := by
  let T := RawAction × RawAlignOutcome
  have i0 : PolyFun (fun p : T => p) := polyFun_id
  have hq : PolyFun (fun p : T => ((alignRColorOf p).2, alignRDomColor (alignRColorOf p))) :=
    (psnd polyFun_alignRColorOf).pair (polyFun_alignRColorOf.comp polyFun_alignRDomColor)
  have hB : PolyFun (fun p : T =>
      alignKerPartB (((alignRColorOf p).2, alignRDomColor (alignRColorOf p)), p.1.2.1)) :=
    (hq.pair (pfst (psnd (pfst i0)))).comp polyFun_alignKerPartB
  have i : PolyFun (fun r : RawColPart × T => r) := polyFun_id
  have hA : PolyFun (fun r : RawColPart × T =>
      alignKerPartA (((alignRColorOf r.2).2, alignRDomColor (alignRColorOf r.2)),
        (r.2.1.2.1, r.1))) :=
    (((psnd i).comp hq).pair ((pfst (psnd (pfst (psnd i)))).pair (pfst i))).comp
      polyFun_alignKerPartA
  exact pelim (pfst (psnd i0)) hB hA

theorem polyFun_alignKerGens : PolyFun alignKerGens :=
  ((pfst polyFun_id).pair polyFun_alignKerPart).comp polyFun_alignG1

theorem polyFun_alignKerOrbits : PolyFun alignKerOrbits := by
  have hq := polyFun_alignRColorOf
  have hwin : PolyFun (fun p : RawAction × RawAlignOutcome =>
      alignRDomWindow (alignRColorOf p, alignRDomColor (alignRColorOf p))) :=
    (hq.pair (hq.comp polyFun_alignRDomColor)).comp polyFun_alignRDomWindow
  exact (polyFun_alignKerGens.pair hwin).comp polyFun_winOrbits

end Algo
