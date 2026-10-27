/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 13.1 on the unit-cost RAM: the group `G_T` (Notation 13.1.1) and the affected set
`Aff(H, ψ)` (Definition 13.1.4, Eq. (68)).
-/
import Workspace.Algo.TopStab
import Workspace.Algo.Order
import Workspace.LocalCertificates.Procedure
import Workspace.Machine.Pow

/-!
# §13.1 on the RAM: `G_T` and the affected set

This file carries the two lowest layers of Procedure LocalCertificates onto the machine.

## `G_T` (claim C1, Notation 13.1.1)

> We note that the group `(G^ϕ)_A` can be trivially computed because `ϕ` is a giant
> representation.  Therefore `G_A` can be computed in polynomial time as
> `G_A = ϕ⁻¹((G^ϕ)_A)`.

That is Proposition 12.0.9, which A12 already implements as `Algo.topStab`
(`Workspace/Algo/TopStab.lean`).  All that is added here is the bridge
`Babai.stabIn_eq_map_setwiseStabViaHom` between the two names the two sections use for the
same group, and `Algo.decGroup_topStab_bigGT`, which is C1 in the form §13 uses.

## The affected set (Definition 13.1.4)

> `Aff(H, ϕ) = {x ∈ Ω | H_x^ϕ ≱ A(Γ)}`.  (68)

Two things have to be arranged for a machine.

**Getting `ψ` on a point stabilizer.**  `Algo.rawPointStab` returns generators of `H_u` as
permutations of `Ω`, and their images under `ψ` cannot be read off them.  The fix is the
device of A12: put the action on the disjoint union `Ω ⊔ Γ` (`Algo.rawExtGens`), where the
group is the *graph* of `ψ` (`Algo.mem_ext_group_iff`).  A point `u < n` of the bottom half
is fixed by `a ⊔ ψ(a)` exactly when `a` fixes `u`, so the point stabilizer of `u` in the
graph group is the graph of `H_u`, and its top half is `ψ(H_u)`.  `Algo.topOf` reads that
top half, as `Algo.projOf` reads the bottom half, and `Algo.genGroup_map_topOf` is the
generation statement — the mirror image of `Algo.genGroup_map_projOf` (Prop. 2.2.6 (a)).

**Testing `A(Γ) ≤ K` in polynomial time.**  Enumerating `S(Γ)` is out of the question: in
§13.1 the target is a test set of size `t ≈ log n`, so `t!` is quasipolynomial.  The test is
on the order instead (`Algo.alternating_le_iff_factorial_le`):

> for `K ≤ S(Δ)`, `A(Δ) ≤ K` if and only if `|Δ|! ≤ 2 |K|`.

Both sides are machine naturals of polynomial size: `|K|` is a product of at most `|Δ|` row
lengths of the stabilizer chain (`Algo.rawOrder`), and `|Δ|!` has about `|Δ| log |Δ|` bits,
so it is polynomial in the length of the domain witness — this is `RAM.PolyFun.factorial`,
applied to the *length of a list*, never to a machine natural.

## Main definitions

* `Algo.topOf` — the top half of `a ⊔ b`;
* `Algo.rawIsGiantSub` — decides `A(Δ) ≤ K` for `K` given by generators;
* `Algo.rawTopStabGens` — generators of `ψ(H_u)`;
* `Algo.rawAffected` — decides `u ∈ Aff(H, ψ)`;
* `Algo.rawAff` — the affected set, as a list of points.

## Main results

* `Algo.decGroup_topStab_bigGT` — C1: the routine of Prop. 12.0.9 computes `Babai.bigGT`;
* `Algo.alternating_le_iff_factorial_le` — the order test;
* `Algo.genGroup_map_topOf` — the graph-group read-back of `ψ(H_u)`;
* `Algo.rawAffected_eq_true_iff`, `Algo.winSet_rawAff` — Eq. (68) on raw data;
* `Algo.polyFun_rawIsGiantSub`, `Algo.polyFun_rawTopStabGens`, `Algo.polyFun_rawAffected`,
  `Algo.polyFun_rawAff` — the time classes.

No axiom, no `sorry`, no `native_decide`.
-/

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Classical

variable {Ω Γ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Equiv.Perm Ω)}

/-- Notation 13.1.1 and §12 name the same group: `L_A` of §13.1, taken inside all of `G`,
is the setwise stabilizer through `ϕ` of §12, read back in `S(Ω)`.

This is what turns Proposition 12.0.9 (claim C1, "`G_A` can be computed in polynomial time
as `G_A = ϕ⁻¹((G^ϕ)_A)`") into a statement about `Babai.bigGT`. -/
theorem stabIn_eq_map_setwiseStabViaHom (ϕ : G →* Equiv.Perm Γ) (A : Set Γ) :
    stabIn ϕ (le_refl G) A = (setwiseStabViaHom ϕ A).map G.subtype := by
  ext σ
  rw [mem_stabIn]
  constructor
  · rintro ⟨hσ, himg⟩
    exact ⟨⟨σ, hσ⟩, mem_setwiseStabViaHom.2 himg, rfl⟩
  · rintro ⟨⟨τ, hτ⟩, hmem, rfl⟩
    exact ⟨hτ, mem_setwiseStabViaHom.1 hmem⟩

/-- Notation 13.1.1, the same statement for `Babai.bigGT`, the name §13.1 uses. -/
theorem bigGT_eq_map_setwiseStabViaHom (ϕ : G →* Equiv.Perm Γ) (T : Set Γ) :
    bigGT ϕ T = (setwiseStabViaHom ϕ T).map G.subtype :=
  stabIn_eq_map_setwiseStabViaHom ϕ T

end Babai

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)
open Equiv.Perm

/-! ## Claim C1: `G_T` on the RAM -/

variable {n m : ℕ} {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}

/-- **Claim C1** (Notation 13.1.1, §13.1).

> Therefore `G_A` can be computed in polynomial time as `G_A = ϕ⁻¹((G^ϕ)_A)`.

The routine is `Algo.topStab`, the implementation of Proposition 12.0.9 (A12,
`Workspace/Algo/TopStab.lean`); its time class is `Algo.polyFun_topStab`.  Here its answer
is identified with `Babai.bigGT`, the name §13.1 uses for the same group. -/
theorem decGroup_topStab_bigGT {dom gdom C : List ℕ} (hd : dom.length = n)
    (hm : gdom.length = m) {ϕ : genGroup gens →* Perm (Fin m)} (hI : ImgsOf gens imgs ϕ)
    (hgiant : Babai.IsGiantRep ϕ) :
    decGroup n (topStab (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C)) =
      Babai.bigGT ϕ (winSet m C) := by
  rw [decGroup_topStab hd hm hI hgiant, Babai.bigGT_eq_map_setwiseStabViaHom]

/-- Claim C1 on arbitrary well-formed raw input. -/
theorem topStab_bigGT_of_wf (p : RawAction × List ℕ)
    (ϕ : decGroup n p.1.1.2 →* Perm (Fin m))
    (hp : RawAction.WF n m p.1 ϕ) (hgiant : Babai.IsGiantRep ϕ) :
    decGroup n (topStab p) = Babai.bigGT ϕ (winSet m p.2) := by
  rw [topStab_spec_of_wf p ϕ hp hgiant, Babai.bigGT_eq_map_setwiseStabViaHom]

/-! ## The order test for `A(Δ) ≤ K`

Definition 13.1.4 asks whether the image of a point stabilizer contains the alternating
group.  The image is handed over by generators, and the alternating group has `|Δ|!/2`
elements, so it cannot be enumerated.  The following elementary equivalence replaces the
enumeration by one comparison of two numbers. -/

/-- **The order test.**  A subgroup of `S(Δ)` contains `A(Δ)` exactly when twice its order
reaches `|Δ|!`.

*Proof.*  If `A(Δ) ≤ K` then `|A(Δ)| ≤ |K|`, and `2|A(Δ)| = |S(Δ)| = |Δ|!` as soon as `Δ`
has two points; for `|Δ| ≤ 1` the group `S(Δ)` is trivial and both sides hold.  Conversely
`|S(Δ) : K| · |K| = |S(Δ)| ≤ 2|K|` forces the index to be one or two.  Index one gives
`K = S(Δ)`.  Index two gives `g² ∈ K` for every `g`, and every 3-cycle `c` satisfies
`c = c⁴ = (c²)²`, so `K` contains all 3-cycles, which generate `A(Δ)`.

No hypothesis on `|Δ|` is needed. -/
theorem alternating_le_iff_factorial_le {Δ : Type*} [Fintype Δ] [DecidableEq Δ]
    (K : Subgroup (Perm Δ)) :
    alternatingGroup Δ ≤ K ↔ Nat.factorial (Fintype.card Δ) ≤ 2 * Nat.card K := by
  have hperm : Nat.card (Perm Δ) = Nat.factorial (Fintype.card Δ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hindex : K.index * Nat.card K = Nat.card (Perm Δ) := K.index_mul_card
  constructor
  · intro hle
    rcases subsingleton_or_nontrivial Δ with hΔ | hΔ
    · have hc : Fintype.card Δ ≤ 1 := Fintype.card_le_one_iff_subsingleton.2 hΔ
      have h1 : Nat.factorial (Fintype.card Δ) = 1 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hc with h | h <;> rw [h] <;> rfl
      omega
    · have h2 : 2 * Nat.card (alternatingGroup Δ) = Nat.card (Perm Δ) :=
        two_mul_nat_card_alternatingGroup
      have h3 : Nat.card (alternatingGroup Δ) ≤ Nat.card K :=
        Nat.card_le_card_of_injective
          (fun a => (⟨(a : Perm Δ), hle a.2⟩ : K))
          (fun a b hab => Subtype.ext
            (show (a : Perm Δ) = (b : Perm Δ) from
              congrArg (fun z : ↥K => (z : Perm Δ)) hab))
      omega
  · intro hle
    have hidx : K.index ≤ 2 := by
      by_contra hcon
      push_neg at hcon
      have : 3 * Nat.card K ≤ K.index * Nat.card K := Nat.mul_le_mul_right _ hcon
      omega
    have hfac : 0 < Nat.factorial (Fintype.card Δ) := Nat.factorial_pos _
    have hidx0 : K.index ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hindex
      omega
    have hcase : K.index = 1 ∨ K.index = 2 := by omega
    rcases hcase with h | h
    · rw [Subgroup.index_eq_one] at h
      rw [h]
      exact le_top
    · rw [← closure_three_cycles_eq_alternating, Subgroup.closure_le]
      intro c hc
      have hord : orderOf c = 3 := IsThreeCycle.orderOf hc
      have hpow : c = (c ^ 2) ^ 2 := by
        have h4 : c ^ 4 = c := by
          have h3 : c ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one c
          calc c ^ 4 = c ^ 3 * c := by rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ]
            _ = c := by rw [h3, one_mul]
        rw [← pow_mul]
        exact h4.symm
      rw [SetLike.mem_coe, hpow]
      exact Subgroup.sq_mem_of_index_two h _

/-! ## The top half of `Ω ⊔ Γ`

`Algo.projOf` (`Workspace/Algo/Extend.lean`) reads the `Ω`-half of a permutation of the
disjoint union.  Definition 13.1.4 needs the other half. -/

/-- **The read-back of one permutation of `Ω ⊔ Γ`, as a permutation of `Γ`.**  On a
permutation of the shape `a ⊔ b` it is `b`; on anything else it is junk. -/
noncomputable def topOf (n m : ℕ) (σ : Perm (Fin (n + m))) : Perm (Fin m) :=
  decPerm m (rawRestrictPerm (extWin n m, encPerm (n + m) σ))

@[simp] theorem topOf_extPerm (a : Perm (Fin n)) (b : Perm (Fin m)) :
    topOf n m (extPerm n m a b) = b := by
  rw [topOf, rawRestrictPerm_extPerm, decPerm_encPerm]

/-! ## The point stabilizer in the graph group -/

section Graph

variable {ϕ : genGroup gens →* Perm (Fin m)}

/-- **The point stabilizer of `u ∈ Ω` in the extended group is the graph of `H_u`.**  A
permutation `a ⊔ ψ(a)` fixes the point `u` of the bottom half exactly when `a` fixes `u`.
This is the companion of `Algo.mem_pointwiseStabilizer_ext` (Prop. 2.2.6 (a)), for a point
of `Ω` instead of the whole of `Γ`. -/
theorem mem_pointStab_ext (hI : ImgsOf gens imgs ϕ) (u : Fin n) {σ : Perm (Fin (n + m))} :
    σ ∈ Babai.pointwiseStabilizer (genGroup (extGensOf n m gens imgs))
        {x : Fin (n + m) | (x : ℕ) ∈ [(u : ℕ)]}
      ↔ ∃ (a : Perm (Fin n)) (h : a ∈ genGroup gens), a u = u ∧
          σ = extPerm n m a (ϕ ⟨a, h⟩) := by
  have hun : (u : ℕ) < n + m := by have := u.isLt; omega
  have hpt : (⟨(u : ℕ), hun⟩ : Fin (n + m)) ∈ {x : Fin (n + m) | (x : ℕ) ∈ [(u : ℕ)]} := by
    simp
  rw [Babai.mem_pointwiseStabilizer]
  constructor
  · rintro ⟨hmem, hfix⟩
    obtain ⟨a, ha, rfl⟩ := (mem_ext_group_iff hI).1 hmem
    refine ⟨a, ha, ?_, rfl⟩
    have hfx : (extPerm n m a (ϕ ⟨a, ha⟩)) ⟨(u : ℕ), hun⟩ = (⟨(u : ℕ), hun⟩ : Fin (n + m)) :=
      hfix _ hpt
    have hval : (((extPerm n m a (ϕ ⟨a, ha⟩)) ⟨(u : ℕ), hun⟩ : Fin (n + m)) : ℕ) = (u : ℕ) := by
      rw [hfx]
    rw [extPerm_val_lt a _ u.isLt hun] at hval
    exact Fin.ext (by simpa using hval)
  · rintro ⟨a, ha, hfix, rfl⟩
    refine ⟨(mem_ext_group_iff hI).2 ⟨a, ha, rfl⟩, ?_⟩
    intro x hx
    have hxu : (x : ℕ) = (u : ℕ) := by simpa using hx
    have hxe : x = (⟨(u : ℕ), hun⟩ : Fin (n + m)) := Fin.ext hxu
    subst hxe
    refine Fin.ext ?_
    rw [extPerm_val_lt a _ u.isLt hun, Fin.eta, hfix]

/-- **The top half of the point stabilizer of `u` in the graph group generates `ψ(H_u)`.**

This is the statement Definition 13.1.4 needs: the machine has generators `L` of the point
stabilizer of `u` in the extended group (which is what `Algo.rawPointStab` returns there),
and reading their top halves gives generators of the image `H_u^ψ`.

*Proof.*  As in `Algo.genGroup_map_projOf`.  Every member of `L` is of the shape
`a ⊔ ψ(a)` with `a` fixing `u` (`Algo.mem_pointStab_ext`), so its top half lies in
`ψ(H_u)`, which gives one inclusion.  For the other, an induction over the closure shows
that every element of `⟨L⟩` is of the shape `a ⊔ b` with `b ∈ ⟨topOf '' L⟩`; applying it to
`a ⊔ ψ(a)` for `a ∈ H_u`, which lies in `⟨L⟩`, and using injectivity of `⊔`, gives
`ψ(a) ∈ ⟨topOf '' L⟩`. -/
theorem genGroup_map_topOf (hI : ImgsOf gens imgs ϕ) (u : Fin n)
    (L : List (Perm (Fin (n + m))))
    (hL : genGroup L = Babai.pointwiseStabilizer (genGroup (extGensOf n m gens imgs))
      {x : Fin (n + m) | (x : ℕ) ∈ [(u : ℕ)]}) :
    genGroup (L.map (topOf n m)) = (MulAction.stabilizer (genGroup gens) u).map ϕ := by
  have hgen : ∀ τ ∈ L, ∃ (a : Perm (Fin n)) (h : a ∈ genGroup gens), a u = u ∧
      τ = extPerm n m a (ϕ ⟨a, h⟩) := by
    intro τ hτ
    have hmem : τ ∈ genGroup L := Subgroup.subset_closure hτ
    rw [hL] at hmem
    exact (mem_pointStab_ext hI u).1 hmem
  have hstab : ∀ (a : Perm (Fin n)) (h : a ∈ genGroup gens), a u = u →
      (⟨a, h⟩ : genGroup gens) ∈ MulAction.stabilizer (genGroup gens) u := by
    intro a h hfix
    rw [MulAction.mem_stabilizer_iff]
    show (⟨a, h⟩ : genGroup gens) • u = u
    rw [Subgroup.smul_def, Equiv.Perm.smul_def]
    exact hfix
  apply le_antisymm
  · rw [genGroup, Subgroup.closure_le]
    rintro y hy
    obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 hy
    obtain ⟨a, ha, hfix, rfl⟩ := hgen τ hτ
    rw [SetLike.mem_coe, topOf_extPerm]
    exact ⟨⟨a, ha⟩, hstab a ha hfix, rfl⟩
  · have key : ∀ σ ∈ genGroup L, ∃ (a : Perm (Fin n)) (b : Perm (Fin m)),
        σ = extPerm n m a b ∧ b ∈ genGroup (L.map (topOf n m)) := by
      intro σ hσ
      rw [genGroup] at hσ
      induction hσ using Subgroup.closure_induction with
      | mem x hx =>
          obtain ⟨a, ha, hfix, hxa⟩ := hgen x hx
          refine ⟨a, ϕ ⟨a, ha⟩, hxa, Subgroup.subset_closure ?_⟩
          exact List.mem_map.2 ⟨x, hx, by rw [hxa, topOf_extPerm]⟩
      | one => exact ⟨1, 1, by rw [extPerm_one], Subgroup.one_mem _⟩
      | mul x y hx hy ihx ihy =>
          obtain ⟨a, b, hxab, hb⟩ := ihx
          obtain ⟨c, d, hycd, hd⟩ := ihy
          exact ⟨a * c, b * d, by rw [hxab, hycd, ← extPerm_mul],
            Subgroup.mul_mem _ hb hd⟩
      | inv x hx ihx =>
          obtain ⟨a, b, hxab, hb⟩ := ihx
          exact ⟨a⁻¹, b⁻¹, by rw [hxab, extPerm_inv], Subgroup.inv_mem _ hb⟩
    rintro y ⟨g, hg, rfl⟩
    have hfix : (g : Perm (Fin n)) u = u := by
      have := (MulAction.mem_stabilizer_iff).1 hg
      rw [Subgroup.smul_def, Equiv.Perm.smul_def] at this
      exact this
    have hext : extPerm n m (g : Perm (Fin n)) (ϕ g) ∈ genGroup L := by
      rw [hL]
      refine (mem_pointStab_ext hI u).2 ⟨(g : Perm (Fin n)), g.2, hfix, ?_⟩
      congr 1
    obtain ⟨a, b, hab, hb⟩ := key _ hext
    rw [(extPerm_injective hab).2]
    exact hb

end Graph

/-! ## The order test as a routine -/

/-- **Decides `A(Δ) ≤ K`** for a subgroup `K ≤ S(Δ)` given by generators, by comparing the
order of `K` with `|Δ|!/2` (`Algo.alternating_le_iff_factorial_le`).  `p.1` is the domain
witness of `Δ`; its length is `|Δ|`. -/
def rawIsGiantSub (p : List ℕ × RawGens) : Bool :=
  decide (Nat.factorial p.1.length ≤ 2 * rawOrder p)

/-- **The order test is correct.** -/
theorem rawIsGiantSub_eq_true_iff {dom : List ℕ} (hd : dom.length = m)
    (gs : List (Perm (Fin m))) :
    rawIsGiantSub (dom, gs.map (encPerm m)) = true ↔ alternatingGroup (Fin m) ≤ genGroup gs := by
  rw [rawIsGiantSub, decide_eq_true_eq, rawOrder_spec dom hd gs, hd,
    alternating_le_iff_factorial_le (genGroup gs), Fintype.card_fin]

/-! ## The affected set (Definition 13.1.4) -/

/-- Generators of `H_u^ψ`, the image under `ψ` of the stabilizer of the point `u`: put the
action on `Ω ⊔ Γ`, take the point stabilizer of `u` there, and read the top halves. -/
def rawTopStabGens (p : RawAction × ℕ) : RawGens :=
  (rawPointStab ((rawExtDom (p.1.1.1, p.1.2.1), rawExtGens (p.1.1.2, p.1.2.2)),
    [p.2])).map (fun r => rawRestrictPerm (rawExtWin (p.1.1.1, p.1.2.1), r))

section Aff

variable {ϕ : genGroup gens →* Perm (Fin m)} {dom gdom : List ℕ}

set_option maxHeartbeats 1000000 in
/-- **The routine computes `H_u^ψ`**, as an explicit list of encodings.  Both the decoding
spec and the well-formedness of the answer are read off this one statement. -/
theorem rawTopStabGens_repr (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (u : Fin n) :
    ∃ L : List (Perm (Fin m)),
      rawTopStabGens (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), (u : ℕ))
          = L.map (encPerm m) ∧
        genGroup L = (MulAction.stabilizer (genGroup gens) u).map ϕ := by
  have hlen : (dom ++ gdom).length = n + m := by simp [hd, hg]
  have hun : (u : ℕ) < n + m := by have := u.isLt; omega
  have hlt : ∀ x ∈ [(u : ℕ)], x < n + m := by
    intro x hx
    rw [List.mem_singleton] at hx
    omega
  have hnd : ([(u : ℕ)] : List ℕ).Nodup := List.nodup_singleton _
  have hraw : rawExtGens (gens.map (encPerm n), imgs.map (encPerm m))
      = (extGensOf n m gens imgs).map (encPerm (n + m)) := rawExtGens_spec gens imgs hI.1
  have hwin : rawExtWin (dom, gdom) = extWin n m := rawExtWin_eq dom gdom hd hg
  have hval : rawTopStabGens (((dom, gens.map (encPerm n)),
      (gdom, imgs.map (encPerm m))), (u : ℕ))
      = (rawPointStab ((dom ++ gdom, (extGensOf n m gens imgs).map (encPerm (n + m))),
          [(u : ℕ)])).map (fun r => rawRestrictPerm (extWin n m, r)) := by
    rw [rawTopStabGens]
    rw [show rawExtDom (dom, gdom) = dom ++ gdom from rfl, hraw, hwin]
  obtain ⟨L, hLenc⟩ : ∃ L : List (Perm (Fin (n + m))),
      L.map (encPerm (n + m)) = rawPointStab ((dom ++ gdom,
        (extGensOf n m gens imgs).map (encPerm (n + m))), [(u : ℕ)]) :=
    ⟨_, map_encPerm_decPerm' (wf_rawPointStab hlen hnd hlt _)⟩
  have hgenL : genGroup L = Babai.pointwiseStabilizer (genGroup (extGensOf n m gens imgs))
      {x : Fin (n + m) | (x : ℕ) ∈ [(u : ℕ)]} := by
    have h := decGroup_rawPointStab (dom ++ gdom) hlen (extGensOf n m gens imgs) [(u : ℕ)]
      hnd hlt
    rw [← hLenc, decGroup_map_encPerm] at h
    exact h
  have hstep : ∀ τ ∈ L, rawRestrictPerm (extWin n m, encPerm (n + m) τ)
      = encPerm m (topOf n m τ) := by
    intro τ hτ
    have hmem : τ ∈ genGroup L := Subgroup.subset_closure hτ
    rw [hgenL] at hmem
    obtain ⟨a, ha, -, rfl⟩ := (mem_pointStab_ext hI u).1 hmem
    rw [rawRestrictPerm_extPerm, topOf_extPerm]
  refine ⟨L.map (topOf n m), ?_, genGroup_map_topOf hI u L hgenL⟩
  rw [hval, ← hLenc, List.map_map, List.map_map]
  exact List.map_congr_left hstep

/-- **The routine computes `H_u^ψ`.** -/
theorem decGroup_rawTopStabGens (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (u : Fin n) :
    decGroup m (rawTopStabGens (((dom, gens.map (encPerm n)),
        (gdom, imgs.map (encPerm m))), (u : ℕ)))
      = (MulAction.stabilizer (genGroup gens) u).map ϕ := by
  obtain ⟨L, heq, hgen⟩ := rawTopStabGens_repr hd hg hI u
  rw [heq, decGroup_map_encPerm, hgen]

/-- The answer of the routine is a well-formed list of raw permutations of `[0, m)`. -/
theorem wf_rawTopStabGens (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (u : Fin n) :
    RawGens.WF m (rawTopStabGens (((dom, gens.map (encPerm n)),
      (gdom, imgs.map (encPerm m))), (u : ℕ))) := by
  obtain ⟨L, heq, -⟩ := rawTopStabGens_repr hd hg hI u
  rw [heq]
  exact wf_map_encPerm m L

/-- **Decides whether a point is affected** (Definition 13.1.4, Eq. (68)): `u` is affected
by `(H, ψ)` when `H_u^ψ` does not contain `A(Γ)`. -/
def rawAffected (p : RawAction × ℕ) : Bool :=
  ! rawIsGiantSub (p.1.2.1, rawTopStabGens p)

/-- **Definition 13.1.4, Eq. (68), on raw data.** -/
theorem rawAffected_eq_true_iff (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (u : Fin n) :
    rawAffected (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), (u : ℕ)) = true
      ↔ Babai.AffectedIn ϕ u := by
  obtain ⟨L, heq, hgen⟩ := rawTopStabGens_repr hd hg hI u
  rw [rawAffected,
    show (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))) : RawAction).2.1
      = gdom from rfl, heq, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
    rawIsGiantSub_eq_true_iff hg L, hgen]
  exact Iff.rfl

/-- **The affected set** `Aff(H, ψ)` of Definition 13.1.4, Eq. (68), as a list of points of
`Ω`.  The points are `0, …, n-1`, read off the *length* of the domain witness: a machine
natural is never a loop bound (`RAM.polyFun_rangeLength`). -/
def rawAff (p : RawAction) : List ℕ :=
  (List.range p.1.1.length).filter (fun u => rawAffected (p, u))

theorem nodup_rawAff (p : RawAction) : (rawAff p).Nodup :=
  List.Nodup.filter _ (List.nodup_range)

theorem lt_of_mem_rawAff {p : RawAction} {u : ℕ} (hu : u ∈ rawAff p) : u < p.1.1.length := by
  rw [rawAff, List.mem_filter] at hu
  exact List.mem_range.1 hu.1

/-- **Eq. (68) on raw data**: the routine lists exactly the affected points. -/
theorem mem_rawAff_iff (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (u : ℕ) :
    u ∈ rawAff ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m)))
      ↔ ∃ h : u < n, Babai.AffectedIn ϕ (⟨u, h⟩ : Fin n) := by
  rw [rawAff, List.mem_filter]
  constructor
  · rintro ⟨hrange, htest⟩
    have hun : u < n := by
      have := List.mem_range.1 hrange
      simpa [hd] using this
    refine ⟨hun, ?_⟩
    have := (rawAffected_eq_true_iff hd hg hI (⟨u, hun⟩ : Fin n)).1 htest
    exact this
  · rintro ⟨hun, haff⟩
    refine ⟨List.mem_range.2 (by simpa [hd] using hun), ?_⟩
    exact (rawAffected_eq_true_iff hd hg hI (⟨u, hun⟩ : Fin n)).2 haff

/-- **Definition 13.1.4, Eq. (68)**: the set the routine returns is `Aff(H, ψ)`. -/
theorem winSet_rawAff (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) :
    winSet n (rawAff ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))))
      = {x : Fin n | Babai.AffectedIn ϕ x} := by
  ext x
  rw [mem_winSet, mem_rawAff_iff hd hg hI]
  constructor
  · rintro ⟨h, haff⟩
    have : (⟨(x : ℕ), h⟩ : Fin n) = x := Fin.eta _ _
    rwa [this] at haff
  · intro hx
    exact ⟨x.isLt, by simpa using hx⟩

end Aff

/-! ## The time classes -/

theorem polyFun_rawIsGiantSub : PolyFun rawIsGiantSub := by
  have hlen : PolyFun (fun p : List ℕ × RawGens => p.1.length) :=
    polyFun_fst.comp polyFun_length
  have hbd : ∀ p : List ℕ × RawGens, p.1.length ≤ Enc.size p :=
    fun p => le_trans (length_le_size p.1) (size_fst_le' p)
  have h1 : PolyFun (fun p : List ℕ × RawGens => Nat.factorial p.1.length) :=
    hlen.factorial hbd polyBound_id
  have h2 : PolyFun (fun p : List ℕ × RawGens => 2 * rawOrder p) :=
    ((polyFun_const 2).pair polyFun_rawOrder).comp polyFun_mul
  exact (h1.le h2).of_eq (fun _ => rfl)

theorem polyFun_rawTopStabGens : PolyFun rawTopStabGens := by
  have hd : PolyFun (fun z : RawAction × ℕ => rawExtDom (z.1.1.1, z.1.2.1)) :=
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_fst)).pair
      ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)).comp polyFun_rawExtDom
  have hgs : PolyFun (fun z : RawAction × ℕ => rawExtGens (z.1.1.2, z.1.2.2)) :=
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_snd)).pair
      ((polyFun_fst.comp polyFun_snd).comp polyFun_snd)).comp polyFun_rawExtGens
  have hsing : PolyFun (fun z : RawAction × ℕ => [z.2]) :=
    polyFun_snd.comp polyFun_singleton
  have hinner : PolyFun (fun z : RawAction × ℕ =>
      rawPointStab ((rawExtDom (z.1.1.1, z.1.2.1), rawExtGens (z.1.1.2, z.1.2.2)),
        [z.2])) :=
    ((hd.pair hgs).pair hsing).comp polyFun_rawPointStab
  have hf : PolyFun (fun q : (RawAction × ℕ) × RawPerm =>
      rawRestrictPerm (rawExtWin (q.1.1.1.1, q.1.1.2.1), q.2)) :=
    ((((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst).pair
      (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst)).comp
        polyFun_rawExtWin).pair polyFun_snd).comp polyFun_rawRestrictPerm
  exact ((polyFun_id.pair hinner).comp (PolyFun.mapParam hf)).of_eq (fun _ => rfl)

theorem polyFun_rawAffected : PolyFun rawAffected := by
  have hcore : PolyFun (fun p : RawAction × ℕ =>
      rawIsGiantSub (p.1.2.1, rawTopStabGens p)) :=
    ((((polyFun_fst.comp polyFun_snd).comp polyFun_fst)).pair
      polyFun_rawTopStabGens).comp polyFun_rawIsGiantSub
  refine (PolyFun.ite hcore (polyFun_const false) (polyFun_const true)).of_eq (fun p => ?_)
  by_cases h : rawIsGiantSub (p.1.2.1, rawTopStabGens p) <;> simp [rawAffected, h]

theorem polyFun_rawAff : PolyFun rawAff := by
  have hrange : PolyFun (fun p : RawAction => List.range p.1.1.length) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_rangeLength
  exact ((polyFun_id.pair hrange).comp (PolyFun.filterParam polyFun_rawAffected)).of_eq
    (fun _ => rfl)


end Algo
