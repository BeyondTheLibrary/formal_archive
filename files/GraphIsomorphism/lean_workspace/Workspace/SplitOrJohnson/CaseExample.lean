/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sections 9.6-9.8: an explicit object of the `Case` of §9.8, to show that the `Case`
structures are not empty.
-/
import Workspace.SplitOrJohnson.BlkCases

/-!
# §9.8  An explicit input of the UPCC case

The `Case` headings of §9.6-§9.8 are conditions on a coherent configuration `X` whose
vertex set splits into two vertex-color classes `V₁`, `V₂`.  This file exhibits one
configuration that satisfies the `Case` of §9.8, so `Babai.IsUPCCCase` — and with it
`Babai.IsBipartiteCase`, which it extends — has an instance.

**The configuration.**  Take two copies of `ZMod 5` and let the group of the five
translations `t ↦ t + d` act on both copies at once.  The orbital configuration `X(G)` of
that group (Obs. 3.1.12) is coherent, its two vertex-color classes are the two copies
(Obs. 3.1.15), and two pairs of vertices have the same color exactly when they lie in the
same pair of copies and have the same difference.  So:

* `X₁` and `X₂` are both the *pentagon-like* configuration on `ZMod 5` whose colors are the
  five differences: homogeneous, of rank `5 ≥ 3`, and each off-diagonal constituent is the
  cycle `t → t + d` with `d ≠ 0`, which is connected because `5` is prime.  Both are UPCCs.
* the link is nontrivial: the pairs `((false,0),(true,0))` and `((false,0),(true,1))` have
  different differences, so different colors.

There is nothing special about `5` beyond being a prime larger than `3`; `5` is the
smallest degree of a UPCC.
-/

namespace Babai

open scoped Classical

namespace UPCCExample

/-! ### The group of translations of two copies of `ZMod 5` -/

/-- The vertex set: two copies of `ZMod 5`. -/
abbrev Vtx : Type := Bool × ZMod 5

/-- The translation by `d`, acting on both copies at once. -/
def shift (d : ZMod 5) : Equiv.Perm Vtx where
  toFun p := (p.1, p.2 + d)
  invFun p := (p.1, p.2 - d)
  left_inv p := by simp
  right_inv p := by simp

@[simp] theorem shift_apply (d : ZMod 5) (p : Vtx) : shift d p = (p.1, p.2 + d) := rfl

/-- The group `G` of the five translations. -/
def G : Subgroup (Equiv.Perm Vtx) where
  carrier := Set.range shift
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨b + a, Equiv.ext fun p => Prod.ext rfl (by simp [shift]; ring)⟩
  one_mem' := ⟨0, Equiv.ext fun p => Prod.ext rfl (by simp [shift])⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, Equiv.ext fun p => Prod.ext rfl (by simp [shift, sub_eq_add_neg])⟩

theorem mem_G {σ : Equiv.Perm Vtx} : σ ∈ G ↔ ∃ d, shift d = σ := Iff.rfl

/-! ### The configuration and its colors -/

/-- Observation 3.1.12.  The orbital configuration of `G`: two pentagons joined by their
difference pattern. -/
noncomputable def X : PartitionStructure Vtx := PartitionStructure.orbitalConfig G

theorem X_isCoherent : X.IsCoherent := PartitionStructure.orbitalConfig_isCoherent G

/-- The color classes of `X`: two pairs get the same color exactly when they lie in the
same pair of copies and have the same difference. -/
theorem X_color_eq_iff (x y u v : Vtx) :
    X.color x y = X.color u v ↔ (x.1 = u.1 ∧ y.1 = v.1 ∧ y.2 - x.2 = v.2 - u.2) := by
  rw [X, PartitionStructure.orbitalConfig_color_eq_iff]
  constructor
  · rintro ⟨σ, ⟨d, rfl⟩, hσ⟩
    have h1 : (u.1, u.2 + d) = x := congrArg Prod.fst hσ
    have h2 : (v.1, v.2 + d) = y := congrArg Prod.snd hσ
    refine ⟨?_, ?_, ?_⟩
    · exact (congrArg Prod.fst h1).symm
    · exact (congrArg Prod.fst h2).symm
    · have e1 : u.2 + d = x.2 := congrArg Prod.snd h1
      have e2 : v.2 + d = y.2 := congrArg Prod.snd h2
      rw [← e1, ← e2]; ring
  · rintro ⟨h1, h2, h3⟩
    refine ⟨shift (x.2 - u.2), ⟨_, rfl⟩, Prod.ext ?_ ?_⟩
    · exact Prod.ext h1.symm (by simp)
    · refine Prod.ext h2.symm ?_
      show v.2 + (x.2 - u.2) = y.2
      have h4 : y.2 - x.2 = v.2 - u.2 := h3
      linear_combination -h4

/-- The two parts: the two copies of `ZMod 5`, as vertex-color classes of `X`. -/
noncomputable abbrev part (b : Bool) : Set Vtx := X.vertexClass (X.vcolor (b, 0))

theorem mem_part_iff (b : Bool) (p : Vtx) : p ∈ part b ↔ p.1 = b := by
  show X.color p p = X.color (b, 0) (b, 0) ↔ _
  rw [X_color_eq_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, h, by simp⟩⟩

noncomputable instance instFintypePart (b : Bool) :
    Fintype ↥(X.vertexClass (X.vcolor (b, 0))) := Fintype.ofFinite _

/-- The vertex of the copy `b` at the point `t`. -/
def pt (b : Bool) (t : ZMod 5) : ↥(part b) := ⟨(b, t), (mem_part_iff b _).2 rfl⟩

@[simp] theorem pt_coe (b : Bool) (t : ZMod 5) : ((pt b t : Vtx)) = (b, t) := rfl

theorem eq_pt (b : Bool) (x : ↥(part b)) : x = pt b (x : Vtx).2 :=
  Subtype.ext (Prod.ext ((mem_part_iff b _).1 x.2) rfl)

/-! ### `X₁` and `X₂` are UPCCs -/

/-- The colors of `X[V_b]`: the difference of the two points. -/
theorem induced_color_eq_iff (b : Bool) (x y x' y' : ↥(part b)) :
    (X.induced (part b)).color x y = (X.induced (part b)).color x' y' ↔
      (y : Vtx).2 - (x : Vtx).2 = (y' : Vtx).2 - (x' : Vtx).2 := by
  rw [X.induced_color_eq_iff, X_color_eq_iff]
  have hx := (mem_part_iff b (x : Vtx)).1 x.2
  have hy := (mem_part_iff b (y : Vtx)).1 y.2
  have hx' := (mem_part_iff b (x' : Vtx)).1 x'.2
  have hy' := (mem_part_iff b (y' : Vtx)).1 y'.2
  simp [hx, hy, hx', hy']

/-- Definition 3.2.1, Notation 3.2.2.  `X[V_b]` is a UPCC: homogeneous, of rank `5`, and
each off-diagonal constituent is the cycle `t → t + d`, which is connected because `5` is
prime. -/
theorem induced_isUniprimitive (b : Bool) : (X.induced (part b)).IsUniprimitive := by
  -- every nonzero element of `ZMod 5` generates it: `5` is prime
  have hsolve : ∀ d e : ZMod 5, d ≠ 0 → ∃ n : Fin 5, ((n : ℕ) : ZMod 5) * d = e := by decide
  set Y := X.induced (part b) with hY
  -- homogeneity
  have hhom : Y.IsHomogeneous := by
    intro x y
    show Y.color x x = Y.color y y
    rw [hY, induced_color_eq_iff]
    simp
  -- connectivity of an off-diagonal constituent
  have hconn : ∀ k : Fin Y.rank, Y.IsOffDiagonalColor k →
      (Y.extConstituent k).IsWeaklyConnected := by
    intro k hoff
    obtain ⟨u₀, v₀, hk⟩ := Y.color_surjective k
    set d : ZMod 5 := (v₀ : Vtx).2 - (u₀ : Vtx).2 with hd
    have hdne : d ≠ 0 := by
      intro h0
      have huv : u₀ = v₀ := by
        refine Subtype.ext (Prod.ext ?_ ?_)
        · rw [(mem_part_iff b _).1 u₀.2, (mem_part_iff b _).1 v₀.2]
        · have : (v₀ : Vtx).2 - (u₀ : Vtx).2 = 0 := h0
          linear_combination -this
      have hmem : ((u₀, u₀) : ↥(part b) × ↥(part b)) ∈ Y.rel k ∩ diag _ := by
        refine ⟨?_, rfl⟩
        show Y.color u₀ u₀ = k
        rw [← hk, huv]
      rw [hoff] at hmem
      exact hmem
    -- adjacency in the constituent is "the difference is `d`"
    have hadj : ∀ x y : ↥(part b), (Y.extConstituent k).Adj x y ↔
        (y : Vtx).2 - (x : Vtx).2 = d := by
      intro x y
      have h1 : (Y.extConstituent k).Adj x y ↔ Y.color x y = Y.color u₀ v₀ := by
        rw [hk]; exact Iff.rfl
      rw [h1, hY, induced_color_eq_iff]
    -- one step of the cycle
    have hstep : ∀ t : ZMod 5,
        (Y.extConstituent k).symmetrization.Adj (pt b t) (pt b (t + d)) := by
      intro t
      refine Or.inl ?_
      exact (hadj (pt b t) (pt b (t + d))).2 (by simp)
    -- walking `n` steps
    have hchain : ∀ (n : ℕ) (t : ZMod 5),
        Relation.ReflTransGen (Y.extConstituent k).symmetrization.Adj
          (pt b t) (pt b (t + (n : ZMod 5) * d)) := by
      intro n
      induction n with
      | zero => intro t; simpa using Relation.ReflTransGen.refl
      | succ n ih =>
        intro t
        have h := (ih t).tail (hstep (t + (n : ZMod 5) * d))
        have he : t + (n : ZMod 5) * d + d = t + ((n : ℕ) + 1 : ℕ) * d := by
          push_cast
          ring
        rwa [he] at h
    intro x y
    rw [Digraph.accessible_iff_reflTransGen]
    obtain ⟨s, rfl⟩ : ∃ s, x = pt b s := ⟨(x : Vtx).2, eq_pt b x⟩
    obtain ⟨t, rfl⟩ : ∃ t, y = pt b t := ⟨(y : Vtx).2, eq_pt b y⟩
    -- `d ≠ 0` generates `ZMod 5`, because `5` is prime
    obtain ⟨n, hn⟩ := hsolve d (t - s) hdne
    have h := hchain (n : ℕ) s
    have he : s + ((n : ℕ) : ZMod 5) * d = t := by rw [hn]; ring
    rwa [he] at h
  -- rank at least 3
  have hrank : 3 ≤ Y.rank := by
    set c0 := Y.color (pt b 0) (pt b 0) with hc0
    set c1 := Y.color (pt b 0) (pt b 1) with hc1
    set c2 := Y.color (pt b 0) (pt b 2) with hc2
    have hne : ∀ s t : ZMod 5, s ≠ t → Y.color (pt b 0) (pt b s) ≠ Y.color (pt b 0) (pt b t) := by
      intro s t hst hcon
      rw [hY, induced_color_eq_iff] at hcon
      exact hst (by simpa using hcon)
    have h01 : c0 ≠ c1 := hne 0 1 (by decide)
    have h02 : c0 ≠ c2 := hne 0 2 (by decide)
    have h12 : c1 ≠ c2 := hne 1 2 (by decide)
    have hcard : ({c0, c1, c2} : Finset (Fin Y.rank)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [h01, h02]),
        Finset.card_insert_of_notMem (by simp [h12]), Finset.card_singleton]
    have := Finset.card_le_univ ({c0, c1, c2} : Finset (Fin Y.rank))
    rw [hcard, Fintype.card_fin] at this
    exact this
  exact ⟨⟨hhom, hconn⟩, hrank⟩

/-! ### The `Case` of §9.8 holds -/

theorem vcolor_ne : X.vcolor (false, 0) ≠ X.vcolor (true, 0) := by
  intro h
  have h' : X.color (false, 0) (false, 0) = X.color (true, 0) (true, 0) := h
  rw [X_color_eq_iff] at h'
  exact Bool.noConfusion h'.1

/-- §9.8.  **The `Case` of §9.8 has an instance.**  The orbital configuration of the five
translations acting on two copies of `ZMod 5` is coherent, its two vertex-color classes are
the two copies, both induced configurations are UPCCs, and the link is nontrivial.  So
`Babai.IsUPCCCase`, and with it `Babai.IsBipartiteCase`, is satisfiable; in particular
§9.6-§9.8 are not vacuous. -/
theorem isUPCCCase :
    IsUPCCCase X.natColor (X.vertexClass (X.vcolor (false, 0)))
      (X.vertexClass (X.vcolor (true, 0))) := by
  refine isUPCCCase_induced X X_isCoherent vcolor_ne ?_ ?_ ?_
    (x₁ := pt false 0) (y₁ := pt true 0) (x₂ := pt false 0) (y₂ := pt true 1) ?_
  · intro p
    rcases Bool.eq_false_or_eq_true p.1 with h | h
    · exact Or.inr ((mem_part_iff true p).2 h)
    · exact Or.inl ((mem_part_iff false p).2 h)
  · exact induced_isUniprimitive false
  · exact induced_isUniprimitive true
  · intro hcon
    rw [PartitionStructure.natColor_eq_iff, X_color_eq_iff] at hcon
    exact absurd (by simpa using hcon.2.2) (by decide : ¬ ((0 : ZMod 5) = 1))

end UPCCExample

end Babai
