/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Auxiliary §2 facts needed in §3 that are not (yet) available in `Workspace.Prelim`.
-/
import Workspace.Prelim.BinaryRelations

/-!
# Auxiliary §2.4 lemmas used in §3

`Digraph.accessible_iff_reflTransGen` (`Workspace.Prelim.BinaryRelations`) is proved there.
This file keeps an independent proof of the same equivalence, written when that proof was
still open, because §3 refers to it by the name `Digraph.accessible_iff_reflTransGen'`.
-/

namespace Babai

namespace Digraph

variable {Ω : Type*} (Y : Digraph Ω)

/-! The "induction along a walk" lemmas `walk_rel`, `accessible_rel` and
`weaklyAccessible_rel` now live in `Workspace.Prelim.BinaryRelations`. -/

/-- The length-`0` walk at `u`. -/
theorem accessible_refl (u : Ω) : Y.Accessible u u :=
  ⟨0, fun _ => u, fun i => absurd i.2 (by omega), rfl, rfl⟩

/-- Appending one edge to a walk. -/
theorem accessible_snoc {u v w : Ω} (h : Y.Accessible u v) (hvw : Y.Adj v w) :
    Y.Accessible u w := by
  obtain ⟨t, p, hp, h0, hl⟩ := h
  refine ⟨t + 1, Fin.snoc p w, ?_, ?_, ?_⟩
  · intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have h1 : (Fin.snoc p w : Fin (t + 2) → Ω) j.castSucc.castSucc = p j.castSucc := by
        rw [Fin.snoc_castSucc]
      have h2 : (Fin.snoc p w : Fin (t + 2) → Ω) j.castSucc.succ = p j.succ := by
        rw [Fin.succ_castSucc, Fin.snoc_castSucc]
      rw [h1, h2]
      exact hp j
    · have h1 : (Fin.snoc p w : Fin (t + 2) → Ω) (Fin.last t).castSucc = p (Fin.last t) := by
        rw [Fin.snoc_castSucc]
      have h2 : (Fin.snoc p w : Fin (t + 2) → Ω) (Fin.last t).succ = w := by
        rw [show (Fin.last t).succ = Fin.last (t + 1) from rfl, Fin.snoc_last]
      rw [h1, h2, hl]
      exact hvw
  · rw [show (0 : Fin (t + 2)) = (0 : Fin (t + 1)).castSucc from rfl, Fin.snoc_castSucc, h0]
  · rw [show Fin.last (t + 1) = (Fin.last t).succ from rfl,
      show (Fin.last t).succ = ((Fin.last t) : Fin (t + 1)).succ from rfl]
    exact Fin.snoc_last _ _

/-- Accessibility (Def. 2.4.17) is the reflexive-transitive closure of adjacency.  This is
`Digraph.accessible_iff_reflTransGen` (`Workspace.Prelim.BinaryRelations`), proved again
here; see the module docstring. -/
theorem accessible_iff_reflTransGen' (u v : Ω) :
    Y.Accessible u v ↔ Relation.ReflTransGen Y.Adj u v := by
  constructor
  · exact Y.accessible_rel (fun _ => Relation.ReflTransGen.refl)
      (fun h h' => h.trans h') (fun _ _ h => Relation.ReflTransGen.single h)
  · intro h
    induction h with
    | refl => exact Y.accessible_refl u
    | tail _ hbc ih => exact Y.accessible_snoc ih hbc

theorem accessible_trans {u v w : Ω} (h : Y.Accessible u v) (h' : Y.Accessible v w) :
    Y.Accessible u w := by
  rw [accessible_iff_reflTransGen'] at *
  exact h.trans h'

theorem accessible_of_adj {u v : Ω} (h : Y.Adj u v) : Y.Accessible u v :=
  Y.accessible_snoc (Y.accessible_refl u) h

/-- In a digraph whose edge relation is symmetric, accessibility is symmetric. -/
theorem accessible_symm (hsymm : ∀ a b, Y.Adj a b → Y.Adj b a) {u v : Ω}
    (h : Y.Accessible u v) : Y.Accessible v u := by
  refine Y.accessible_rel (r := fun a b => Y.Accessible b a) (fun x => Y.accessible_refl x)
    (fun hab hbc => Y.accessible_trans hbc hab) (fun a b hab => Y.accessible_of_adj (hsymm a b hab)) h

theorem symmetrization_adj_symm (a b : Ω) : Y.symmetrization.Adj a b → Y.symmetrization.Adj b a := by
  intro h
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- The weak component of `u` is the set of vertices weakly accessible from `u`
(weak accessibility is symmetric). -/
theorem weakComponent_eq_weaklyAccessible (u : Ω) :
    Y.weakComponent u = {v | Y.WeaklyAccessible u v} := by
  ext v
  constructor
  · rintro ⟨h, -⟩; exact h
  · intro h
    exact ⟨h, Y.symmetrization.accessible_symm Y.symmetrization_adj_symm h⟩

theorem weaklyAccessible_of_accessible {u v : Ω} (h : Y.Accessible u v) :
    Y.WeaklyAccessible u v := by
  refine Y.accessible_rel (r := fun a b => Y.WeaklyAccessible a b)
    (fun x => Y.symmetrization.accessible_refl x)
    (fun hab hbc => Y.symmetrization.accessible_trans hab hbc)
    (fun a b hab => Y.symmetrization.accessible_of_adj (Or.inl hab)) h

/-! `mem_weakComponent_self` and `weakComponent_eq_of_mem` now live in
`Workspace.Prelim.BinaryRelations`, next to Def. 2.4.21, together with the statement that
the weak components form a partition of the vertex set. -/

/-! ### Transpositions as digraph automorphisms

The digraph analogue of Observation 2.4.28 (which `Workspace.Prelim.BinaryRelations` proves
for bipartite graphs): the transposition `(x,y)` is an automorphism of a digraph exactly if
`x` and `y` have the same out- and in-neighbours outside `{x,y}`, and the four edges inside
`{x,y}` are matched up by the swap. -/

/-- A transposition is an automorphism of a digraph exactly if the two vertices have the
same out-neighbours and the same in-neighbours outside the pair `{x,y}`, and the edges
inside `{x,y}` are invariant under the swap. -/
theorem swap_mem_aut_iff [DecidableEq Ω] {x y : Ω} :
    Equiv.swap x y ∈ Y.Aut ↔
      ((∀ w, w ≠ x → w ≠ y → ((x, w) ∈ Y.E ↔ (y, w) ∈ Y.E)) ∧
        (∀ w, w ≠ x → w ≠ y → ((w, x) ∈ Y.E ↔ (w, y) ∈ Y.E)) ∧
        ((x, y) ∈ Y.E ↔ (y, x) ∈ Y.E) ∧ ((x, x) ∈ Y.E ↔ (y, y) ∈ Y.E)) := by
  constructor
  · intro hσ
    refine ⟨fun w hwx hwy => ?_, fun w hwx hwy => ?_, ?_, ?_⟩
    · have h1 := hσ y w
      rwa [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hwx hwy] at h1
    · have h1 := hσ w y
      rwa [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hwx hwy] at h1
    · have h1 := hσ y x
      rwa [Equiv.swap_apply_right, Equiv.swap_apply_left] at h1
    · have h1 := hσ y y
      rwa [Equiv.swap_apply_right] at h1
  · rintro ⟨hout, hin, hxy, hxx⟩ u v
    rcases eq_or_ne u x with rfl | hux
    · rcases eq_or_ne v u with rfl | hvx
      · rw [Equiv.swap_apply_left]; exact hxx.symm
      · rcases eq_or_ne v y with rfl | hvy
        · rw [Equiv.swap_apply_left, Equiv.swap_apply_right]; exact hxy.symm
        · rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hvx hvy]
          exact (hout v hvx hvy).symm
    · rcases eq_or_ne u y with rfl | huy
      · rcases eq_or_ne v x with rfl | hvx
        · rw [Equiv.swap_apply_right, Equiv.swap_apply_left]; exact hxy
        · rcases eq_or_ne v u with rfl | hvy
          · rw [Equiv.swap_apply_right]; exact hxx
          · rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hvx hvy]
            exact hout v hvx hvy
      · rcases eq_or_ne v x with rfl | hvx
        · rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hux huy]
          exact (hin u hux huy).symm
        · rcases eq_or_ne v y with rfl | hvy
          · rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hux huy]
            exact hin u hux huy
          · rw [Equiv.swap_apply_of_ne_of_ne hux huy, Equiv.swap_apply_of_ne_of_ne hvx hvy]

end Digraph

end Babai
