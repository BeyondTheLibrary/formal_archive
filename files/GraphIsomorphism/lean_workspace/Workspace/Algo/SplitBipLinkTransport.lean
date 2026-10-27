import Workspace.Algo.SplitBipRefine

/-! Section 9.4: transport of the link scans with their ordered vertex lists. -/

namespace Algo
open Babai RAM

private theorem sbipProduct_map (l r : List ℕ) (f : ℕ → ℕ) :
    (l.map f).product (r.map f) = (l.product r).map (fun q => (f q.1,f q.2)) := by
  induction l with
  | nil => simp [List.product]
  | cons a l ih =>
      simp only [List.product,List.map_cons,List.flatMap_cons,List.map_append,List.map_map,Function.comp_def] at *
      exact congrArg (List.append (r.map (fun b => (f a,f b)))) ih

/-- The ordered pair-color list does not change under a relabeling. -/
theorem sbipLinkColors_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (hp : RawWL.WF n 2 p) (hπ : RawPerm.WF n π)
    (l r : List ℕ) (hl : ∀ a ∈ l, a < n) (hr : ∀ b ∈ r, b < n) :
    sbipLinkColors (relabelWL (π,p),(permList π l,permList π r)) = sbipLinkColors (p,(l,r)) := by
  unfold sbipLinkColors
  rw [show (permList π l).product (permList π r) =
    (l.product r).map (fun q => (rawApply (π,q.1),rawApply (π,q.2))) from sbipProduct_map l r _]
  rw [List.map_map]
  apply List.map_congr_left
  intro q hq
  obtain ⟨hu,hv⟩ := List.mem_product.mp hq
  exact binColor_relabel hp hπ (hl q.1 hu) (hr q.2 hv)

/-- A second-part class transports its names and keeps its color. -/
theorem sbipSecondClass_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (hp : RawWL.WF n 2 p) (hπ : RawPerm.WF n π)
    (l r : List ℕ) (hr : ∀ b ∈ r, b < n) (k : ℕ) :
    sbipSecondClass ((relabelWL (π,p),(permList π l,permList π r)),k) =
      permList π (sbipSecondClass ((p,(l,r)),k)) :=
  sbipClass_relabel hp hπ hr (k+1)

/-- The useful-class predicate is unchanged under relabeling. -/
theorem sbipUseful_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (hp : RawWL.WF n 2 p) (hπ : RawPerm.WF n π)
    (l r : List ℕ) (hl : ∀ a ∈ l, a < n) (hr : ∀ b ∈ r, b < n) (k : ℕ) :
    sbipUseful ((relabelWL (π,p),(permList π l,permList π r)),k) = sbipUseful ((p,(l,r)),k) := by
  unfold sbipUseful
  rw [sbipSecondClass_relabel hp hπ l r hr]
  rw [sbipLinkColors_relabel hp hπ l _ hl
    (fun b hb => hr b ((sbipSecondClass_mem _ _ _).1 hb).1)]

/-- The list of useful diagonal colors keeps its order. -/
theorem sbipUsefulColors_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (hp : RawWL.WF n 2 p) (hπ : RawPerm.WF n π)
    (l r : List ℕ) (hl : ∀ a ∈ l, a < n) (hr : ∀ b ∈ r, b < n) :
    sbipUsefulColors (relabelWL (π,p),(permList π l,permList π r)) = sbipUsefulColors (p,(l,r)) := by
  have hc : sbipSecondColors (relabelWL (π,p),(permList π l,permList π r)) =
      sbipSecondColors (p,(l,r)) := by
    simp only [sbipSecondColors,permList,List.map_map]
    exact List.map_congr_left (fun b hb => binColor_relabel hp hπ (hr b hb) (hr b hb))
  unfold sbipUsefulColors
  rw [hc]
  exact List.filter_congr (fun k _ => sbipUseful_relabel hp hπ l r hl hr k)

/-- Section 9.4, step 7: the selected integer is invariant. -/
theorem sbipFirstNontrivial_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (hp : RawWL.WF n 2 p) (hπ : RawPerm.WF n π)
    (l r : List ℕ) (hl : ∀ a ∈ l, a < n) (hr : ∀ b ∈ r, b < n) :
    sbipFirstNontrivial (relabelWL (π,p),(permList π l,permList π r)) =
      sbipFirstNontrivial (p,(l,r)) :=
  congrArg upccCaseLeast (sbipUsefulColors_relabel hp hπ l r hl hr)

/-- Section 9.4, step 7: the whole retained class transports. -/
theorem sbipStep7Right_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (hp : RawWL.WF n 2 p) (hπ : RawPerm.WF n π)
    (l r : List ℕ) (hl : ∀ a ∈ l, a < n) (hr : ∀ b ∈ r, b < n) :
    sbipStep7Right (relabelWL (π,p),(permList π l,permList π r)) =
      permList π (sbipStep7Right (p,(l,r))) := by
  unfold sbipStep7Right
  rw [sbipFirstNontrivial_relabel hp hπ l r hl hr,sbipSecondClass_relabel hp hπ l r hr]

/-- Section 9.4, step 8: the first involved color is invariant. -/
theorem sbipFirstInvolved_relabel {n : ℕ} {p : RawConfig} {π : RawPerm}
    (hp : RawWL.WF n 2 p) (hπ : RawPerm.WF n π)
    (l r : List ℕ) (hl : ∀ a ∈ l, a < n) (hr : ∀ b ∈ r, b < n) :
    sbipFirstInvolved (relabelWL (π,p),(permList π l,permList π r)) =
      sbipFirstInvolved (p,(l,r)) :=
  congrArg upccCaseLeast (sbipLinkColors_relabel hp hπ l r hl hr)

/-- The second refinement has the same exact names along any isomorphism of
its constructed initial tables. The tables use list positions after restriction. -/
theorem sbipStep8Refine_transport (r s : RawSbipRefine)
    (e : Fin (r.1.2.1 ++ r.1.2.2).length ≃ Fin (s.1.2.1 ++ s.1.2.2).length)
    (hi : ∀ u v, namedBin _ (sbipIndexed (sbipStep8Initial s,s.1.2.1 ++ s.1.2.2)) (e u) (e v) =
      namedBin _ (sbipIndexed (sbipStep8Initial r,r.1.2.1 ++ r.1.2.2)) u v)
    (u v : Fin (r.1.2.1 ++ r.1.2.2).length) :
    binColor (sbipStep8Refine s,(e u,e v)) = binColor (sbipStep8Refine r,(u,v)) := by
  have hcard : (r.1.2.1 ++ r.1.2.2).length = (s.1.2.1 ++ s.1.2.2).length :=
    Nat.card_fin _ |>.symm.trans ((Nat.card_congr e).trans (Nat.card_fin _))
  rw [sbipStep8Refine,sbipStep3,← namedBin, namedBinary_stable (sbipIndexed_wf _ _),
    sbipStep8Refine,sbipStep3,← namedBin,namedBinary_stable (sbipIndexed_wf _ _)]
  have hr : (r.1.2.1 ++ r.1.2.2).length ^ 2 * (r.1.2.1 ++ r.1.2.2).length ^ 2 =
      (s.1.2.1 ++ s.1.2.2).length ^ 2 * (s.1.2.1 ++ s.1.2.2).length ^ 2 := by rw [hcard]
  rw [hr]
  exact WL.namedIter_map e hi _ u v

end Algo
