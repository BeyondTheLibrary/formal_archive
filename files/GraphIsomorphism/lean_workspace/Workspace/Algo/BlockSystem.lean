/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: a minimal block system, on raw data (§11.3, Reduce-to-Johnson, line 4).
-/
import Workspace.Algo.Blocks
import Workspace.Algo.Orbits
import Workspace.Machine.ListOps5
import Workspace.Luks.ReduceToJohnson
import Workspace.Prelim.BlockActionPrimitive

/-!
# Line 4 of Procedure Reduce-to-Johnson: "Find minimal block system `ℬ`"

§11.3, line 5048.  The paper gives no citation for this step; `Workspace/Algo/DESIGN.md`,
item 2, lists it as the largest **class-B** item — used, called well known, no source — so it
has to be proved.  This file is that proof.

A *minimal system of imprimitivity* (§11.1: "systems with at least two blocks that cannot be
made coarser, i.e. the blocks are maximal") is `Babai.IsMinimalSystemOfImprimitivity`.  The
action of `G` on such a system is primitive (`Babai.isPrimitive_onBlocks`), which is what
line 4 is for: line 5 and line 6 speak of the primitive group `Ḡ`.

## The route

Everything runs on a **labelling** `lab : List ℕ`, where `lab` has one entry per point and two
points are in the same class exactly when their entries agree (`Algo.LabRel`).  A labelling is
automatically an equivalence relation — it is the fibre relation of a function — so no
transitivity bookkeeping is needed anywhere.

* `Algo.mergeLab (lab, (s, t))` merges the classes of `s` and `t`: it relabels the class of `t`
  by the label of `s`.  It is the smallest coarsening that relates `s` and `t`
  (`Algo.mergeLab_least`).
* `Algo.labStep` is one round of the closure loop: for every generator `g` and every pair
  `u, v` of points in one class, merge the classes of `g(u)` and `g(v)`.
* `Algo.closeLab` runs `n(n+1)` rounds.  That is enough: a round that changes nothing leaves a
  relation closed under the generators (`Algo.labStep_closed_of_stable`), and a round that
  changes something adds a pair, of which there are at most `n²`.  The answer is the smallest
  `G`-congruence containing the relation one starts from (`Algo.closeLab_least`,
  `Algo.closeLab_closed`).
* `Algo.minLab` is line 4 itself: start from the singletons and run once through the points
  `b = 0, 1, …, n-1`, each time trying to merge the class of the point `0` with the class of
  `b` and closing up; keep the answer if it is still a proper partition, discard it otherwise.
  One pass suffices, because the class of `0` only grows: if `b` was discarded then the
  closure of the *current* class of `0` together with `b` was everything, hence so is the
  closure of the *final* class of `0` together with `b` (`Algo.minLab_spec`).
* `Algo.labBlocks` reads the classes off the labelling, and `Algo.rawMinBlocks` is line 4.

## Why the blocks are maximal

Let `C` be a block of imprimitivity containing the final class `B₀` of `0`, with `C ≠ Ω`, and
let `z ∈ C`.  The translates `σ(C)`, `σ ∈ G`, form a partition of `Ω`, hence a `G`-congruence
`Algo.transRel` containing the final labelling and not relating everything.  Running the pass
again against that congruence shows that the step at `b = z` must have been *kept*, so `z` lies
in `B₀`.  So `C = B₀`.

## Main definitions

`Algo.LabRel`, `Algo.mergeLab`, `Algo.labJobs`, `Algo.labStep`, `Algo.closeLab`,
`Algo.labBlocks`, `Algo.minLab`, `Algo.rawMinBlocks`.

## Main results

* `Algo.closeLab_closed`, `Algo.closeLab_least`, `Algo.closeLab_mono` — the closure loop;
* `Algo.rawMinBlocks_blocksWF`, `Algo.isMinimalSystemOfImprimitivity_rawMinBlocks` — **line 4**:
  the answer is a minimal system of imprimitivity of `decGroup n gs` on the domain;
* `Algo.isPrimitive_rawMinBlocks` — `Ḡ` is primitive on it (`Babai.IsPrimitive`);
* `Algo.blockData_rawMinBlocks` — the `Algo.BlockData` datum of `Workspace/Algo/Blocks.lean`;
* `Algo.polyFun_rawMinBlocks` — the running time.

No axiom, no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

/-! ## Labellings

A labelling is a list with one entry per point; the classes are its fibres. -/

/-- A **labelling** of the points `0, …, n-1`: `lab[u]` is the label of the class of `u`. -/
abbrev RawLab := List ℕ

/-- The label of a point. -/
def labAt (lab : RawLab) (u : ℕ) : ℕ := lab.getD u 0

/-- **Two points are in one class** when their labels agree. -/
def LabRel (lab : RawLab) (u v : ℕ) : Prop := labAt lab u = labAt lab v

theorem LabRel.refl (lab : RawLab) (u : ℕ) : LabRel lab u u := rfl

theorem LabRel.symm {lab : RawLab} {u v : ℕ} (h : LabRel lab u v) : LabRel lab v u := Eq.symm h

theorem LabRel.trans {lab : RawLab} {u v w : ℕ} (h : LabRel lab u v) (h' : LabRel lab v w) :
    LabRel lab u w := Eq.trans h h'

instance (lab : RawLab) (u v : ℕ) : Decidable (LabRel lab u v) := by
  unfold LabRel; infer_instance

/-- **An abstract congruence**: a relation on the points that is symmetric, transitive and
carried along by the generators.  This is what `Algo.closeLab` is least among. -/
structure CongrOn (n : ℕ) (gs : RawGens) (r : ℕ → ℕ → Prop) : Prop where
  /-- symmetry -/
  symm : ∀ {u v : ℕ}, r u v → r v u
  /-- transitivity -/
  trans : ∀ {u v w : ℕ}, r u v → r v w → r u w
  /-- the generators carry the relation along -/
  closed : ∀ g ∈ gs, ∀ u < n, ∀ v < n, r u v → r (rawApply (g, u)) (rawApply (g, v))

/-- A labelling that the generators carry along. -/
def LabClosed (n : ℕ) (gs : RawGens) (lab : RawLab) : Prop :=
  ∀ g ∈ gs, ∀ u < n, ∀ v < n, LabRel lab u v → LabRel lab (rawApply (g, u)) (rawApply (g, v))

theorem congrOn_labRel {n : ℕ} {gs : RawGens} {lab : RawLab} (h : LabClosed n gs lab) :
    CongrOn n gs (LabRel lab) :=
  ⟨fun h' => h'.symm, fun h' h'' => h'.trans h'', h⟩

/-! ## Merging two classes -/

/-- **Merging the classes of two points**: every point labelled like `t` is relabelled like
`s`. -/
def mergeLab (p : RawLab × (ℕ × ℕ)) : RawLab :=
  p.1.map (fun x => if x = labAt p.1 p.2.2 then labAt p.1 p.2.1 else x)

@[simp] theorem length_mergeLab (lab : RawLab) (q : ℕ × ℕ) :
    (mergeLab (lab, q)).length = lab.length := by simp [mergeLab]

/-- The label of a point after a merge. -/
theorem labAt_mergeLab (lab : RawLab) (s t u : ℕ) (hu : u < lab.length) :
    labAt (mergeLab (lab, (s, t))) u =
      if labAt lab u = labAt lab t then labAt lab s else labAt lab u := by
  have h1 : labAt (mergeLab (lab, (s, t))) u
      = (mergeLab (lab, (s, t)))[u]'(by simpa using hu) :=
    List.getD_eq_getElem _ _ (by simpa using hu)
  have h2 : labAt lab u = lab[u]'hu := List.getD_eq_getElem _ _ hu
  rw [h1, h2]
  show (lab.map (fun x => if x = labAt lab t then labAt lab s else x))[u]'_ = _
  rw [List.getElem_map, ← h2]

/-- Every entry of a merge was an entry, or is the default `0`. -/
theorem mem_mergeLab {lab : RawLab} {q : ℕ × ℕ} {e : ℕ} (he : e ∈ mergeLab (lab, q)) :
    e ∈ lab ∨ e = 0 := by
  obtain ⟨x, hx, hxe⟩ := List.mem_map.1 he
  by_cases hcase : x = labAt lab q.2
  · rw [if_pos hcase] at hxe
    subst hxe
    rcases Nat.lt_or_ge q.1 lab.length with hlt | hge
    · refine Or.inl ?_
      show lab.getD q.1 0 ∈ lab
      rw [List.getD_eq_getElem _ _ hlt]
      exact List.getElem_mem hlt
    · exact Or.inr (List.getD_eq_default _ _ hge)
  · rw [if_neg hcase] at hxe
    exact Or.inl (hxe ▸ hx)

/-- **A merge only coarsens.** -/
theorem labRel_mergeLab_of_labRel {lab : RawLab} {s t u v : ℕ} (hu : u < lab.length)
    (hv : v < lab.length) (h : LabRel lab u v) : LabRel (mergeLab (lab, (s, t))) u v := by
  unfold LabRel at h ⊢
  rw [labAt_mergeLab lab s t u hu, labAt_mergeLab lab s t v hv, h]

/-- **A merge relates the two points.** -/
theorem labRel_mergeLab_pair (lab : RawLab) {s t : ℕ} (hs : s < lab.length)
    (ht : t < lab.length) : LabRel (mergeLab (lab, (s, t))) s t := by
  unfold LabRel
  rw [labAt_mergeLab lab s t s hs, labAt_mergeLab lab s t t ht, if_pos rfl]
  split <;> rfl

/-- **A merge is the least coarsening that relates the two points.** -/
theorem mergeLab_least {n : ℕ} {lab : RawLab} {r : ℕ → ℕ → Prop} {s t : ℕ}
    (hsymm : ∀ {a b : ℕ}, r a b → r b a) (htrans : ∀ {a b c : ℕ}, r a b → r b c → r a c)
    (hlab : ∀ u < n, ∀ v < n, LabRel lab u v → r u v) (hst : r s t)
    (hs : s < n) (ht : t < n) (hlen : n ≤ lab.length) :
    ∀ u < n, ∀ v < n, LabRel (mergeLab (lab, (s, t))) u v → r u v := by
  intro u hu v hv h
  unfold LabRel at h
  rw [labAt_mergeLab lab s t u (lt_of_lt_of_le hu hlen),
    labAt_mergeLab lab s t v (lt_of_lt_of_le hv hlen)] at h
  by_cases hut : labAt lab u = labAt lab t <;> by_cases hvt : labAt lab v = labAt lab t
  · exact hlab u hu v hv (hut.trans hvt.symm)
  · rw [if_pos hut, if_neg hvt] at h
    -- `u ~ t`, and `v` has the label of `s`
    exact htrans (htrans (hlab u hu t ht hut) (hsymm hst)) (hlab s hs v hv h)
  · rw [if_neg hut, if_pos hvt] at h
    exact htrans (htrans (hlab u hu s hs h) hst) (hsymm (hlab v hv t ht hvt))
  · rw [if_neg hut, if_neg hvt] at h
    exact hlab u hu v hv h

/-! ## One round of the closure loop -/

/-- **The ordered pairs of points.** -/
def labPairsList (dom : List ℕ) : List (ℕ × ℕ) :=
  ((List.range dom.length).map (fun u => (List.range dom.length).map (fun v => (u, v)))).flatten

theorem mem_labPairsList {dom : List ℕ} {u v : ℕ} :
    (u, v) ∈ labPairsList dom ↔ u < dom.length ∧ v < dom.length := by
  constructor
  · intro h
    obtain ⟨L, hL, hmem⟩ := List.mem_flatten.1 h
    obtain ⟨u', hu', rfl⟩ := List.mem_map.1 hL
    obtain ⟨v', hv', heq⟩ := List.mem_map.1 hmem
    obtain ⟨rfl, rfl⟩ : u' = u ∧ v' = v := by simpa [Prod.ext_iff] using heq
    exact ⟨List.mem_range.1 hu', List.mem_range.1 hv'⟩
  · rintro ⟨hu, hv⟩
    exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨u, List.mem_range.2 hu, rfl⟩,
      List.mem_map.2 ⟨v, List.mem_range.2 hv, rfl⟩⟩

/-- **The jobs of one round**: for every generator and every ordered pair of points, the
merge to perform if the pair is in one class. -/
def labJobs (p : RawGens × List ℕ) : List (RawPerm × (ℕ × ℕ)) :=
  (p.1.map (fun g => (labPairsList p.2).map (fun q => (g, q)))).flatten

theorem mem_labJobs {gs : RawGens} {dom : List ℕ} {g : RawPerm} {u v : ℕ} :
    (g, (u, v)) ∈ labJobs (gs, dom) ↔ g ∈ gs ∧ u < dom.length ∧ v < dom.length := by
  constructor
  · intro h
    obtain ⟨L, hL, hmem⟩ := List.mem_flatten.1 h
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hL
    obtain ⟨q, hq, heq⟩ := List.mem_map.1 hmem
    obtain ⟨rfl, rfl⟩ : g' = g ∧ q = (u, v) := by simpa [Prod.ext_iff] using heq
    exact ⟨hg', mem_labPairsList.1 hq⟩
  · rintro ⟨hg, hu, hv⟩
    exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨g, hg, rfl⟩,
      List.mem_map.2 ⟨(u, v), mem_labPairsList.2 ⟨hu, hv⟩, rfl⟩⟩

/-- **One job**: merge the images of a pair that is in one class. -/
def mergeJob (p : RawLab × (RawPerm × (ℕ × ℕ))) : RawLab :=
  if labAt p.1 p.2.2.1 = labAt p.1 p.2.2.2 then
    mergeLab (p.1, (rawApply (p.2.1, p.2.2.1), rawApply (p.2.1, p.2.2.2)))
  else p.1

@[simp] theorem length_mergeJob (lab : RawLab) (j : RawPerm × (ℕ × ℕ)) :
    (mergeJob (lab, j)).length = lab.length := by
  unfold mergeJob; split <;> simp

theorem mem_mergeJob {lab : RawLab} {j : RawPerm × (ℕ × ℕ)} {e : ℕ}
    (he : e ∈ mergeJob (lab, j)) : e ∈ lab ∨ e = 0 := by
  unfold mergeJob at he
  split at he
  · exact mem_mergeLab he
  · exact Or.inl he

theorem labRel_mergeJob_of_labRel {lab : RawLab} {j : RawPerm × (ℕ × ℕ)} {u v : ℕ}
    (hu : u < lab.length) (hv : v < lab.length) (h : LabRel lab u v) :
    LabRel (mergeJob (lab, j)) u v := by
  unfold mergeJob
  split
  · exact labRel_mergeLab_of_labRel hu hv h
  · exact h

/-- **One round.** -/
def labStep (p : (RawGens × List ℕ) × RawLab) : RawLab :=
  (labJobs p.1).foldl (fun l j => mergeJob (l, j)) p.2

/-! ### The fold over the jobs -/

theorem length_foldl_mergeJob : ∀ (js : List (RawPerm × (ℕ × ℕ))) (lab : RawLab),
    (js.foldl (fun l j => mergeJob (l, j)) lab).length = lab.length := by
  intro js
  induction js with
  | nil => intro lab; rfl
  | cons j t ih => intro lab; rw [List.foldl_cons, ih, length_mergeJob]

theorem mem_foldl_mergeJob : ∀ (js : List (RawPerm × (ℕ × ℕ))) (lab : RawLab) {e : ℕ},
    e ∈ js.foldl (fun l j => mergeJob (l, j)) lab → e ∈ lab ∨ e = 0 := by
  intro js
  induction js with
  | nil => intro lab e he; exact Or.inl he
  | cons j t ih =>
      intro lab e he
      rw [List.foldl_cons] at he
      rcases ih _ he with h | h
      · exact mem_mergeJob h
      · exact Or.inr h

theorem labRel_foldl_mergeJob_of_labRel : ∀ (js : List (RawPerm × (ℕ × ℕ))) (lab : RawLab)
    {u v : ℕ}, u < lab.length → v < lab.length → LabRel lab u v →
      LabRel (js.foldl (fun l j => mergeJob (l, j)) lab) u v := by
  intro js
  induction js with
  | nil => intro lab u v _ _ h; exact h
  | cons j t ih =>
      intro lab u v hu hv h
      rw [List.foldl_cons]
      exact ih _ (by rw [length_mergeJob]; exact hu) (by rw [length_mergeJob]; exact hv)
        (labRel_mergeJob_of_labRel hu hv h)

/-- **Every job is done**: if a pair is in one class at the start of the round, the images of
the pair are in one class at the end of the round. -/
theorem labRel_image_foldl : ∀ (js : List (RawPerm × (ℕ × ℕ))) (lab : RawLab)
    {g : RawPerm} {u v : ℕ}, (g, (u, v)) ∈ js → u < lab.length → v < lab.length →
      rawApply (g, u) < lab.length → rawApply (g, v) < lab.length → LabRel lab u v →
      LabRel (js.foldl (fun l j => mergeJob (l, j)) lab) (rawApply (g, u)) (rawApply (g, v)) := by
  intro js
  induction js with
  | nil => intro lab g u v hj; exact absurd hj (by simp)
  | cons j t ih =>
      intro lab g u v hj hu hv hgu hgv h
      rw [List.foldl_cons]
      rcases List.mem_cons.1 hj with rfl | hj'
      · -- the head is the job: it merges the two images
        have hmerge : LabRel (mergeJob (lab, (g, (u, v)))) (rawApply (g, u)) (rawApply (g, v)) := by
          have heq : mergeJob (lab, (g, (u, v)))
              = mergeLab (lab, (rawApply (g, u), rawApply (g, v))) := by
            show (if labAt lab u = labAt lab v then _ else lab) = _
            rw [if_pos (show labAt lab u = labAt lab v from h)]
          rw [heq]
          exact labRel_mergeLab_pair lab hgu hgv
        exact labRel_foldl_mergeJob_of_labRel t _ (by rw [length_mergeJob]; exact hgu)
          (by rw [length_mergeJob]; exact hgv) hmerge
      · exact ih _ hj' (by rw [length_mergeJob]; exact hu) (by rw [length_mergeJob]; exact hv)
          (by rw [length_mergeJob]; exact hgu) (by rw [length_mergeJob]; exact hgv)
          (labRel_mergeJob_of_labRel hu hv h)

theorem foldl_mergeJob_least {n : ℕ} {gs : RawGens} {r : ℕ → ℕ → Prop} (hr : CongrOn n gs r)
    (hwf : RawGens.WF n gs) : ∀ (js : List (RawPerm × (ℕ × ℕ))) (lab : RawLab),
      (∀ j ∈ js, j.1 ∈ gs ∧ j.2.1 < n ∧ j.2.2 < n) → n ≤ lab.length →
      (∀ u < n, ∀ v < n, LabRel lab u v → r u v) →
      ∀ u < n, ∀ v < n, LabRel (js.foldl (fun l j => mergeJob (l, j)) lab) u v → r u v := by
  intro js
  induction js with
  | nil => intro lab _ _ h; exact h
  | cons j t ih =>
      intro lab hjs hlen hlab
      rw [List.foldl_cons]
      obtain ⟨hg, hu, hv⟩ := hjs j (List.mem_cons_self ..)
      refine ih _ (fun j' hj' => hjs j' (List.mem_cons_of_mem _ hj'))
        (by rw [length_mergeJob]; exact hlen) ?_
      -- one job stays inside `r`
      unfold mergeJob
      split
      · rename_i hcase
        have hguv : r (rawApply (j.1, j.2.1)) (rawApply (j.1, j.2.2)) :=
          hr.closed j.1 hg _ hu _ hv (hlab _ hu _ hv hcase)
        have hgu : rawApply (j.1, j.2.1) < n := by
          rw [rawApply_of_wf (hwf j.1 hg) hu]; exact Fin.isLt _
        have hgv : rawApply (j.1, j.2.2) < n := by
          rw [rawApply_of_wf (hwf j.1 hg) hv]; exact Fin.isLt _
        exact mergeLab_least hr.symm hr.trans hlab hguv hgu hgv hlen
      · exact hlab

/-! ### The round -/

@[simp] theorem length_labStep (q : RawGens × List ℕ) (lab : RawLab) :
    (labStep (q, lab)).length = lab.length := length_foldl_mergeJob _ _

theorem mem_labStep {q : RawGens × List ℕ} {lab : RawLab} {e : ℕ} (he : e ∈ labStep (q, lab)) :
    e ∈ lab ∨ e = 0 := mem_foldl_mergeJob _ _ he

theorem labStep_mono {q : RawGens × List ℕ} {lab : RawLab} {u v : ℕ} (hu : u < lab.length)
    (hv : v < lab.length) (h : LabRel lab u v) : LabRel (labStep (q, lab)) u v :=
  labRel_foldl_mergeJob_of_labRel _ _ hu hv h

theorem labStep_least {n : ℕ} {gs : RawGens} {dom : List ℕ} {r : ℕ → ℕ → Prop}
    (hr : CongrOn n gs r) (hwf : RawGens.WF n gs) (hdom : dom.length = n) {lab : RawLab}
    (hlen : n ≤ lab.length) (hlab : ∀ u < n, ∀ v < n, LabRel lab u v → r u v) :
    ∀ u < n, ∀ v < n, LabRel (labStep ((gs, dom), lab)) u v → r u v :=
  foldl_mergeJob_least hr hwf _ _
    (fun j hj => by
      obtain ⟨hg, hu, hv⟩ := mem_labJobs.1 (show (j.1, (j.2.1, j.2.2)) ∈ labJobs (gs, dom) from hj)
      exact ⟨hg, hdom ▸ hu, hdom ▸ hv⟩)
    hlen hlab

/-- **A round that changes nothing leaves a closed labelling.** -/
theorem labStep_closed_of_stable {n : ℕ} {gs : RawGens} {dom : List ℕ} (hwf : RawGens.WF n gs)
    (hdom : dom.length = n) {lab : RawLab} (hlen : n ≤ lab.length)
    (hstable : ∀ u < n, ∀ v < n, LabRel (labStep ((gs, dom), lab)) u v → LabRel lab u v) :
    LabClosed n gs lab := by
  intro g hg u hu v hv h
  have hgu : rawApply (g, u) < n := by rw [rawApply_of_wf (hwf g hg) hu]; exact Fin.isLt _
  have hgv : rawApply (g, v) < n := by rw [rawApply_of_wf (hwf g hg) hv]; exact Fin.isLt _
  refine hstable _ hgu _ hgv ?_
  exact labRel_image_foldl _ _ (mem_labJobs.2 ⟨hg, by omega, by omega⟩)
    (lt_of_lt_of_le hu hlen) (lt_of_lt_of_le hv hlen) (lt_of_lt_of_le hgu hlen)
    (lt_of_lt_of_le hgv hlen) h

/-! ## The closure loop

The loop runs `n(n+1)` rounds.  The count arrives as the length of a list, never as a machine
natural, for the reason recorded at the end of `Workspace/Machine/DESIGN.md`. -/

/-- **The rounds of the closure loop**, `n(n+1)` of them. -/
def labRounds (dom : List ℕ) : List ℕ :=
  ((List.range dom.length).map (fun u => u :: List.range dom.length)).flatten

theorem length_labRounds (dom : List ℕ) :
    (labRounds dom).length = dom.length * (dom.length + 1) := by
  rw [labRounds, List.length_flatten, List.map_map]
  have : ((List.range dom.length).map (List.length ∘ (fun u => u :: List.range dom.length)))
      = List.replicate dom.length (dom.length + 1) := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp, ?_⟩
    intro b hb
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hb
    simp
  rw [this, List.sum_replicate, smul_eq_mul]

/-- **The closure of a labelling**: the smallest `G`-congruence that coarsens it. -/
def closeLab (p : (RawGens × List ℕ) × RawLab) : RawLab :=
  (labRounds p.1.2).foldl (fun l _ => labStep (p.1, l)) p.2

theorem closeLab_eq_iterate (q : RawGens × List ℕ) (lab : RawLab) :
    closeLab (q, lab) = (fun l => labStep (q, l))^[(labRounds q.2).length] lab :=
  foldl_const_eq_iterate _ _

/-! ### The iteration -/

section Iterate

variable {n : ℕ} {gs : RawGens} {dom : List ℕ}

theorem length_labIterate (q : RawGens × List ℕ) (lab : RawLab) :
    ∀ k : ℕ, ((fun l => labStep (q, l))^[k] lab).length = lab.length := by
  intro k
  induction k generalizing lab with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ih, length_labStep]

theorem labIterate_mono (q : RawGens × List ℕ) : ∀ (k : ℕ) (lab : RawLab) {u v : ℕ},
    u < lab.length → v < lab.length → LabRel lab u v →
      LabRel ((fun l => labStep (q, l))^[k] lab) u v := by
  intro k
  induction k with
  | zero => intro lab u v _ _ h; exact h
  | succ k ih =>
      intro lab u v hu hv h
      rw [Function.iterate_succ_apply]
      exact ih _ (by rw [length_labStep]; exact hu) (by rw [length_labStep]; exact hv)
        (labStep_mono hu hv h)

theorem labIterate_least {r : ℕ → ℕ → Prop} (hr : CongrOn n gs r) (hwf : RawGens.WF n gs)
    (hdom : dom.length = n) : ∀ (k : ℕ) (lab : RawLab), n ≤ lab.length →
      (∀ u < n, ∀ v < n, LabRel lab u v → r u v) →
      ∀ u < n, ∀ v < n, LabRel ((fun l => labStep ((gs, dom), l))^[k] lab) u v → r u v := by
  intro k
  induction k with
  | zero => intro lab _ hlab; exact hlab
  | succ k ih =>
      intro lab hlen hlab
      rw [Function.iterate_succ_apply]
      exact ih _ (by rw [length_labStep]; exact hlen) (labStep_least hr hwf hdom hlen hlab)

/-! ### The counting argument -/

/-- The pairs of points in one class, as a finite set. -/
def labPairs (n : ℕ) (lab : RawLab) : Finset (ℕ × ℕ) :=
  ((Finset.range n) ×ˢ (Finset.range n)).filter (fun p => labAt lab p.1 = labAt lab p.2)

theorem mem_labPairs {n : ℕ} {lab : RawLab} {p : ℕ × ℕ} :
    p ∈ labPairs n lab ↔ p.1 < n ∧ p.2 < n ∧ LabRel lab p.1 p.2 := by
  simp only [labPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

theorem card_labPairs_le (n : ℕ) (lab : RawLab) : (labPairs n lab).card ≤ n * n := by
  have h := Finset.card_filter_le ((Finset.range n) ×ˢ (Finset.range n))
    (fun p => labAt lab p.1 = labAt lab p.2)
  simpa [labPairs] using h

theorem labPairs_subset {n : ℕ} {lab lab' : RawLab}
    (h : ∀ u < n, ∀ v < n, LabRel lab u v → LabRel lab' u v) :
    labPairs n lab ⊆ labPairs n lab' := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := mem_labPairs.1 hp
  exact mem_labPairs.2 ⟨h1, h2, h _ h1 _ h2 h3⟩

/-- **The counting step**: either some round leaves the relation as it was, or the relation has
grown in each round so far. -/
theorem exists_stable_round (q : RawGens × List ℕ) (lab : RawLab) {n : ℕ}
    (hlen : n ≤ lab.length) : ∀ N : ℕ,
      (∃ k < N, ∀ u < n, ∀ v < n,
        LabRel ((fun l => labStep (q, l))^[k + 1] lab) u v →
          LabRel ((fun l => labStep (q, l))^[k] lab) u v) ∨
      N ≤ (labPairs n ((fun l => labStep (q, l))^[N] lab)).card := by
  intro N
  induction N with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ N ih =>
      rcases ih with ⟨k, hk, hstable⟩ | hcard
      · exact Or.inl ⟨k, by omega, hstable⟩
      by_cases hst : ∀ u < n, ∀ v < n,
          LabRel ((fun l => labStep (q, l))^[N + 1] lab) u v →
            LabRel ((fun l => labStep (q, l))^[N] lab) u v
      · exact Or.inl ⟨N, by omega, hst⟩
      · right
        push_neg at hst
        obtain ⟨u, hu, v, hv, hrel, hnot⟩ := hst
        have hsub : labPairs n ((fun l => labStep (q, l))^[N] lab)
            ⊆ labPairs n ((fun l => labStep (q, l))^[N + 1] lab) := by
          refine labPairs_subset (fun a ha b hb hab => ?_)
          rw [Function.iterate_succ_apply']
          exact labStep_mono (by rw [length_labIterate]; omega)
            (by rw [length_labIterate]; omega) hab
        have hssub : labPairs n ((fun l => labStep (q, l))^[N] lab)
            ⊂ labPairs n ((fun l => labStep (q, l))^[N + 1] lab) := by
          refine Finset.ssubset_iff_of_subset hsub |>.2 ⟨(u, v), ?_, ?_⟩
          · exact mem_labPairs.2 ⟨hu, hv, hrel⟩
          · intro hcon
            exact hnot (mem_labPairs.1 hcon).2.2
        have := Finset.card_lt_card hssub
        omega

theorem mem_labIterate (q : RawGens × List ℕ) : ∀ (k : ℕ) (lab : RawLab) {e : ℕ},
    e ∈ (fun l => labStep (q, l))^[k] lab → e ∈ lab ∨ e = 0 := by
  intro k
  induction k with
  | zero => intro lab e he; exact Or.inl he
  | succ k ih =>
      intro lab e he
      rw [Function.iterate_succ_apply] at he
      rcases ih _ he with h | h
      · exact mem_labStep h
      · exact Or.inr h

/-- **Once the relation stops growing it never grows again.** -/
theorem labIterate_stable_forever (hwf : RawGens.WF n gs) (hdom : dom.length = n)
    {lab : RawLab} (hlen : n ≤ lab.length) {k : ℕ}
    (hstable : ∀ u < n, ∀ v < n,
      LabRel ((fun l => labStep ((gs, dom), l))^[k + 1] lab) u v →
        LabRel ((fun l => labStep ((gs, dom), l))^[k] lab) u v) :
    ∀ j : ℕ, ∀ u < n, ∀ v < n,
      LabRel ((fun l => labStep ((gs, dom), l))^[k + j] lab) u v →
        LabRel ((fun l => labStep ((gs, dom), l))^[k] lab) u v := by
  set F : RawLab → RawLab := fun l => labStep ((gs, dom), l) with hF
  set L : RawLab := F^[k] lab with hL
  have hLlen : n ≤ L.length := by rw [hL, length_labIterate]; exact hlen
  have hstep : F^[k + 1] lab = labStep ((gs, dom), L) := by
    rw [hL]
    exact Function.iterate_succ_apply' F k lab
  have hclosed : LabClosed n gs L := by
    refine labStep_closed_of_stable hwf hdom hLlen (fun u hu v hv h => ?_)
    exact hstable u hu v hv (by rw [hstep]; exact h)
  intro j u hu v hv h
  have hj : F^[k + j] lab = F^[j] L := by
    rw [hL, ← Function.iterate_add_apply F j k lab, Nat.add_comm]
  rw [hj] at h
  exact labIterate_least (congrOn_labRel hclosed) hwf hdom j L hLlen
    (fun a _ b _ hab => hab) u hu v hv h

end Iterate

/-! ### The specification of the closure -/

section Closure

variable {n : ℕ} {gs : RawGens} {dom : List ℕ}

@[simp] theorem length_closeLab (q : RawGens × List ℕ) (lab : RawLab) :
    (closeLab (q, lab)).length = lab.length := by
  rw [closeLab_eq_iterate, length_labIterate]

theorem mem_closeLab {q : RawGens × List ℕ} {lab : RawLab} {e : ℕ} (he : e ∈ closeLab (q, lab)) :
    e ∈ lab ∨ e = 0 := by
  rw [closeLab_eq_iterate] at he
  exact mem_labIterate q _ lab he

/-- **The closure coarsens.** -/
theorem closeLab_mono {q : RawGens × List ℕ} {lab : RawLab} {u v : ℕ} (hu : u < lab.length)
    (hv : v < lab.length) (h : LabRel lab u v) : LabRel (closeLab (q, lab)) u v := by
  rw [closeLab_eq_iterate]
  exact labIterate_mono q _ lab hu hv h

/-- **The closure is least**: it sits inside every congruence that coarsens the labelling. -/
theorem closeLab_least {r : ℕ → ℕ → Prop} (hr : CongrOn n gs r) (hwf : RawGens.WF n gs)
    (hdom : dom.length = n) {lab : RawLab} (hlen : n ≤ lab.length)
    (hlab : ∀ u < n, ∀ v < n, LabRel lab u v → r u v) :
    ∀ u < n, ∀ v < n, LabRel (closeLab ((gs, dom), lab)) u v → r u v := by
  rw [closeLab_eq_iterate]
  exact labIterate_least hr hwf hdom _ lab hlen hlab

/-- **The closure is closed**: the generators carry it along.  This is where the round count
`n(n+1)` is used. -/
theorem closeLab_closed (hwf : RawGens.WF n gs) (hdom : dom.length = n) {lab : RawLab}
    (hlen : n ≤ lab.length) : LabClosed n gs (closeLab ((gs, dom), lab)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro g _ u hu; exact absurd hu (by omega)
  set F : RawLab → RawLab := fun l => labStep ((gs, dom), l) with hF
  set N : ℕ := (labRounds dom).length with hN
  have hNval : N = n * (n + 1) := by rw [hN, length_labRounds, hdom]
  -- some round leaves the relation as it was
  have hex : ∃ k < N, ∀ u < n, ∀ v < n,
      LabRel (F^[k + 1] lab) u v → LabRel (F^[k] lab) u v := by
    rcases exists_stable_round (gs, dom) lab hlen N with h | h
    · exact h
    · exfalso
      have hcard := card_labPairs_le n (F^[N] lab)
      have : N ≤ n * n := le_trans h hcard
      rw [hNval] at this
      nlinarith
  obtain ⟨k, hkN, hstable⟩ := hex
  -- the relation is the same at the round `k` and at the end
  have hle : ∀ u < n, ∀ v < n, LabRel (F^[N] lab) u v → LabRel (F^[k] lab) u v := by
    intro u hu v hv h
    have hNk : N = k + (N - k) := by omega
    rw [hNk] at h
    exact labIterate_stable_forever hwf hdom hlen hstable (N - k) u hu v hv h
  have hge : ∀ u < n, ∀ v < n, LabRel (F^[k] lab) u v → LabRel (F^[N] lab) u v := by
    intro u hu v hv h
    have hNk : N = (N - k) + k := by omega
    rw [hNk, Function.iterate_add_apply]
    exact labIterate_mono (gs, dom) _ _ (by rw [length_labIterate]; omega)
      (by rw [length_labIterate]; omega) h
  -- the relation at the round `k` is closed
  have hclosed : LabClosed n gs (F^[k] lab) := by
    refine labStep_closed_of_stable hwf hdom (by rw [length_labIterate]; exact hlen)
      (fun u hu v hv h => ?_)
    refine hstable u hu v hv ?_
    have hsucc : F^[k + 1] lab = labStep ((gs, dom), F^[k] lab) :=
      Function.iterate_succ_apply' F k lab
    rw [hsucc]
    exact h
  intro g hg u hu v hv h
  have hgu : rawApply (g, u) < n := by rw [rawApply_of_wf (hwf g hg) hu]; exact Fin.isLt _
  have hgv : rawApply (g, v) < n := by rw [rawApply_of_wf (hwf g hg) hv]; exact Fin.isLt _
  rw [closeLab_eq_iterate] at h ⊢
  exact hge _ hgu _ hgv (hclosed g hg u hu v hv (hle u hu v hv h))

end Closure

/-! ## The classes of a labelling, as a block system -/

/-- **The class of a point**, as a list of points. -/
def labClass (dom : List ℕ) (lab : RawLab) (u : ℕ) : List ℕ :=
  (List.range dom.length).filter (fun v => decide (labAt lab v = labAt lab u))

theorem mem_labClass {dom : List ℕ} {lab : RawLab} {u v : ℕ} :
    v ∈ labClass dom lab u ↔ v < dom.length ∧ LabRel lab v u := by
  simp [labClass, List.mem_filter, List.mem_range, LabRel]

theorem self_mem_labClass {dom : List ℕ} {lab : RawLab} {u : ℕ} (hu : u < dom.length) :
    u ∈ labClass dom lab u := mem_labClass.2 ⟨hu, rfl⟩

/-- **The block system a labelling describes**: its classes, one per label. -/
def labBlocks (p : List ℕ × RawLab) : RawBlocks :=
  (dedupG ([], (List.range p.1.length).map (fun u => labAt p.2 u))).map
    (fun c => (List.range p.1.length).filter (fun v => decide (labAt p.2 v = c)))

theorem mem_labBlocks {dom : List ℕ} {lab : RawLab} {B : List ℕ} :
    B ∈ labBlocks (dom, lab) ↔ ∃ u < dom.length, B = labClass dom lab u := by
  constructor
  · intro hB
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hB
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ((mem_dedupG_nil _ _).1 hc)
    exact ⟨u, by simpa using hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    refine List.mem_map.2 ⟨labAt lab u, ?_, rfl⟩
    exact (mem_dedupG_nil _ _).2 (List.mem_map.2 ⟨u, List.mem_range.2 hu, rfl⟩)

theorem blocksWF_labBlocks {n : ℕ} {dom : List ℕ} (hdom : dom.length = n) (lab : RawLab) :
    BlocksWF n (labBlocks (dom, lab)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro B hB hcon
    obtain ⟨u, hu, rfl⟩ := mem_labBlocks.1 hB
    have := self_mem_labClass (dom := dom) (lab := lab) hu
    rw [hcon] at this
    exact absurd this List.not_mem_nil
  · intro w hw
    obtain ⟨B, hB, hwB⟩ := List.mem_flatten.1 hw
    obtain ⟨u, hu, rfl⟩ := mem_labBlocks.1 hB
    exact hdom ▸ (mem_labClass.1 hwB).1
  · rw [List.nodup_flatten]
    constructor
    · intro B hB
      obtain ⟨u, hu, rfl⟩ := mem_labBlocks.1 hB
      exact List.Nodup.filter _ (List.nodup_range)
    · show List.Pairwise _ (List.map _ _)
      refine List.pairwise_map.2 ((nodup_dedupG _).imp ?_)
      intro c c' hne a ha ha'
      have h1 : labAt lab a = c := of_decide_eq_true (List.mem_filter.1 ha).2
      have h2 : labAt lab a = c' := of_decide_eq_true (List.mem_filter.1 ha').2
      exact hne (h1.symm.trans h2)

/-- **The class of a point**, as a subset of the domain. -/
def labSet (n : ℕ) (lab : RawLab) (u : ℕ) : Set (Fin n) := {x | LabRel lab (x : ℕ) u}

theorem mem_labSet {n : ℕ} {lab : RawLab} {u : ℕ} {x : Fin n} :
    x ∈ labSet n lab u ↔ LabRel lab (x : ℕ) u := Iff.rfl

theorem winSet_labClass {n : ℕ} {dom : List ℕ} {lab : RawLab} {u : ℕ} (hdom : dom.length = n) :
    winSet n (labClass dom lab u) = labSet n lab u := by
  ext x
  rw [mem_winSet, mem_labClass, mem_labSet]
  exact ⟨fun h => h.2, fun h => ⟨by rw [hdom]; exact x.isLt, h⟩⟩

theorem mem_blockSets_labBlocks {n : ℕ} {dom : List ℕ} {lab : RawLab} (hdom : dom.length = n)
    {S : Set (Fin n)} :
    S ∈ blockSets n (labBlocks (dom, lab)) ↔ ∃ u < n, S = labSet n lab u := by
  constructor
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨u, hu, rfl⟩ := mem_labBlocks.1 hB
    exact ⟨u, hdom ▸ hu, (winSet_labClass hdom).symm ▸ rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨labClass dom lab u, mem_labBlocks.2 ⟨u, by omega, rfl⟩, winSet_labClass hdom⟩

/-- Two classes are equal or disjoint, and equal exactly when their points are related. -/
theorem labSet_eq_of_labRel {n : ℕ} {lab : RawLab} {u v : ℕ} (h : LabRel lab u v) :
    labSet n lab u = labSet n lab v := by
  ext x
  exact ⟨fun hx => hx.trans h, fun hx => hx.trans h.symm⟩

/-! ## The classes are blocks of imprimitivity

Closure under the generators is closure under the group, because the relation is a *finite* set
of pairs: a generator maps it into itself injectively, hence onto itself, and the permutations
that do so form a subgroup.  This is the argument of `Algo.image_eq_of_mem_genGroup`
(`Workspace/Algo/Orbits.lean`), run on pairs instead of points. -/

section Group

variable {n : ℕ} {gs : RawGens} {lab : RawLab}

/-- The pairs of points in one class, as a finite set. -/
def labFinset (n : ℕ) (lab : RawLab) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => LabRel lab (p.1 : ℕ) (p.2 : ℕ))

theorem mem_labFinset {p : Fin n × Fin n} :
    p ∈ labFinset n lab ↔ LabRel lab (p.1 : ℕ) (p.2 : ℕ) := by
  simp [labFinset]

/-- The permutations that map a finite set of pairs onto itself. -/
def pairStabilizer {n : ℕ} (T : Finset (Fin n × Fin n)) : Subgroup (Perm (Fin n)) where
  carrier := {σ | T.image (fun p => ((σ p.1, σ p.2) : Fin n × Fin n)) = T}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have h : (fun p : Fin n × Fin n =>
          (((a * b : Perm (Fin n)) p.1, (a * b : Perm (Fin n)) p.2) : Fin n × Fin n))
        = (fun q : Fin n × Fin n => ((a q.1, a q.2) : Fin n × Fin n)) ∘
          (fun p : Fin n × Fin n => ((b p.1, b p.2) : Fin n × Fin n)) := rfl
    rw [h, ← Finset.image_image, hb, ha]
  one_mem' := by
    show Finset.image _ T = T
    have h : (fun p : Fin n × Fin n =>
        (((1 : Perm (Fin n)) p.1, (1 : Perm (Fin n)) p.2) : Fin n × Fin n)) = id := by
      funext p
      simp
    rw [h, Finset.image_id]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [Finset.image_image]
    have h : ((fun q : Fin n × Fin n =>
        (((a⁻¹ : Perm (Fin n)) q.1, (a⁻¹ : Perm (Fin n)) q.2) : Fin n × Fin n)) ∘
        (fun p : Fin n × Fin n => ((a p.1, a p.2) : Fin n × Fin n))) = id := by
      funext p
      simp
    rw [h, Finset.image_id]

theorem mem_pairStabilizer_iff {T : Finset (Fin n × Fin n)} {σ : Perm (Fin n)}
    (hσ : σ ∈ pairStabilizer T) (x y : Fin n) : ((σ x, σ y) ∈ T) ↔ ((x, y) ∈ T) := by
  have hT : T.image (fun p => ((σ p.1, σ p.2) : Fin n × Fin n)) = T := hσ
  constructor
  · intro h
    rw [← hT] at h
    obtain ⟨p, hp, hpq⟩ := Finset.mem_image.1 h
    have h1 : σ p.1 = σ x := congrArg Prod.fst hpq
    have h2 : σ p.2 = σ y := congrArg Prod.snd hpq
    have hpxy : p = (x, y) := Prod.ext (σ.injective h1) (σ.injective h2)
    exact hpxy ▸ hp
  · intro h
    rw [← hT]
    exact Finset.mem_image.2 ⟨(x, y), h, rfl⟩

/-- **The whole group carries a closed labelling along.** -/
theorem labRel_smul_iff (hwf : RawGens.WF n gs) (hclosed : LabClosed n gs lab)
    {σ : Perm (Fin n)} (hσ : σ ∈ decGroup n gs) (x y : Fin n) :
    LabRel lab ((σ x : Fin n) : ℕ) ((σ y : Fin n) : ℕ) ↔ LabRel lab (x : ℕ) (y : ℕ) := by
  classical
  have hle : decGroup n gs ≤ pairStabilizer (labFinset n lab) := by
    rw [decGroup, genGroup]
    refine (Subgroup.closure_le _).2 ?_
    rintro σ' hσ'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 (show σ' ∈ gs.map (decPerm n) from hσ')
    have hinj : Function.Injective (fun p : Fin n × Fin n =>
        ((decPerm n g p.1, decPerm n g p.2) : Fin n × Fin n)) := by
      intro p q hpq
      exact Prod.ext ((decPerm n g).injective (congrArg Prod.fst hpq))
        ((decPerm n g).injective (congrArg Prod.snd hpq))
    show Finset.image _ (labFinset n lab) = labFinset n lab
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
      refine mem_labFinset.2 ?_
      have hgu := hclosed g hg (p.1 : ℕ) p.1.isLt (p.2 : ℕ) p.2.isLt (mem_labFinset.1 hp)
      rwa [rawApply_of_wf (hwf g hg) p.1.isLt, rawApply_of_wf (hwf g hg) p.2.isLt] at hgu
    · rw [Finset.card_image_of_injective _ hinj]
  have h := mem_pairStabilizer_iff (hle hσ) x y
  rw [mem_labFinset, mem_labFinset] at h
  exact h

/-- **The image of a class is a class.** -/
theorem image_labSet (hwf : RawGens.WF n gs) (hclosed : LabClosed n gs lab)
    {σ : Perm (Fin n)} (hσ : σ ∈ decGroup n gs) {u : ℕ} (hu : u < n) :
    σ '' labSet n lab u = labSet n lab ((σ ⟨u, hu⟩ : Fin n) : ℕ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (labRel_smul_iff hwf hclosed hσ x ⟨u, hu⟩).2 hx
  · intro hy
    refine ⟨σ⁻¹ y, ?_, by simp⟩
    refine (labRel_smul_iff hwf hclosed hσ (σ⁻¹ y) ⟨u, hu⟩).1 ?_
    have hyy : (σ (σ⁻¹ y) : Fin n) = y := by simp
    rw [hyy]
    exact hy

/-- From a transitive group, a permutation carrying one point to another. -/
theorem exists_smul_of_isTransitive {G : Subgroup (Perm (Fin n))} (hG : Babai.IsTransitive G)
    (x y : Fin n) : ∃ σ ∈ G, (σ : Perm (Fin n)) x = y := by
  haveI := hG.isPretransitive
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
  exact ⟨(g : Perm (Fin n)), g.2, hg⟩

/-- **The classes of a closed labelling form a system of imprimitivity** (§2.2.1). -/
theorem isSystemOfImprimitivity_labBlocks {dom : List ℕ} (hwf : RawGens.WF n gs)
    (hdom : dom.length = n) (hclosed : LabClosed n gs lab)
    (htr : Babai.IsTransitive (decGroup n gs)) (hn : 0 < n) :
    Babai.IsSystemOfImprimitivity (decGroup n gs) Set.univ
      (blockSets n (labBlocks (dom, lab))) := by
  refine ⟨Babai.isInvariant_univ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro S hS
    obtain ⟨u, hu, rfl⟩ := (mem_blockSets_labBlocks hdom).1 hS
    exact ⟨⟨u, hu⟩, rfl⟩
  · rintro S hS S' hS' hne
    obtain ⟨u, hu, rfl⟩ := (mem_blockSets_labBlocks hdom).1 hS
    obtain ⟨u', hu', rfl⟩ := (mem_blockSets_labBlocks hdom).1 hS'
    refine Set.disjoint_left.2 (fun x hx hx' => hne ?_)
    exact labSet_eq_of_labRel ((mem_labSet.1 hx).symm.trans (mem_labSet.1 hx'))
  · refine Set.eq_univ_of_forall (fun x => ?_)
    refine ⟨labSet n lab (x : ℕ), (mem_blockSets_labBlocks hdom).2 ⟨(x : ℕ), x.isLt, rfl⟩, ?_⟩
    exact mem_labSet.2 rfl
  · intro σ hσ S hS
    obtain ⟨u, hu, rfl⟩ := (mem_blockSets_labBlocks hdom).1 hS
    rw [image_labSet hwf hclosed hσ hu]
    exact (mem_blockSets_labBlocks hdom).2 ⟨_, Fin.isLt _, rfl⟩
  · exact ⟨labSet n lab 0, (mem_blockSets_labBlocks hdom).2 ⟨0, hn, rfl⟩⟩
  · rintro S hS S' hS'
    obtain ⟨u, hu, rfl⟩ := (mem_blockSets_labBlocks hdom).1 hS
    obtain ⟨u', hu', rfl⟩ := (mem_blockSets_labBlocks hdom).1 hS'
    obtain ⟨σ, hσ, hσu⟩ := exists_smul_of_isTransitive htr ⟨u, hu⟩ ⟨u', hu'⟩
    refine ⟨σ, hσ, ?_⟩
    rw [image_labSet hwf hclosed hσ hu, hσu]

end Group

/-! ## Line 4: one pass over the points

Start from the singletons.  For `b = 0, 1, …, n-1`, merge the class of `0` with the class of
`b` and close up; keep the answer if it is still a proper partition, discard it otherwise. -/

/-- **The test that a labelling is a proper partition**: some point is outside the class of
`0`. -/
def labProper (p : List ℕ × RawLab) : Bool :=
  !((List.range p.1.length).filter (fun u => !decide (labAt p.2 u = labAt p.2 0))).isEmpty

theorem labProper_eq_true_iff {dom : List ℕ} {lab : RawLab} :
    labProper (dom, lab) = true ↔ ∃ u < dom.length, ¬ LabRel lab u 0 := by
  simp only [labProper, Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem,
    List.mem_filter, List.mem_range, Bool.not_eq_true', decide_eq_false_iff_not, LabRel]

/-- **One step of line 4.** -/
def minLabStep (p : (RawGens × List ℕ) × (RawLab × ℕ)) : RawLab :=
  if labProper (p.1.2, closeLab (p.1, mergeLab (p.2.1, (0, p.2.2)))) then
    closeLab (p.1, mergeLab (p.2.1, (0, p.2.2)))
  else p.2.1

/-- **Line 4** of Procedure Reduce-to-Johnson (§11.3, line 5048): "Find minimal block
system `ℬ`", as a labelling. -/
def minLab (p : RawGens × List ℕ) : RawLab :=
  (List.range p.2.length).foldl (fun l b => minLabStep (p, (l, b))) (List.range p.2.length)

/-- **Line 4** of Procedure Reduce-to-Johnson (§11.3, line 5048): "Find minimal block
system `ℬ`". -/
def rawMinBlocks (p : RawGens × List ℕ) : RawBlocks := labBlocks (p.2, minLab p)

section Pass

variable {n : ℕ} {gs : RawGens} {dom : List ℕ}

@[simp] theorem length_minLabStep (q : RawGens × List ℕ) (lab : RawLab) (b : ℕ) :
    (minLabStep (q, (lab, b))).length = lab.length := by
  unfold minLabStep
  split
  · rw [length_closeLab, length_mergeLab]
  · rfl

theorem length_foldl_minLabStep (q : RawGens × List ℕ) : ∀ (l : List ℕ) (lab : RawLab),
    (l.foldl (fun x b => minLabStep (q, (x, b))) lab).length = lab.length := by
  intro l
  induction l with
  | nil => intro lab; rfl
  | cons b t ih => intro lab; rw [List.foldl_cons, ih, length_minLabStep]

theorem mem_foldl_minLabStep (q : RawGens × List ℕ) : ∀ (l : List ℕ) (lab : RawLab) {e : ℕ},
    e ∈ l.foldl (fun x b => minLabStep (q, (x, b))) lab → e ∈ lab ∨ e = 0 := by
  intro l
  induction l with
  | nil => intro lab e he; exact Or.inl he
  | cons b t ih =>
      intro lab e he
      rw [List.foldl_cons] at he
      rcases ih _ he with h | h
      · unfold minLabStep at h
        split at h
        · rcases mem_closeLab h with h' | h'
          · exact mem_mergeLab h'
          · exact Or.inr h'
        · exact Or.inl h
      · exact Or.inr h

/-- One step only coarsens. -/
theorem minLabStep_mono {lab : RawLab} {b u v : ℕ} (hu : u < lab.length) (hv : v < lab.length)
    (h : LabRel lab u v) : LabRel (minLabStep ((gs, dom), (lab, b))) u v := by
  unfold minLabStep
  split
  · exact closeLab_mono (by rw [length_mergeLab]; exact hu) (by rw [length_mergeLab]; exact hv)
      (labRel_mergeLab_of_labRel hu hv h)
  · exact h

theorem foldl_minLabStep_mono : ∀ (l : List ℕ) (lab : RawLab) {u v : ℕ},
    u < lab.length → v < lab.length → LabRel lab u v →
      LabRel (l.foldl (fun x b => minLabStep (((gs, dom)), (x, b))) lab) u v := by
  intro l
  induction l with
  | nil => intro lab u v _ _ h; exact h
  | cons b t ih =>
      intro lab u v hu hv h
      rw [List.foldl_cons]
      exact ih _ (by rw [length_minLabStep]; exact hu) (by rw [length_minLabStep]; exact hv)
        (minLabStep_mono hu hv h)

/-- One step keeps a closed labelling closed. -/
theorem minLabStep_closed (hwf : RawGens.WF n gs) (hdom : dom.length = n) {lab : RawLab}
    (hlen : n ≤ lab.length) (hclosed : LabClosed n gs lab) (b : ℕ) :
    LabClosed n gs (minLabStep ((gs, dom), (lab, b))) := by
  unfold minLabStep
  split
  · exact closeLab_closed hwf hdom (by rw [length_mergeLab]; exact hlen)
  · exact hclosed

theorem foldl_minLabStep_closed (hwf : RawGens.WF n gs) (hdom : dom.length = n) :
    ∀ (l : List ℕ) (lab : RawLab), n ≤ lab.length → LabClosed n gs lab →
      LabClosed n gs (l.foldl (fun x b => minLabStep ((gs, dom), (x, b))) lab) := by
  intro l
  induction l with
  | nil => intro lab _ h; exact h
  | cons b t ih =>
      intro lab hlen hclosed
      rw [List.foldl_cons]
      exact ih _ (by rw [length_minLabStep]; exact hlen)
        (minLabStep_closed hwf hdom hlen hclosed b)

/-- One step keeps a proper partition proper. -/
theorem minLabStep_proper {lab : RawLab} (h : labProper (dom, lab) = true) (b : ℕ) :
    labProper (dom, minLabStep ((gs, dom), (lab, b))) = true := by
  unfold minLabStep
  split
  · assumption
  · exact h

theorem foldl_minLabStep_proper : ∀ (l : List ℕ) (lab : RawLab), labProper (dom, lab) = true →
    labProper (dom, l.foldl (fun x b => minLabStep ((gs, dom), (x, b))) lab) = true := by
  intro l
  induction l with
  | nil => intro lab h; exact h
  | cons b t ih =>
      intro lab h
      rw [List.foldl_cons]
      exact ih _ (minLabStep_proper h b)

/-- **The key property of the pass.**  Against a congruence `r` that the *final* labelling
sits inside and that does not relate everything to `0`: every point that `r` relates to `0` is
in the final class of `0`.  The step at such a point cannot have been discarded, because its
candidate sits inside `r` and `r` is proper. -/
theorem foldl_minLabStep_key {r : ℕ → ℕ → Prop} (hr : CongrOn n gs r)
    (hwf : RawGens.WF n gs) (hdom : dom.length = n) {z : ℕ} (hz : z < n) (hzr : ¬ r z 0) :
    ∀ (l : List ℕ) (lab : RawLab), n ≤ lab.length →
      (∀ u < n, ∀ v < n,
        LabRel (l.foldl (fun x b => minLabStep ((gs, dom), (x, b))) lab) u v → r u v) →
      ∀ b ∈ l, b < n → r 0 b →
        LabRel (l.foldl (fun x b => minLabStep ((gs, dom), (x, b))) lab) 0 b := by
  have h0 : 0 < n := by omega
  intro l
  induction l with
  | nil => intro lab _ _ b hb; exact absurd hb (by simp)
  | cons b₀ t ih =>
      intro lab hlen hfin b hb hbn hrb
      rw [List.foldl_cons] at hfin ⊢
      have hlen' : n ≤ (minLabStep ((gs, dom), (lab, b₀))).length := by
        rw [length_minLabStep]; exact hlen
      rcases List.mem_cons.1 hb with rfl | hbt
      · -- the head: the step at `b` was kept
        have hlabr : ∀ u < n, ∀ v < n, LabRel lab u v → r u v := by
          intro u hu v hv h
          exact hfin u hu v hv (foldl_minLabStep_mono t _ (by omega) (by omega)
            (minLabStep_mono (by omega) (by omega) h))
        have hcand : ∀ u < n, ∀ v < n,
            LabRel (closeLab ((gs, dom), mergeLab (lab, (0, b)))) u v → r u v := by
          refine closeLab_least hr hwf hdom (by rw [length_mergeLab]; exact hlen) ?_
          exact mergeLab_least hr.symm hr.trans hlabr hrb h0 hbn hlen
        have hprop : labProper (dom, closeLab ((gs, dom), mergeLab (lab, (0, b)))) = true := by
          refine labProper_eq_true_iff.2 ⟨z, by omega, fun hcon => hzr ?_⟩
          exact hcand z hz 0 h0 hcon
        have hstep : minLabStep ((gs, dom), (lab, b))
            = closeLab ((gs, dom), mergeLab (lab, (0, b))) := by
          show (if labProper (dom, closeLab ((gs, dom), mergeLab (lab, (0, b)))) = true then _
            else lab) = _
          rw [if_pos hprop]
        have hrel : LabRel (minLabStep ((gs, dom), (lab, b))) 0 b := by
          rw [hstep]
          exact closeLab_mono (by rw [length_mergeLab]; omega) (by rw [length_mergeLab]; omega)
            (labRel_mergeLab_pair lab (by omega) (by omega))
        exact foldl_minLabStep_mono t _ (by omega) (by omega) hrel
      · exact ih _ hlen' hfin b hbt hbn hrb

/-! ### The labelling the pass returns -/

@[simp] theorem length_minLab (gs : RawGens) (dom : List ℕ) :
    (minLab (gs, dom)).length = dom.length := by
  rw [minLab, length_foldl_minLabStep, List.length_range]

theorem mem_minLab {gs : RawGens} {dom : List ℕ} {e : ℕ} (he : e ∈ minLab (gs, dom)) :
    e ∈ List.range dom.length ∨ e = 0 := mem_foldl_minLabStep _ _ _ he

theorem labAt_range {n u : ℕ} (hu : u < n) : labAt (List.range n) u = u := by
  rw [labAt, List.getD_eq_getElem _ _ (by simpa using hu), List.getElem_range]

theorem labClosed_range (n : ℕ) (gs : RawGens) : LabClosed n gs (List.range n) := by
  intro g _ u hu v hv h
  have huv : u = v := by
    rw [LabRel, labAt_range hu, labAt_range hv] at h
    exact h
  rw [huv]
  exact rfl

theorem minLab_closed (hwf : RawGens.WF n gs) (hdom : dom.length = n) :
    LabClosed n gs (minLab (gs, dom)) := by
  rw [minLab, hdom]
  exact foldl_minLabStep_closed hwf hdom _ _ (by simp) (labClosed_range n gs)

theorem minLab_proper (hdom : dom.length = n) (hn : 2 ≤ n) :
    labProper (dom, minLab (gs, dom)) = true := by
  rw [minLab, hdom]
  refine foldl_minLabStep_proper _ _ (labProper_eq_true_iff.2 ⟨1, by omega, fun hcon => ?_⟩)
  rw [LabRel, labAt_range (show 1 < n by omega), labAt_range (show 0 < n by omega)] at hcon
  exact absurd hcon (by omega)

theorem minLab_key {r : ℕ → ℕ → Prop} (hr : CongrOn n gs r) (hwf : RawGens.WF n gs)
    (hdom : dom.length = n) {z : ℕ} (hz : z < n) (hzr : ¬ r z 0)
    (hfin : ∀ u < n, ∀ v < n, LabRel (minLab (gs, dom)) u v → r u v) {b : ℕ} (hb : b < n)
    (hrb : r 0 b) : LabRel (minLab (gs, dom)) 0 b := by
  have h := foldl_minLabStep_key hr hwf hdom hz hzr (List.range dom.length) (List.range dom.length)
    (by simp [hdom]) (by rw [← minLab]; exact hfin) b (List.mem_range.2 (by omega)) hb hrb
  rw [← minLab] at h
  exact h

end Pass

/-! ## The translates of a block, as a congruence

For the maximality of the blocks: a block of imprimitivity of a transitive group cuts the
domain into its translates, and that partition is a congruence. -/

section Trans

variable {n : ℕ} {gs : RawGens} {dom : List ℕ}

/-- The partition into the translates of a set, as a relation on the points. -/
def transRel (n : ℕ) (G : Subgroup (Perm (Fin n))) (C : Set (Fin n)) (u v : ℕ) : Prop :=
  ∃ (hu : u < n) (hv : v < n), ∃ σ ∈ G,
    (⟨u, hu⟩ : Fin n) ∈ (σ : Perm (Fin n)) '' C ∧ (⟨v, hv⟩ : Fin n) ∈ (σ : Perm (Fin n)) '' C

theorem congrOn_transRel (hwf : RawGens.WF n gs) {C : Set (Fin n)}
    (hC : Babai.IsBlockOfImprimitivity (decGroup n gs) C) :
    CongrOn n gs (transRel n (decGroup n gs) C) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro u v ⟨hu, hv, σ, hσ, h1, h2⟩
    exact ⟨hv, hu, σ, hσ, h2, h1⟩
  · rintro u v w ⟨hu, hv, σ, hσ, h1, h2⟩ ⟨hv', hw, τ, hτ, h3, h4⟩
    refine ⟨hu, hw, σ, hσ, h1, ?_⟩
    rcases Babai.image_eq_or_disjoint_image hC hσ hτ with heq | hdisj
    · rw [heq]
      exact h4
    · exact absurd (Set.disjoint_left.1 hdisj h2) (by
        have : (⟨v, hv⟩ : Fin n) = ⟨v, hv'⟩ := rfl
        rw [this]
        exact fun hcon => hcon h3)
  · rintro g hg u hu v hv ⟨hu', hv', σ, hσ, h1, h2⟩
    have hgmem : decPerm n g ∈ decGroup n gs := decPerm_mem_decGroup hg
    have hgu : rawApply (g, u) = ((decPerm n g ⟨u, hu⟩ : Fin n) : ℕ) :=
      rawApply_of_wf (hwf g hg) hu
    have hgv : rawApply (g, v) = ((decPerm n g ⟨v, hv⟩ : Fin n) : ℕ) :=
      rawApply_of_wf (hwf g hg) hv
    refine ⟨by rw [hgu]; exact Fin.isLt _, by rw [hgv]; exact Fin.isLt _,
      decPerm n g * σ, mul_mem hgmem hσ, ?_, ?_⟩
    · have : (⟨rawApply (g, u), by rw [hgu]; exact Fin.isLt _⟩ : Fin n)
          = decPerm n g ⟨u, hu'⟩ := Fin.ext hgu
      rw [this]
      obtain ⟨c, hc, hcu⟩ := h1
      exact ⟨c, hc, by rw [← hcu]; rfl⟩
    · have : (⟨rawApply (g, v), by rw [hgv]; exact Fin.isLt _⟩ : Fin n)
          = decPerm n g ⟨v, hv'⟩ := Fin.ext hgv
      rw [this]
      obtain ⟨c, hc, hcv⟩ := h2
      exact ⟨c, hc, by rw [← hcv]; rfl⟩

end Trans

/-! ## Line 4 is a minimal system of imprimitivity -/

section Spec

variable {n : ℕ} {gs : RawGens} {dom : List ℕ}

/-- The final class of the point `0`. -/
theorem zero_mem_labSet_zero {lab : RawLab} (h0 : 0 < n) :
    (⟨0, h0⟩ : Fin n) ∈ labSet n lab 0 := mem_labSet.2 rfl

/-- **The class of `0` is a maximal block**: a block of imprimitivity that contains it and is
not everything equals it. -/
theorem labSet_zero_maximal (hwf : RawGens.WF n gs) (hdom : dom.length = n)
    (htr : Babai.IsTransitive (decGroup n gs)) (hn : 2 ≤ n) {C : Set (Fin n)}
    (hC : Babai.IsBlockOfImprimitivity (decGroup n gs) C)
    (hsub : labSet n (minLab (gs, dom)) 0 ⊆ C) (hCne : C ≠ Set.univ) :
    C = labSet n (minLab (gs, dom)) 0 := by
  have h0 : 0 < n := by omega
  set lab : RawLab := minLab (gs, dom) with hlab
  have hclosed : LabClosed n gs lab := minLab_closed hwf hdom
  have h0C : (⟨0, h0⟩ : Fin n) ∈ C := hsub (zero_mem_labSet_zero h0)
  set r : ℕ → ℕ → Prop := transRel n (decGroup n gs) C with hr
  have hrC : CongrOn n gs r := congrOn_transRel hwf hC
  -- `r` does not relate everything to `0`
  obtain ⟨w, hw⟩ : ∃ w : Fin n, w ∉ C := by
    by_contra hcon
    push_neg at hcon
    exact hCne (Set.eq_univ_of_forall hcon)
  have hzr : ¬ r (w : ℕ) 0 := by
    rintro ⟨hu, hv, σ, hσ, h1, h2⟩
    have h0σ : (⟨0, h0⟩ : Fin n) ∈ (σ : Perm (Fin n)) '' C := by
      have : (⟨(0 : ℕ), hv⟩ : Fin n) = ⟨0, h0⟩ := rfl
      rwa [this] at h2
    have hone : ((1 : Perm (Fin n)) : Fin n → Fin n) '' C = C := by simp
    have hCσ : (σ : Perm (Fin n)) '' C = C := by
      rcases Babai.image_eq_or_disjoint_image hC hσ (one_mem _) with heq | hdisj
      · rw [hone] at heq; exact heq
      · exact absurd (Set.disjoint_left.1 hdisj h0σ) (by
          rw [hone]
          exact fun hcon => hcon h0C)
    have : (w : Fin n) ∈ C := by
      have hwu : (⟨(w : ℕ), hu⟩ : Fin n) = w := Fin.ext rfl
      rw [← hCσ, ← hwu]
      exact h1
    exact hw this
  -- the final labelling sits inside `r`
  have hfin : ∀ u < n, ∀ v < n, LabRel lab u v → r u v := by
    intro u hu v hv huv
    obtain ⟨σ, hσ, hσu⟩ := exists_smul_of_isTransitive htr ⟨0, h0⟩ ⟨u, hu⟩
    have himg : (σ : Perm (Fin n)) '' labSet n lab 0 = labSet n lab u := by
      rw [image_labSet hwf hclosed hσ h0, hσu]
    have hsubσ : labSet n lab u ⊆ (σ : Perm (Fin n)) '' C := by
      rw [← himg]
      exact Set.image_mono hsub
    exact ⟨hu, hv, σ, hσ, hsubσ (mem_labSet.2 rfl), hsubσ (mem_labSet.2 (huv.symm))⟩
  -- every point of `C` is in the class of `0`
  refine Set.Subset.antisymm (fun x hx => ?_) hsub
  refine mem_labSet.2 ?_
  have hone : ((1 : Perm (Fin n)) : Fin n → Fin n) '' C = C := by simp
  have hrx : r 0 (x : ℕ) := by
    refine ⟨h0, x.isLt, 1, one_mem _, ?_, ?_⟩
    · rw [hone]; exact h0C
    · rw [hone]
      have hxx : (⟨(x : ℕ), x.isLt⟩ : Fin n) = x := Fin.ext rfl
      rw [hxx]; exact hx
  exact (minLab_key hrC hwf hdom w.isLt hzr hfin x.isLt hrx).symm

/-- **Line 4 of Procedure Reduce-to-Johnson** (§11.3, line 5048): the routine returns a
*minimal* system of imprimitivity — at least two blocks, and the blocks are maximal (§11.1). -/
theorem isMinimalSystemOfImprimitivity_rawMinBlocks (hwf : RawGens.WF n gs)
    (hdom : dom.length = n) (htr : Babai.IsTransitive (decGroup n gs)) (hn : 2 ≤ n) :
    Babai.IsMinimalSystemOfImprimitivity (decGroup n gs) Set.univ
      (blockSets n (rawMinBlocks (gs, dom))) := by
  have h0 : 0 < n := by omega
  set lab : RawLab := minLab (gs, dom) with hlab
  have hclosed : LabClosed n gs lab := minLab_closed hwf hdom
  have hsys : Babai.IsSystemOfImprimitivity (decGroup n gs) Set.univ
      (blockSets n (labBlocks (dom, lab))) :=
    isSystemOfImprimitivity_labBlocks hwf hdom hclosed htr h0
  obtain ⟨z, hz, hznot⟩ := labProper_eq_true_iff.1 (minLab_proper (gs := gs) hdom hn)
  rw [hdom] at hz
  refine ⟨show Babai.IsSystemOfImprimitivity _ _ (blockSets n (rawMinBlocks (gs, dom))) from
    hsys, ?_, ?_⟩
  · -- at least two blocks: the class of `z` is not the class of `0`
    have hne : labSet n lab z ≠ labSet n lab 0 := by
      intro hcon
      have : (⟨z, hz⟩ : Fin n) ∈ labSet n lab 0 := by rw [← hcon]; exact mem_labSet.2 rfl
      exact hznot (mem_labSet.1 this)
    refine (Set.one_lt_ncard (Set.toFinite _)).2 ⟨labSet n lab z, ?_, labSet n lab 0, ?_, hne⟩
    · exact (mem_blockSets_labBlocks hdom).2 ⟨z, hz, rfl⟩
    · exact (mem_blockSets_labBlocks hdom).2 ⟨0, h0, rfl⟩
  · -- the blocks are maximal
    rintro B hB C - hBC hCblock
    obtain ⟨u, hu, rfl⟩ := (mem_blockSets_labBlocks hdom).1 hB
    by_cases hCuniv : C = Set.univ
    · exact Or.inr hCuniv
    left
    -- translate the class of `u` to the class of `0`
    obtain ⟨σ, hσ, hσu⟩ := exists_smul_of_isTransitive htr ⟨u, hu⟩ ⟨0, h0⟩
    have himg : (σ : Perm (Fin n)) '' labSet n lab u = labSet n lab 0 := by
      rw [image_labSet hwf hclosed hσ hu, hσu]
    have hCblock' : Babai.IsBlockOfImprimitivity (decGroup n gs) ((σ : Perm (Fin n)) '' C) :=
      Babai.isBlockOfImprimitivity_image hCblock hσ
    have hsub' : labSet n lab 0 ⊆ (σ : Perm (Fin n)) '' C := by
      rw [← himg]; exact Set.image_mono hBC
    have hne' : (σ : Perm (Fin n)) '' C ≠ Set.univ := by
      intro hcon
      refine hCuniv (Set.eq_univ_of_forall (fun x => ?_))
      have hx : σ x ∈ (σ : Perm (Fin n)) '' C := by rw [hcon]; trivial
      obtain ⟨c, hc, hcx⟩ := hx
      have : c = x := σ.injective hcx
      exact this ▸ hc
    have heq := labSet_zero_maximal hwf hdom htr hn hCblock' hsub' hne'
    -- undo the translation
    have : (σ : Perm (Fin n)) '' C = (σ : Perm (Fin n)) '' labSet n lab u := by
      rw [heq, himg]
    refine Set.Subset.antisymm (fun x hx => ?_) hBC
    have hσx : σ x ∈ (σ : Perm (Fin n)) '' labSet n lab u := by rw [← this]; exact ⟨x, hx, rfl⟩
    obtain ⟨c, hc, hcx⟩ := hσx
    exact (σ.injective hcx) ▸ hc

/-- The block system the routine returns is well formed (`Algo.BlocksWF`). -/
theorem blocksWF_rawMinBlocks (hdom : dom.length = n) (gs : RawGens) :
    BlocksWF n (rawMinBlocks (gs, dom)) := blocksWF_labBlocks hdom _

/-- **The action on the blocks is primitive** (`Babai.IsPrimitive`), which is what line 4 is
for: lines 5 and 6 speak of the primitive group `Ḡ`. -/
theorem isPrimitive_rawMinBlocks (hwf : RawGens.WF n gs) (hdom : dom.length = n)
    (htr : Babai.IsTransitive (decGroup n gs)) (hn : 2 ≤ n) :
    Babai.IsPrimitive (Babai.onBlocks (decGroup n gs) (blockSets n (rawMinBlocks (gs, dom)))
      (isMinimalSystemOfImprimitivity_rawMinBlocks hwf hdom htr hn).permutes) :=
  Babai.isPrimitive_onBlocks (isMinimalSystemOfImprimitivity_rawMinBlocks hwf hdom htr hn)

/-- **The datum a descent instance carries** (`Algo.BlockData`, `Workspace/Algo/Blocks.lean`):
the images of the generators on the blocks of the computed system are the images of the action
`ψ : G → S(ℬ)`. -/
theorem blockData_rawMinBlocks {gens : List (Perm (Fin n))} (hdom : dom.length = n)
    (htr : Babai.IsTransitive (genGroup gens)) (hn : 2 ≤ n) :
    BlockData n (rawMinBlocks (gens.map (encPerm n), dom)) gens := by
  have hwf : RawGens.WF n (gens.map (encPerm n)) := wf_map_encPerm n gens
  have htr' : Babai.IsTransitive (decGroup n (gens.map (encPerm n))) := by
    rw [decGroup_map_encPerm]; exact htr
  have hmin := isMinimalSystemOfImprimitivity_rawMinBlocks hwf hdom htr' hn
  have hperm : ∀ σ ∈ genGroup gens, ∀ B ∈ blockSets n (rawMinBlocks (gens.map (encPerm n), dom)),
      (σ : Perm (Fin n)) '' B ∈ blockSets n (rawMinBlocks (gens.map (encPerm n), dom)) := by
    intro σ hσ B hB
    exact hmin.permutes σ (by rw [decGroup_map_encPerm] at *; exact hσ) B hB
  exact (blockData_of_permutes (blocksWF_rawMinBlocks hdom _) hperm).1

end Spec

/-! ## The running time

All three loops — the closure loop, the pass over the points, and the duplicate removal that
reads the blocks off — keep an accumulator that is a list of the length of the labelling they
started from, whose entries are entries of that labelling or the default `0`.  That is the size
bound `RAM.PolyFun.foldlParam` asks for. -/

section Poly

/-- The size of a list that is as long as `x` and whose entries come from `x` or are `0`. -/
def labSizeBound (m : ℕ) : ℕ := 1 + m * (2 * (m + Enc.size (0 : ℕ)) + 1)

theorem polyBound_labSizeBound : PolyBound labSizeBound :=
  (polyBound_const 1).add (polyBound_id.mul
    (((polyBound_const 2).mul (polyBound_id.add (polyBound_const (Enc.size (0 : ℕ))))).add
      (polyBound_const 1)))

theorem size_le_labSizeBound {l x : RawLab} (hlen : l.length = x.length)
    (hmem : ∀ e ∈ l, e ∈ x ∨ e = 0) {N : ℕ} (hx : Enc.size x ≤ N) :
    Enc.size l ≤ labSizeBound N := by
  have hxl : x.length ≤ N := le_trans (length_le_size x) hx
  have hentry : ∀ e ∈ l, Enc.size e ≤ N + Enc.size (0 : ℕ) := by
    intro e he
    rcases hmem e he with h | rfl
    · have := size_mem_le h
      omega
    · omega
  have h1 := size_list_le_of_entries l (N + Enc.size (0 : ℕ)) hentry
  have h2 : l.length * (2 * (N + Enc.size (0 : ℕ)) + 1) ≤ N * (2 * (N + Enc.size (0 : ℕ)) + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  show Enc.size l ≤ 1 + N * (2 * (N + Enc.size (0 : ℕ)) + 1)
  omega

theorem polyFun_labAt : PolyFun (fun p : RawLab × ℕ => labAt p.1 p.2) :=
  ((polyFun_id.pair (polyFun_const (0 : ℕ))).comp polyFun_getD).of_eq (fun _ => rfl)

theorem polyFun_mergeLab : PolyFun mergeLab := by
  have hs : PolyFun (fun z : (RawLab × (ℕ × ℕ)) × ℕ => labAt z.1.1 z.1.2.1) :=
    ((polyFun_fst.comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)).comp polyFun_labAt
  have ht : PolyFun (fun z : (RawLab × (ℕ × ℕ)) × ℕ => labAt z.1.1 z.1.2.2) :=
    ((polyFun_fst.comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_snd).comp polyFun_snd)).comp polyFun_labAt
  have hcond : PolyFun (fun z : (RawLab × (ℕ × ℕ)) × ℕ =>
      decide (z.2 = labAt z.1.1 z.1.2.2)) := (polyFun_snd.pair ht).comp polyFun_natEq
  have hpar : PolyFun (fun z : (RawLab × (ℕ × ℕ)) × ℕ =>
      if z.2 = labAt z.1.1 z.1.2.2 then labAt z.1.1 z.1.2.1 else z.2) :=
    (PolyFun.ite hcond hs polyFun_snd).of_eq
      (fun z => by by_cases h : z.2 = labAt z.1.1 z.1.2.2 <;> simp [h])
  exact ((polyFun_id.pair polyFun_fst).comp (PolyFun.mapParam hpar)).of_eq (fun _ => rfl)

theorem polyFun_mergeJob : PolyFun mergeJob := by
  have h1 : PolyFun (fun p : RawLab × (RawPerm × (ℕ × ℕ)) => labAt p.1 p.2.2.1) :=
    (polyFun_fst.pair ((polyFun_snd.comp polyFun_snd).comp polyFun_fst)).comp polyFun_labAt
  have h2 : PolyFun (fun p : RawLab × (RawPerm × (ℕ × ℕ)) => labAt p.1 p.2.2.2) :=
    (polyFun_fst.pair ((polyFun_snd.comp polyFun_snd).comp polyFun_snd)).comp polyFun_labAt
  have hcond : PolyFun (fun p : RawLab × (RawPerm × (ℕ × ℕ)) =>
      decide (labAt p.1 p.2.2.1 = labAt p.1 p.2.2.2)) := (h1.pair h2).comp polyFun_natEq
  have hgu : PolyFun (fun p : RawLab × (RawPerm × (ℕ × ℕ)) => rawApply (p.2.1, p.2.2.1)) :=
    ((polyFun_snd.comp polyFun_fst).pair
      ((polyFun_snd.comp polyFun_snd).comp polyFun_fst)).comp polyFun_rawApply
  have hgv : PolyFun (fun p : RawLab × (RawPerm × (ℕ × ℕ)) => rawApply (p.2.1, p.2.2.2)) :=
    ((polyFun_snd.comp polyFun_fst).pair
      ((polyFun_snd.comp polyFun_snd).comp polyFun_snd)).comp polyFun_rawApply
  have hthen : PolyFun (fun p : RawLab × (RawPerm × (ℕ × ℕ)) =>
      mergeLab (p.1, (rawApply (p.2.1, p.2.2.1), rawApply (p.2.1, p.2.2.2)))) :=
    (polyFun_fst.pair (hgu.pair hgv)).comp polyFun_mergeLab
  exact (PolyFun.ite hcond hthen polyFun_fst).of_eq (fun p => by
    unfold mergeJob
    by_cases h : labAt p.1 p.2.2.1 = labAt p.1 p.2.2.2 <;> simp [h])

theorem polyFun_labPairsList : PolyFun labPairsList := by
  have hinner : PolyFun (fun z : (List ℕ × ℕ) × ℕ => ((z.1.2, z.2) : ℕ × ℕ)) :=
    (polyFun_fst.comp polyFun_snd).pair polyFun_snd
  have hrow : PolyFun (fun z : List ℕ × ℕ => z.1.map (fun v => (z.2, v))) :=
    ((polyFun_id.pair polyFun_fst).comp (PolyFun.mapParam hinner)).of_eq (fun _ => rfl)
  have hall : PolyFun (fun p : List ℕ × List ℕ =>
      (p.2.map (fun u => p.1.map (fun v => (u, v)))).flatten) := PolyFun.flatMapParam hrow
  exact ((polyFun_rangeLength.pair polyFun_rangeLength).comp hall).of_eq (fun _ => rfl)

theorem polyFun_labJobs : PolyFun labJobs := by
  have hinner : PolyFun (fun z : (List (ℕ × ℕ) × RawPerm) × (ℕ × ℕ) =>
      ((z.1.2, z.2) : RawPerm × (ℕ × ℕ))) := (polyFun_fst.comp polyFun_snd).pair polyFun_snd
  have hrow : PolyFun (fun z : List (ℕ × ℕ) × RawPerm => z.1.map (fun q => (z.2, q))) :=
    ((polyFun_id.pair polyFun_fst).comp (PolyFun.mapParam hinner)).of_eq (fun _ => rfl)
  have hall : PolyFun (fun p : List (ℕ × ℕ) × RawGens =>
      (p.2.map (fun g => p.1.map (fun q => (g, q)))).flatten) := PolyFun.flatMapParam hrow
  exact (((polyFun_snd.comp polyFun_labPairsList).pair polyFun_fst).comp hall).of_eq
    (fun _ => rfl)

theorem polyFun_labRounds : PolyFun labRounds := by
  have hinner : PolyFun (fun z : List ℕ × ℕ => z.2 :: z.1) :=
    (polyFun_snd.pair polyFun_fst).comp polyFun_cons
  have hall : PolyFun (fun p : List ℕ × List ℕ => (p.2.map (fun u => u :: p.1)).flatten) :=
    PolyFun.flatMapParam hinner
  exact ((polyFun_rangeLength.pair polyFun_rangeLength).comp hall).of_eq (fun _ => rfl)

theorem polyFun_labStep : PolyFun labStep := by
  have hf : PolyFun (fun z : (RawGens × List ℕ) × (RawLab × (RawPerm × (ℕ × ℕ))) =>
      mergeJob z.2) := polyFun_snd.comp polyFun_mergeJob
  have hacc : ∀ (cc : RawGens × List ℕ) (x : RawLab) (r : List (RawPerm × (ℕ × ℕ))) (j : ℕ),
      Enc.size (List.foldl (fun y a => mergeJob (y, a)) x (r.take j))
        ≤ labSizeBound (Enc.size ((cc, (x, r)) :
            (RawGens × List ℕ) × (RawLab × List (RawPerm × (ℕ × ℕ))))) := by
    intro cc x r j
    set N := Enc.size ((cc, (x, r)) :
      (RawGens × List ℕ) × (RawLab × List (RawPerm × (ℕ × ℕ)))) with hN
    have hxr : Enc.size ((x, r) : RawLab × List (RawPerm × (ℕ × ℕ))) ≤ N :=
      Combine.size_snd_le cc ((x, r) : RawLab × List (RawPerm × (ℕ × ℕ)))
    have hx : Enc.size x ≤ N := le_trans (Combine.size_fst_le x r) hxr
    exact size_le_labSizeBound (length_foldl_mergeJob _ _)
      (fun e he => mem_foldl_mergeJob _ _ he) hx
  have hfold := PolyFun.foldlParam hf polyBound_labSizeBound hacc
  have hin : PolyFun (fun p : (RawGens × List ℕ) × RawLab =>
      ((p.1, (p.2, labJobs p.1)) :
        (RawGens × List ℕ) × (RawLab × List (RawPerm × (ℕ × ℕ))))) :=
    polyFun_fst.pair (polyFun_snd.pair (polyFun_fst.comp polyFun_labJobs))
  exact (hin.comp hfold).of_eq (fun _ => rfl)

theorem polyFun_closeLab : PolyFun closeLab := by
  have hf : PolyFun (fun z : (RawGens × List ℕ) × (RawLab × ℕ) => labStep (z.1, z.2.1)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_labStep
  have hacc : ∀ (cc : RawGens × List ℕ) (x : RawLab) (r : List ℕ) (j : ℕ),
      Enc.size (List.foldl (fun y (a : ℕ) => (fun z : (RawGens × List ℕ) × (RawLab × ℕ) =>
            labStep (z.1, z.2.1)) (cc, (y, a))) x (r.take j))
        ≤ labSizeBound (Enc.size ((cc, (x, r)) :
            (RawGens × List ℕ) × (RawLab × List ℕ))) := by
    intro cc x r j
    set N := Enc.size ((cc, (x, r)) : (RawGens × List ℕ) × (RawLab × List ℕ)) with hN
    have hxr : Enc.size ((x, r) : RawLab × List ℕ) ≤ N :=
      Combine.size_snd_le cc ((x, r) : RawLab × List ℕ)
    have hx : Enc.size x ≤ N := le_trans (Combine.size_fst_le x r) hxr
    show Enc.size (List.foldl (fun y (_ : ℕ) => labStep (cc, y)) x (r.take j)) ≤ _
    rw [foldl_const_eq_iterate]
    exact size_le_labSizeBound (length_labIterate cc x _)
      (fun e he => mem_labIterate cc _ x he) hx
  have hfold := PolyFun.foldlParam hf polyBound_labSizeBound hacc
  have hin : PolyFun (fun p : (RawGens × List ℕ) × RawLab =>
      ((p.1, (p.2, labRounds p.1.2)) : (RawGens × List ℕ) × (RawLab × List ℕ))) :=
    polyFun_fst.pair (polyFun_snd.pair ((polyFun_fst.comp polyFun_snd).comp polyFun_labRounds))
  exact (hin.comp hfold).of_eq (fun _ => rfl)

theorem polyFun_labProper : PolyFun labProper := by
  have hlab0 : PolyFun (fun z : (List ℕ × RawLab) × ℕ => labAt z.1.2 0) :=
    ((polyFun_fst.comp polyFun_snd).pair (polyFun_const (0 : ℕ))).comp polyFun_labAt
  have hlabu : PolyFun (fun z : (List ℕ × RawLab) × ℕ => labAt z.1.2 z.2) :=
    ((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp polyFun_labAt
  have hpred : PolyFun (fun z : (List ℕ × RawLab) × ℕ =>
      !decide (labAt z.1.2 z.2 = labAt z.1.2 0)) := by
    refine (PolyFun.ite ((hlabu.pair hlab0).comp polyFun_natEq) (polyFun_const false)
      (polyFun_const true)).of_eq (fun z => ?_)
    by_cases h : labAt z.1.2 z.2 = labAt z.1.2 0 <;> simp [h]
  have hfil : PolyFun (fun p : List ℕ × RawLab =>
      (List.range p.1.length).filter (fun u => !decide (labAt p.2 u = labAt p.2 0))) := by
    have hin : PolyFun (fun p : List ℕ × RawLab =>
        ((p, List.range p.1.length) : (List ℕ × RawLab) × List ℕ)) :=
      polyFun_id.pair (polyFun_fst.comp polyFun_rangeLength)
    exact (hin.comp (PolyFun.filterParam hpred)).of_eq (fun _ => rfl)
  refine (PolyFun.ite (hfil.comp polyFun_isEmpty) (polyFun_const false)
    (polyFun_const true)).of_eq (fun p => ?_)
  show _ = !(((List.range p.1.length).filter
    (fun u => !decide (labAt p.2 u = labAt p.2 0))).isEmpty)
  by_cases h : ((List.range p.1.length).filter
      (fun u => !decide (labAt p.2 u = labAt p.2 0))).isEmpty = true <;> simp [h]

theorem polyFun_minLabStep : PolyFun minLabStep := by
  have hcand : PolyFun (fun p : (RawGens × List ℕ) × (RawLab × ℕ) =>
      closeLab (p.1, mergeLab (p.2.1, (0, p.2.2)))) := by
    have hm : PolyFun (fun p : (RawGens × List ℕ) × (RawLab × ℕ) =>
        mergeLab (p.2.1, (0, p.2.2))) :=
      ((polyFun_snd.comp polyFun_fst).pair
        ((polyFun_const (0 : ℕ)).pair (polyFun_snd.comp polyFun_snd))).comp polyFun_mergeLab
    exact (polyFun_fst.pair hm).comp polyFun_closeLab
  have hcond : PolyFun (fun p : (RawGens × List ℕ) × (RawLab × ℕ) =>
      labProper (p.1.2, closeLab (p.1, mergeLab (p.2.1, (0, p.2.2))))) :=
    (((polyFun_fst.comp polyFun_snd).pair hcand)).comp polyFun_labProper
  exact (PolyFun.ite hcond hcand (polyFun_snd.comp polyFun_fst)).of_eq (fun p => by
    unfold minLabStep
    by_cases h : labProper (p.1.2, closeLab (p.1, mergeLab (p.2.1, (0, p.2.2)))) = true <;>
      simp [h])

theorem polyFun_minLab : PolyFun minLab := by
  have hacc : ∀ (cc : RawGens × List ℕ) (x : RawLab) (r : List ℕ) (j : ℕ),
      Enc.size (List.foldl (fun y a => minLabStep (cc, (y, a))) x (r.take j))
        ≤ labSizeBound (Enc.size ((cc, (x, r)) : (RawGens × List ℕ) × (RawLab × List ℕ))) := by
    intro cc x r j
    set N := Enc.size ((cc, (x, r)) : (RawGens × List ℕ) × (RawLab × List ℕ)) with hN
    have hxr : Enc.size ((x, r) : RawLab × List ℕ) ≤ N :=
      Combine.size_snd_le cc ((x, r) : RawLab × List ℕ)
    have hx : Enc.size x ≤ N := le_trans (Combine.size_fst_le x r) hxr
    exact size_le_labSizeBound (length_foldl_minLabStep cc _ x)
      (fun e he => mem_foldl_minLabStep cc _ x he) hx
  have hfold := PolyFun.foldlParam polyFun_minLabStep polyBound_labSizeBound hacc
  have hin : PolyFun (fun p : RawGens × List ℕ =>
      ((p, (List.range p.2.length, List.range p.2.length)) :
        (RawGens × List ℕ) × (RawLab × List ℕ))) :=
    polyFun_id.pair ((polyFun_snd.comp polyFun_rangeLength).pair
      (polyFun_snd.comp polyFun_rangeLength))
  exact (hin.comp hfold).of_eq (fun _ => rfl)

theorem polyFun_labBlocks : PolyFun labBlocks := by
  have hlabels : PolyFun (fun p : List ℕ × RawLab =>
      (List.range p.1.length).map (fun u => labAt p.2 u)) := by
    have hinner : PolyFun (fun z : (List ℕ × RawLab) × ℕ => labAt z.1.2 z.2) :=
      ((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp polyFun_labAt
    have hin : PolyFun (fun p : List ℕ × RawLab =>
        ((p, List.range p.1.length) : (List ℕ × RawLab) × List ℕ)) :=
      polyFun_id.pair (polyFun_fst.comp polyFun_rangeLength)
    exact (hin.comp (PolyFun.mapParam hinner)).of_eq (fun _ => rfl)
  have hdedup : PolyFun (fun p : List ℕ × RawLab =>
      dedupG (([] : List ℕ), (List.range p.1.length).map (fun u => labAt p.2 u))) :=
    ((polyFun_const ([] : List ℕ)).pair hlabels).comp (polyFun_dedupG polyFun_natEq)
  have hblock : PolyFun (fun z : (List ℕ × RawLab) × ℕ =>
      (List.range z.1.1.length).filter (fun v => decide (labAt z.1.2 v = z.2))) := by
    have hf1 : PolyFun (fun w : ((List ℕ × RawLab) × ℕ) × ℕ => labAt w.1.1.2 w.2) :=
      (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).pair polyFun_snd).comp polyFun_labAt
    have hf2 : PolyFun (fun w : ((List ℕ × RawLab) × ℕ) × ℕ => w.1.2) :=
      polyFun_fst.comp polyFun_snd
    have hpred : PolyFun (fun w : ((List ℕ × RawLab) × ℕ) × ℕ =>
        decide (labAt w.1.1.2 w.2 = w.1.2)) := (hf1.pair hf2).comp polyFun_natEq
    have hin : PolyFun (fun z : (List ℕ × RawLab) × ℕ =>
        ((z, List.range z.1.1.length) : ((List ℕ × RawLab) × ℕ) × List ℕ)) :=
      polyFun_id.pair ((polyFun_fst.comp polyFun_fst).comp polyFun_rangeLength)
    exact (hin.comp (PolyFun.filterParam hpred)).of_eq (fun _ => rfl)
  exact ((polyFun_id.pair hdedup).comp (PolyFun.mapParam hblock)).of_eq (fun _ => rfl)

/-- **Line 4 runs in polynomial time.** -/
theorem polyFun_rawMinBlocks : PolyFun rawMinBlocks :=
  ((polyFun_snd.pair polyFun_minLab).comp polyFun_labBlocks).of_eq (fun _ => rfl)

end Poly

end Algo
