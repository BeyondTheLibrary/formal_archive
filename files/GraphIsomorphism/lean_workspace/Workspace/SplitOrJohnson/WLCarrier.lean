import Workspace.SplitOrJohnson.WLInitial
import Workspace.Higher.PrelimExtra

/-!
# Restricting WL to the actual vertices

The initial coloring has fixed padding outside the vertex set. We show that removing
this padding preserves the classes at every round. The invariant is that equal
colors on vertex pairs give equal colors from their first endpoints to each padded
point. The converse axiom gives the same fact for the other directions.
-/

namespace Babai.WL

variable {V C : Type*} [Finite V] {p : V → Prop}

/-- Padding colors depend only on the color of a pair of actual vertices. -/
def carrierPad (c : V → V → C) : Prop :=
  ∀ a b x y : {v // p v}, c a b = c x y → ∀ w, ¬ p w → c a w = c x w

theorem carrierPad_right {c : V → V → C} (hc : IsConfigColoring c)
    (hp : carrierPad (p := p) c) {a b x y : {v // p v}} (he : c a b = c x y)
    {w : V} (hw : ¬ p w) : c w b = c w y :=
  hc.2 _ _ _ _ (hp b a y x (hc.2 _ _ _ _ he) w hw)

/-- Split a count into actual vertices and padded points. -/
theorem carrier_count_split (q : V → Prop) :
    {w | q w}.ncard = {w : {v // p v} | q w}.ncard + {w | ¬ p w ∧ q w}.ncard := by
  classical
  have he : Subtype.val '' {w : {v // p v} | q w} = {w | p w ∧ q w} := by
    ext w
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨v.property, hv⟩
    · rintro ⟨hp, hq⟩; exact ⟨⟨w, hp⟩, hq, rfl⟩
  have hu : {w | q w} = {w | p w ∧ q w} ∪ {w | ¬ p w ∧ q w} := by
    ext w; simp only [Set.mem_setOf_eq, Set.mem_union]; tauto
  rw [hu, Set.ncard_union_eq]
  · rw [← he, Set.ncard_image_of_injective _ Subtype.val_injective]
  · exact Set.disjoint_left.2 fun w h₁ h₂ => h₂.1 h₁.1

/-- One round commutes with restriction at the level of color classes. -/
theorem carrier_step_eq_iff {c : V → V → C} (hc : IsConfigColoring c)
    (hp : carrierPad (p := p) c) (a b x y : {v // p v}) :
    step c a b = step c x y ↔
      step (fun u v : {w // p w} => c u v) a b =
        step (fun u v : {w // p w} => c u v) x y := by
  rw [step_eq_iff, step_eq_iff]
  have hcnt (he : c a b = c x y) (i j : C) :
      {w | c a w = i ∧ c w b = j}.ncard = {w | c x w = i ∧ c w y = j}.ncard ↔
      {w : {v // p v} | c a w = i ∧ c w b = j}.ncard =
        {w : {v // p v} | c x w = i ∧ c w y = j}.ncard := by
    rw [carrier_count_split (p := p) (fun w => c a w = i ∧ c w b = j),
      carrier_count_split (p := p) (fun w => c x w = i ∧ c w y = j)]
    have hz : {w | ¬ p w ∧ (c a w = i ∧ c w b = j)} =
        {w | ¬ p w ∧ (c x w = i ∧ c w y = j)} := by
      ext w
      by_cases hw : p w
      · simp [hw]
      · simp only [Set.mem_setOf_eq, hp a b x y he w hw, carrierPad_right hc hp he hw]
    rw [hz, Nat.add_right_cancel_iff]
  exact ⟨fun h => ⟨h.1, fun i j => (hcnt h.1 i j).1 (h.2 i j)⟩,
    fun h => ⟨h.1, fun i j => (hcnt h.1 i j).2 (h.2 i j)⟩⟩

/-- The count data of a pair determines its first endpoint's row counts. -/
theorem carrier_row_counts {c : V → V → C} {a b x y : V}
    (he : step c a b = step c x y) (i : C) :
    {w | c a w = i}.ncard = {w | c x w = i}.ncard := by
  have hh := (step_eq_iff c a b x y).1 he
  have h := ncard_fiber_comp_congr (fun w => (c a w, c w b))
    (fun w => (c x w, c w y)) Prod.fst
    (fun t => by rcases t with ⟨i, j⟩; simpa only [Prod.mk.injEq] using hh.2 i j) i
  exact h

/-- The padding invariant is preserved by a round. -/
theorem carrierPad_step {c : V → V → C} (hc : IsConfigColoring c)
    (hp : carrierPad (p := p) c) : carrierPad (p := p) (step c) := by
  classical
  intro a b x y he w hw
  have hold := congrArg Prod.fst he
  have hr := carrier_step_eq_iff hc hp a b x y |>.1 he
  refine (step_eq_iff c a w x w).2 ⟨hp a b x y hold w hw, fun i j => ?_⟩
  rw [carrier_count_split (p := p) (fun z => c a z = i ∧ c z w = j),
    carrier_count_split (p := p) (fun z => c x z = i ∧ c z w = j)]
  apply congrArg₂ (· + ·)
  · letI : Nonempty (C × C) := ⟨(c a b, c a b)⟩
    have hf : Function.FactorsThrough
        (fun q : {v // p v} × {v // p v} => (c q.1 q.2, c q.2 w))
        (fun q => c q.1 q.2) := by
      intro q q' hq
      exact Prod.ext hq (hp q.2 q.1 q'.2 q'.1 (hc.2 _ _ _ _ hq) w hw)
    obtain ⟨F, hF⟩ := (Function.factorsThrough_iff _).1 hf
    have hF' (u v : {z // p z}) : F (c u v) = (c u v, c v w) :=
      (congrFun hF (u, v)).symm
    have h := ncard_fiber_comp_congr (fun z : {v // p v} => c a z)
      (fun z : {v // p v} => c x z) F (carrier_row_counts hr) (i, j)
    simpa only [hF', Prod.mk.injEq] using h
  · congr 1
    ext z
    by_cases hz : p z
    · simp [hz]
    · simp only [Set.mem_setOf_eq, hp a b x y hold z hz]

/-- Removing padding preserves the color classes round by round. -/
theorem carrier_iter_eq_iff {c : V → V → C} (hc : IsConfigColoring c)
    (hp : carrierPad (p := p) c) (r : ℕ) (a b x y : {v // p v}) :
    iter c r a b = iter c r x y ↔
      iter (fun u v : {w // p w} => c u v) r a b =
        iter (fun u v : {w // p w} => c u v) r x y := by
  have hpad : ∀ n, carrierPad (p := p) (iter c n) := by
    intro n
    induction n with
    | zero => exact hp
    | succ n ih => exact carrierPad_step (isConfigColoring_iter hc n) ih
  induction r generalizing a b x y with
  | zero => rfl
  | succ r ih =>
    exact (carrier_step_eq_iff (isConfigColoring_iter hc r) (hpad r) a b x y).trans
      (step_congr ih a b x y)

end Babai.WL

namespace Babai.VColBipBlk

variable {S : Type}

/-- Section 9.4, step 3: the actual vertices, with points represented by singletons. -/
def Vtx (G : VColBipBlk S ℕ) := {A : Set S // IsVertexOn G.part₁ G.blocks A}

instance (G : VColBipBlk S ℕ) [Finite S] : Finite (Vtx G) :=
  inferInstanceAs (Finite {A : Set S // IsVertexOn G.part₁ G.blocks A})

/-- The initial coloring read only on the actual vertices. -/
noncomputable def vtxInitColor (G : VColBipBlk S ℕ) (A B : Vtx G) : ℕ :=
  initColor G A.val B.val

theorem carrier_initEdge_left (G : VColBipBlk S ℕ) {W : Set S}
    (hw : ¬ IsVertexOn G.part₁ G.blocks W) (A : Set S) : initEdge G W A = 0 := by
  classical
  rw [initEdge, if_neg]
  rintro ⟨x, hx, he, _⟩
  exact hw (Or.inl ⟨x, hx, he⟩)

theorem carrier_initEdge_right (G : VColBipBlk S ℕ) {W : Set S}
    (hw : ¬ IsVertexOn G.part₁ G.blocks W) (A : Set S) : initEdge G A W = 0 := by
  classical
  rw [initEdge, if_neg]
  rintro ⟨x, _, _, he⟩
  exact hw (Or.inr (G.E_sub _ he).2)

/-- A vertex and a padded point have the same fixed initial color for every vertex. -/
theorem carrier_initColor_off (G : VColBipBlk S ℕ) (A : Vtx G) {W : Set S}
    (hw : ¬ IsVertexOn G.part₁ G.blocks W) : initColor G A.val W = 2 := by
  classical
  have hne : A.val ≠ W := fun he => hw (he ▸ A.property)
  have hblock : W ∉ G.blocks := fun h => hw (Or.inr h)
  rw [initColor, if_neg hne, carrier_initEdge_left G hw,
    carrier_initEdge_right G hw, G.h_off _ _ (Or.inr hblock),
    G.h_off _ _ (Or.inl hblock)]
  decide

theorem carrier_initPad (G : VColBipBlk S ℕ) :
    WL.carrierPad (p := IsVertexOn G.part₁ G.blocks) (initColor G) := by
  intro a b x y _ w hw
  exact (carrier_initColor_off G a hw).trans (carrier_initColor_off G x hw).symm

/-- Section 9.4, step 3: removing the padded points preserves the classes at every round. -/
theorem carrier_iter (G : VColBipBlk S ℕ) [Finite S] (r : ℕ) (A B C D : Vtx G) :
    WL.iter (initColor G) r A.val B.val = WL.iter (initColor G) r C.val D.val ↔
      WL.iter (vtxInitColor G) r A B = WL.iter (vtxInitColor G) r C D :=
  WL.carrier_iter_eq_iff (isConfigColoring_initColor G) (carrier_initPad G) r A B C D

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}

/-- The restriction of the existing stable coloring has exactly the vertex refinement's classes. -/
theorem carrier_wlRaw (G : VColBipBlk ↥s ℕ) (A B C D : Vtx G) :
    wlRaw G A.val B.val = wlRaw G C.val D.val ↔
      WL.iter (vtxInitColor G) (wlRounds Ω) A B =
        WL.iter (vtxInitColor G) (wlRounds Ω) C D :=
  carrier_iter G (wlRounds Ω) A B C D

end Babai.VColBipBlk
