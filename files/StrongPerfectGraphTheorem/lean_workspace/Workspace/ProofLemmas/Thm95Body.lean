import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.Types.Knots
import Workspace.Types.BasicClasses
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.StriationCompl
import Workspace.ProofLemmas.KnotFromTwist
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.Thm95OneEndExtension
import Workspace.ProofLemmas.Thm95Claim3Propagate
import Workspace.ProofLemmas.Thm95ClosingPropagate
import Workspace.ProofLemmas.Thm95Offspring
import Workspace.Statements.S09.Thm_9_1
import Workspace.Statements.S09.Thm_9_3

/-!
# The body of 9.5 — its claims (1), (2), (3) and the closing paragraph
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm95Body

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.Types.BasicClasses Workspace.Types.BasicClasses.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Infrastructure: a twist of the striation carries a knot

The printed proof of 9.5 says, in claims (1), (2), (3) and in the closing paragraph, things like
*"we can choose some `Sᵢ, Sᵢ'` to make a twist, and if we choose an `Sᵢ`-rung and `Sᵢ'`-rung and
apply 9.3 to the resultant knot"*.  That the resulting quadruple really **is** a knot is never
argued; it is exactly the content of the definitions of *parallel*, *co-parallel* and *twist*.
The lemmas below carry out that unargued verification once.
-/

/-- Every vertex of an `S`-rung is an end or lies in the middle set `C`. -/
private theorem srung_tri {G : SimpleGraph V} {A C B : Set V} {p : List V}
    (h : IsSRung G (A, C, B) p) :
    ∃ a b : V, a ∈ A ∧ b ∈ B ∧ IsPathFrom G p a b ∧
      ∀ v ∈ p, v = a ∨ v = b ∨ v ∈ C := by
  obtain ⟨a, b, hpath, haA, hbB, -, -, hint⟩ := h
  refine ⟨a, b, haA, hbB, hpath, ?_⟩
  intro v hv
  by_cases hva : v = a
  · exact Or.inl hva
  · by_cases hvb : v = b
    · exact Or.inr (Or.inl hvb)
    · exact Or.inr (Or.inr (hint v
        ((PathBasics.mem_interior_iff_of_pathFrom hpath).mpr ⟨hv, hva, hvb⟩)))

/-- Consequently every vertex of a rung lies in `V(S)`. -/
private theorem mem_sv {A C B : Set V} {a b : V} {p : List V}
    (haA : a ∈ A) (hbB : b ∈ B) (htri : ∀ v ∈ p, v = a ∨ v = b ∨ v ∈ C)
    {v : V} (hv : v ∈ p) : v ∈ stripVertices ((A, C, B) : Set V × Set V × Set V) := by
  show v ∈ A ∪ B ∪ C
  rcases htri v hv with rfl | rfl | hc
  · exact Set.mem_union_left _ (Set.mem_union_left _ haA)
  · exact Set.mem_union_left _ (Set.mem_union_right _ hbB)
  · exact Set.mem_union_right _ hc

/-- **The adjacency pattern between a rung and an antirung of a parallel pair.**

If the strip `S = (A,C,B)` and the antistrip `T = (X,Z,Y)` are parallel, then for any `S`-rung
`a-P-b` and any `T`-antirung `x-Q-y` the only edges between `V(P)` and `{x,y}` are `ax` and `by`,
and the only nonedges between `V(Q)` and `{a,b}` are `ay` and `bx`.  These are precisely the
third and fourth bullets in the definition of a knot. -/
private theorem edge_pattern {G : SimpleGraph V} {A C B X Z Y : Set V} {a b x y : V}
    (haA : a ∈ A) (hbB : b ∈ B) (hxX : x ∈ X) (hyY : y ∈ Y)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hpar : ParallelStripAntistrip G (A, C, B) (X, Z, Y))
    {P Q : List V}
    (htP : ∀ v ∈ P, v = a ∨ v = b ∨ v ∈ C)
    (htQ : ∀ v ∈ Q, v = x ∨ v = y ∨ v ∈ Z) :
    (∀ u ∈ P, ∀ w ∈ ({x, y} : Set V),
      (G.Adj u w ↔ ((u = a ∧ w = x) ∨ (u = b ∧ w = y)))) ∧
    (∀ u ∈ Q, ∀ w ∈ ({a, b} : Set V),
      (¬ G.Adj u w ↔ ((w = a ∧ u = y) ∨ (w = b ∧ u = x)))) := by
  obtain ⟨⟨hAX, hBY⟩, hXBC, hYAC⟩ := hpar
  have hab : a ≠ b := fun h => (Set.disjoint_left.mp hAB haA) (h ▸ hbB)
  have hxy : x ≠ y := fun h => (Set.disjoint_left.mp hXY hxX) (h ▸ hyY)
  have hba : b ≠ a := hab.symm
  have hyx : y ≠ x := hxy.symm
  have hca : ∀ c ∈ C, c ≠ a := fun c hc h => Set.disjoint_left.mp hAC haA (h ▸ hc)
  have hac : ∀ c ∈ C, a ≠ c := fun c hc h => Set.disjoint_left.mp hAC haA (h.symm ▸ hc)
  have hcb : ∀ c ∈ C, c ≠ b := fun c hc h => Set.disjoint_left.mp hBC hbB (h ▸ hc)
  have hbc : ∀ c ∈ C, b ≠ c := fun c hc h => Set.disjoint_left.mp hBC hbB (h.symm ▸ hc)
  have hzx : ∀ z ∈ Z, z ≠ x := fun z hz h => Set.disjoint_left.mp hXZ hxX (h ▸ hz)
  have hxz : ∀ z ∈ Z, x ≠ z := fun z hz h => Set.disjoint_left.mp hXZ hxX (h.symm ▸ hz)
  have hzy : ∀ z ∈ Z, z ≠ y := fun z hz h => Set.disjoint_left.mp hYZ hyY (h ▸ hz)
  have hyz : ∀ z ∈ Z, y ≠ z := fun z hz h => Set.disjoint_left.mp hYZ hyY (h.symm ▸ hz)
  have hax : G.Adj a x := hAX a haA x (Or.inl hxX)
  have hby : G.Adj b y := hBY b hbB y (Or.inl hyY)
  have haz : ∀ z ∈ Z, G.Adj a z := fun z hz => hAX a haA z (Or.inr hz)
  have hbz : ∀ z ∈ Z, G.Adj b z := fun z hz => hBY b hbB z (Or.inr hz)
  have hxb : ¬ G.Adj x b := hXBC x hxX b (Or.inl hbB)
  have hxc : ∀ c ∈ C, ¬ G.Adj x c := fun c hc => hXBC x hxX c (Or.inr hc)
  have hya : ¬ G.Adj y a := hYAC y hyY a (Or.inl haA)
  have hyc : ∀ c ∈ C, ¬ G.Adj y c := fun c hc => hYAC y hyY c (Or.inr hc)
  constructor
  · intro u hu w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases htP u hu with rfl | rfl | hc
    · rcases hw with rfl | rfl
      · exact iff_of_true hax (Or.inl ⟨rfl, rfl⟩)
      · exact iff_of_false (fun h => hya h.symm) (by tauto)
    · rcases hw with rfl | rfl
      · exact iff_of_false (fun h => hxb h.symm) (by tauto)
      · exact iff_of_true hby (Or.inr ⟨rfl, rfl⟩)
    · have e1 := hca u hc
      have e2 := hac u hc
      have e3 := hcb u hc
      have e4 := hbc u hc
      rcases hw with rfl | rfl
      · exact iff_of_false (fun h => hxc u hc h.symm) (by tauto)
      · exact iff_of_false (fun h => hyc u hc h.symm) (by tauto)
  · intro u hu w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases htQ u hu with rfl | rfl | hz
    · rcases hw with rfl | rfl
      · exact iff_of_false (not_not_intro hax.symm) (by tauto)
      · exact iff_of_true hxb (Or.inr ⟨rfl, rfl⟩)
    · rcases hw with rfl | rfl
      · exact iff_of_true hya (Or.inl ⟨rfl, rfl⟩)
      · exact iff_of_false (not_not_intro hby.symm) (by tauto)
    · have e1 := hzx u hz
      have e2 := hxz u hz
      have e3 := hzy u hz
      have e4 := hyz u hz
      rcases hw with rfl | rfl
      · exact iff_of_false (not_not_intro (haz u hz).symm) (by tauto)
      · exact iff_of_false (not_not_intro (hbz u hz).symm) (by tauto)

/-- **The knot conditions, at the level of the data of the four (anti)paths.**

This is the shape in which the printed proof of 9.5 uses the definition of a twist: three of the
four strip/antistrip pairs are parallel and the fourth is co-parallel (whose parallel form is
`p22` below, `S₂` being parallel to the *reverse* of `T₂`). -/
private theorem isKnot_of_data {G : SimpleGraph V}
    {A₁ C₁ B₁ A₂ C₂ B₂ X₁ Z₁ Y₁ X₂ Z₂ Y₂ : Set V} {P₁ P₂ Q₁ Q₂ : List V}
    {a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V}
    (dA₁B₁ : Disjoint A₁ B₁) (dA₁C₁ : Disjoint A₁ C₁) (dB₁C₁ : Disjoint B₁ C₁)
    (dA₂B₂ : Disjoint A₂ B₂) (dA₂C₂ : Disjoint A₂ C₂) (dB₂C₂ : Disjoint B₂ C₂)
    (dX₁Y₁ : Disjoint X₁ Y₁) (dX₁Z₁ : Disjoint X₁ Z₁) (dY₁Z₁ : Disjoint Y₁ Z₁)
    (dX₂Y₂ : Disjoint X₂ Y₂) (dX₂Z₂ : Disjoint X₂ Z₂) (dY₂Z₂ : Disjoint Y₂ Z₂)
    (haA₁ : a₁ ∈ A₁) (hbB₁ : b₁ ∈ B₁) (hp₁ : IsPathFrom G P₁ a₁ b₁)
    (tri₁ : ∀ v ∈ P₁, v = a₁ ∨ v = b₁ ∨ v ∈ C₁)
    (haA₂ : a₂ ∈ A₂) (hbB₂ : b₂ ∈ B₂) (hp₂ : IsPathFrom G P₂ a₂ b₂)
    (tri₂ : ∀ v ∈ P₂, v = a₂ ∨ v = b₂ ∨ v ∈ C₂)
    (hxX₁ : x₁ ∈ X₁) (hyY₁ : y₁ ∈ Y₁) (hq₁ : IsPathFrom Gᶜ Q₁ x₁ y₁)
    (triq₁ : ∀ v ∈ Q₁, v = x₁ ∨ v = y₁ ∨ v ∈ Z₁)
    (hxX₂ : x₂ ∈ X₂) (hyY₂ : y₂ ∈ Y₂) (hq₂ : IsPathFrom Gᶜ Q₂ x₂ y₂)
    (triq₂ : ∀ v ∈ Q₂, v = x₂ ∨ v = y₂ ∨ v ∈ Z₂)
    (hl₁ : 1 ≤ pathLength P₁) (hl₂ : 1 ≤ pathLength P₂)
    (hm₁ : 1 ≤ pathLength Q₁) (hm₂ : 1 ≤ pathLength Q₂)
    (d12 : ∀ v ∈ P₁, v ∉ P₂) (d1q1 : ∀ v ∈ P₁, v ∉ Q₁) (d1q2 : ∀ v ∈ P₁, v ∉ Q₂)
    (d2q1 : ∀ v ∈ P₂, v ∉ Q₁) (d2q2 : ∀ v ∈ P₂, v ∉ Q₂) (dqq : ∀ v ∈ Q₁, v ∉ Q₂)
    (hanti : Anticomplete G {v : V | v ∈ P₁} {v : V | v ∈ P₂})
    (hcomp : Complete G {v : V | v ∈ Q₁} {v : V | v ∈ Q₂})
    (p11 : ParallelStripAntistrip G (A₁, C₁, B₁) (X₁, Z₁, Y₁))
    (p12 : ParallelStripAntistrip G (A₁, C₁, B₁) (X₂, Z₂, Y₂))
    (p21 : ParallelStripAntistrip G (A₂, C₂, B₂) (X₁, Z₁, Y₁))
    (p22 : ParallelStripAntistrip G (A₂, C₂, B₂) (Y₂, Z₂, X₂)) :
    IsKnot G P₁ P₂ Q₁ Q₂ := by
  obtain ⟨E11, N11⟩ := edge_pattern haA₁ hbB₁ hxX₁ hyY₁ dA₁B₁ dA₁C₁ dB₁C₁
    dX₁Y₁ dX₁Z₁ dY₁Z₁ p11 tri₁ triq₁
  obtain ⟨E12, N12⟩ := edge_pattern haA₁ hbB₁ hxX₂ hyY₂ dA₁B₁ dA₁C₁ dB₁C₁
    dX₂Y₂ dX₂Z₂ dY₂Z₂ p12 tri₁ triq₂
  obtain ⟨E21, N21⟩ := edge_pattern haA₂ hbB₂ hxX₁ hyY₁ dA₂B₂ dA₂C₂ dB₂C₂
    dX₁Y₁ dX₁Z₁ dY₁Z₁ p21 tri₂ triq₁
  obtain ⟨E22, N22⟩ := edge_pattern (A := A₂) (C := C₂) (B := B₂)
    (X := Y₂) (Z := Z₂) (Y := X₂) haA₂ hbB₂ hyY₂ hxX₂ dA₂B₂ dA₂C₂ dB₂C₂
    dX₂Y₂.symm dY₂Z₂ dX₂Z₂ p22 tri₂
    (fun v hv => by have h := triq₂ v hv; tauto)
  refine ⟨a₁, b₁, a₂, b₂, x₁, y₁, x₂, y₂, hp₁, hp₂, hq₁, hq₂,
    d12, d1q1, d1q2, d2q1, d2q2, dqq, hl₁, hl₂, hm₁, hm₂, hanti, hcomp,
    E11, E12, E21, ?_, N11, N12, N21, N22⟩
  intro u hu w hw
  refine E22 u hu w ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
  tauto

/-- **PAPER (9.5, and again in 9.4): *"if we choose an `Sᵢ`-rung and `Sᵢ'`-rung and apply 9.3 to
the resultant knot"*.**

Two rungs and two antirungs of four members of a striation which are parallel in the pattern
`S₁∥T₁`, `S₁∥T₂`, `S₂∥T₁`, `S₂` co-parallel `T₂` — that is, of a **twist** — form a knot. -/
private theorem isKnot_of_parallel {G : SimpleGraph V}
    {S₁ S₂ T₁ T₂ : Set V × Set V × Set V} {P₁ P₂ Q₁ Q₂ : List V}
    (hS₁ : IsStrip G S₁) (hS₂ : IsStrip G S₂)
    (hT₁ : IsAntistrip G T₁) (hT₂ : IsAntistrip G T₂)
    (hR₁ : IsSRung G S₁ P₁) (hR₂ : IsSRung G S₂ P₂)
    (hU₁ : IsSRung Gᶜ T₁ Q₁) (hU₂ : IsSRung Gᶜ T₂ Q₂)
    (hl₁ : 1 ≤ pathLength P₁) (hl₂ : 1 ≤ pathLength P₂)
    (hm₁ : 1 ≤ pathLength Q₁) (hm₂ : 1 ≤ pathLength Q₂)
    (dSS : Disjoint (stripVertices S₁) (stripVertices S₂))
    (dS₁T₁ : Disjoint (stripVertices S₁) (stripVertices T₁))
    (dS₁T₂ : Disjoint (stripVertices S₁) (stripVertices T₂))
    (dS₂T₁ : Disjoint (stripVertices S₂) (stripVertices T₁))
    (dS₂T₂ : Disjoint (stripVertices S₂) (stripVertices T₂))
    (dTT : Disjoint (stripVertices T₁) (stripVertices T₂))
    (hanti : Anticomplete G (stripVertices S₁) (stripVertices S₂))
    (hcomp : Complete G (stripVertices T₁) (stripVertices T₂))
    (p11 : ParallelStripAntistrip G S₁ T₁) (p12 : ParallelStripAntistrip G S₁ T₂)
    (p21 : ParallelStripAntistrip G S₂ T₁) (p22 : CoParallel G S₂ T₂) :
    IsKnot G P₁ P₂ Q₁ Q₂ := by
  obtain ⟨A₁, C₁, B₁⟩ := S₁
  obtain ⟨A₂, C₂, B₂⟩ := S₂
  obtain ⟨X₁, Z₁, Y₁⟩ := T₁
  obtain ⟨X₂, Z₂, Y₂⟩ := T₂
  obtain ⟨dA₁B₁, dA₁C₁, dB₁C₁, -⟩ := hS₁
  obtain ⟨dA₂B₂, dA₂C₂, dB₂C₂, -⟩ := hS₂
  obtain ⟨dX₁Y₁, dX₁Z₁, dY₁Z₁, -⟩ := hT₁
  obtain ⟨dX₂Y₂, dX₂Z₂, dY₂Z₂, -⟩ := hT₂
  obtain ⟨a₁, b₁, haA₁, hbB₁, hp₁, tri₁⟩ := srung_tri hR₁
  obtain ⟨a₂, b₂, haA₂, hbB₂, hp₂, tri₂⟩ := srung_tri hR₂
  obtain ⟨x₁, y₁, hxX₁, hyY₁, hq₁, triq₁⟩ := srung_tri hU₁
  obtain ⟨x₂, y₂, hxX₂, hyY₂, hq₂, triq₂⟩ := srung_tri hU₂
  have mP₁ : ∀ v ∈ P₁, v ∈ stripVertices ((A₁, C₁, B₁) : Set V × Set V × Set V) :=
    fun v hv => mem_sv haA₁ hbB₁ tri₁ hv
  have mP₂ : ∀ v ∈ P₂, v ∈ stripVertices ((A₂, C₂, B₂) : Set V × Set V × Set V) :=
    fun v hv => mem_sv haA₂ hbB₂ tri₂ hv
  have mQ₁ : ∀ v ∈ Q₁, v ∈ stripVertices ((X₁, Z₁, Y₁) : Set V × Set V × Set V) :=
    fun v hv => mem_sv hxX₁ hyY₁ triq₁ hv
  have mQ₂ : ∀ v ∈ Q₂, v ∈ stripVertices ((X₂, Z₂, Y₂) : Set V × Set V × Set V) :=
    fun v hv => mem_sv hxX₂ hyY₂ triq₂ hv
  exact isKnot_of_data dA₁B₁ dA₁C₁ dB₁C₁ dA₂B₂ dA₂C₂ dB₂C₂ dX₁Y₁ dX₁Z₁ dY₁Z₁
    dX₂Y₂ dX₂Z₂ dY₂Z₂ haA₁ hbB₁ hp₁ tri₁ haA₂ hbB₂ hp₂ tri₂ hxX₁ hyY₁ hq₁ triq₁
    hxX₂ hyY₂ hq₂ triq₂ hl₁ hl₂ hm₁ hm₂
    (fun v hv hv2 => Set.disjoint_left.mp dSS (mP₁ v hv) (mP₂ v hv2))
    (fun v hv hv2 => Set.disjoint_left.mp dS₁T₁ (mP₁ v hv) (mQ₁ v hv2))
    (fun v hv hv2 => Set.disjoint_left.mp dS₁T₂ (mP₁ v hv) (mQ₂ v hv2))
    (fun v hv hv2 => Set.disjoint_left.mp dS₂T₁ (mP₂ v hv) (mQ₁ v hv2))
    (fun v hv hv2 => Set.disjoint_left.mp dS₂T₂ (mP₂ v hv) (mQ₂ v hv2))
    (fun v hv hv2 => Set.disjoint_left.mp dTT (mQ₁ v hv) (mQ₂ v hv2))
    (fun v hv w hw => hanti v (mP₁ v hv) w (mP₂ w hw))
    (fun v hv w hw => hcomp v (mQ₁ v hv) w (mQ₂ w hw))
    p11 p12 p21 p22

/-! ### The hypothesis packages -/

/-- The standing hypotheses of 9.5: `G` Berge, no appearance of a `K₄`-enlargement and no
overshadowed appearance of `K₄` in either orientation, and `L = (S, T)` a **maximal** striation.
-/
def Setup (Gx : SimpleGraph V) {m n : ℕ}
    (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V) : Prop :=
  Berge Gx ∧
  (¬ ∃ (k : ℕ) (J' : SimpleGraph (Fin k)),
    IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears Gx J' ∨ Appears Gxᶜ J')) ∧
  (¬ ∃ (k : ℕ) (H : SimpleGraph (Fin k)) (K' : Set V) (φ : H.lineGraph ≃g Gx.induce K'),
    IsAppearance Gx (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gx H K' φ) ∧
  (¬ ∃ (k : ℕ) (H : SimpleGraph (Fin k)) (K' : Set V) (φ : H.lineGraph ≃g Gxᶜ.induce K'),
    IsAppearance Gxᶜ (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gxᶜ H K' φ) ∧
  MaximalStriation Gx S T

/-- PAPER: *"Let `F ⊆ V(G) \ V(L)` be connected, such that for each `f ∈ F`, the set of its
neighbours in `V(L)` is local with respect to `L`."* -/
def Cand (Gx : SimpleGraph V) {m n : ℕ}
    (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V)
    (F : Set V) : Prop :=
  F ⊆ (striationVertices S T)ᶜ ∧ ConnectedSet Gx F ∧
  ∀ f ∈ F, LocalForStriation Gx S T (Gx.neighborSet f ∩ striationVertices S T)

/-- PAPER: *"choose a counterexample `F` with `F` minimal"* — every strictly smaller admissible
configuration inside `F` is not a counterexample. -/
def Minimal (Gx : SimpleGraph V) {m n : ℕ}
    (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V)
    (F : Set V) : Prop :=
  ∀ F' : Set V, F' ⊆ F → F'.ncard < F.ncard → Cand Gx S T F' →
    LocalForStriation Gx S T (attachments Gx F' (striationVertices S T))

/-- If two nonadjacent attachments lie on opposite sides of the striation, minimality makes
`F` the interior of an induced path between them.  This is the common first reduction in the
closing paragraph of 9.5. -/
private theorem minimal_path_between_attachments {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {F : Set V}
    (hL : IsStriation Gx S T) (hF : Cand Gx S T F) (hmin : Minimal Gx S T F) {u w : V}
    (hu : u ∈ attachments Gx F (striationVertices S T))
    (hw : w ∈ attachments Gx F (striationVertices S T))
    (huS : u ∈ ⋃ i : Fin m, stripVertices (S i))
    (hwT : w ∈ ⋃ j : Fin n, stripVertices (T j)) (huw : ¬ Gx.Adj u w) :
    ∃ p : List V, IsPathFrom Gx p u w ∧ 3 ≤ p.length ∧
      {z : V | z ∈ SPGT.interior p} = F := by
  obtain ⟨huL, fu, hfuF, hufu⟩ := hu
  obtain ⟨hwL, fw, hfwF, hwfw⟩ := hw
  have huF : u ∉ F := fun h => hF.1 h huL
  have hwF : w ∉ F := fun h => hF.1 h hwL
  have huwne : u ≠ w := by
    obtain ⟨i, hui⟩ := Set.mem_iUnion.mp huS
    obtain ⟨j, hwj⟩ := Set.mem_iUnion.mp hwT
    exact fun huw => Set.disjoint_left.mp (hL.2.2.2.2.1 i j) hui (huw ▸ hwj)
  obtain ⟨p, hp, hp3, hpF, hpconn, hpua, hpwa⟩ :=
    MinimalConnectedIsPath.exists_path_interior_attached hF.2.1 huwne huw huF hwF
      ⟨fu, hfuF, hufu⟩ ⟨fw, hfwF, hwfw⟩
  let F' : Set V := {z : V | z ∈ SPGT.interior p}
  have hsub : F' ⊆ F := hpF
  have hcand : Cand Gx S T F' :=
    ⟨fun z hz => hF.1 (hpF z hz), hpconn,
      fun z hz => hF.2.2 z (hpF z hz)⟩
  obtain ⟨du, hduI, hudu⟩ := hpua
  obtain ⟨dw, hdwI, hwdw⟩ := hpwa
  have hu' : u ∈ attachments Gx F' (striationVertices S T) :=
    ⟨huL, du, hduI, hudu⟩
  have hw' : w ∈ attachments Gx F' (striationVertices S T) :=
    ⟨hwL, dw, hdwI, hwdw⟩
  have hnlocal : ¬ LocalForStriation Gx S T
      (attachments Gx F' (striationVertices S T)) := by
    rintro ⟨-, -, hcomplete⟩
    exact huw (hcomplete u ⟨hu', huS⟩ w ⟨hw', hwT⟩)
  have hnlt : ¬ F'.ncard < F.ncard := fun hlt => hnlocal (hmin F' hsub hlt hcand)
  have heq : F' = F :=
    Set.eq_of_subset_of_ncard_le hsub (not_lt.mp hnlt) (Set.toFinite F)
  exact ⟨p, hp, hp3, heq⟩

/-! ### Claim (2)

PAPER: *"(2) `X` meets exactly one of `S₁, …, S_m`.  For by (1) it meets at least one of these
sets; suppose it meets two, say `S₁` and `S₂`.  We may assume that `(S₁,S₂,T₁,T₂)` is a twist.
For `i = 1,2` choose an `Sᵢ`-rung `aᵢ-Pᵢ-bᵢ` such that `X` meets `Pᵢ`, and for `j = 1,2` let
`xⱼ-Qⱼ-yⱼ` be a `Tⱼ`-antirung.  Then `(P₁,P₂,Q₁,Q₂)` is a knot `K` say, and `X ∩ V(K)` is not
local with respect to `K`.  From the minimality of `F`, `F` is minimal such that `X ∩ V(K)` is
not local with respect to `K`.  It follows from 9.3 that one of 9.3.1, 9.3.4 holds; and in
either case there is a vertex `f ∈ F` with neighbours in `P₁` and in `P₂`.  Hence the set of
neighbours of `f` in `V(L)` is not local with respect to `L`.  But this contradicts a hypothesis
of the theorem, and hence proves (2)."*

The small lemmas below are the bookkeeping the paragraph leaves implicit. -/

/-- Every vertex of a strip lies on some rung (the covering clause of `IsStrip`). -/
private theorem exists_rung_through {G : SimpleGraph V} {Sx : Set V × Set V × Set V}
    (h : IsStrip G Sx) {v : V} (hv : v ∈ stripVertices Sx) :
    ∃ p : List V, IsSRung G Sx p ∧ v ∈ p := by
  obtain ⟨A, C, B⟩ := Sx
  exact h.2.2.2.2.2 v hv

/-- A strip has at least one rung (`A` is nonempty and every vertex lies on a rung). -/
private theorem exists_rung {G : SimpleGraph V} {Sx : Set V × Set V × Set V}
    (h : IsStrip G Sx) : ∃ p : List V, IsSRung G Sx p := by
  obtain ⟨A, C, B⟩ := Sx
  obtain ⟨a, ha⟩ := h.2.2.2.1
  obtain ⟨p, hp, -⟩ := h.2.2.2.2.2 a (Set.mem_union_left _ (Set.mem_union_left _ ha))
  exact ⟨p, hp⟩

/-- A twist can be chosen through any prescribed strip and antistrip.  This is the sign-matrix
bookkeeping behind each occurrence of "choose the other strip and antistrip to make a twist"
in 9.5. -/
private theorem exists_twist_through {G : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (hL : IsStriation G S T) (i : Fin m) (j : Fin n) :
    ∃ i' : Fin m, ∃ j' : Fin n, i ≠ i' ∧ j ≠ j' ∧
      IsTwist G (S i) (S i') (T j) (T j') := by
  have hm : 2 ≤ m := hL.2.2.2.2.2.2.2.1
  obtain ⟨i', hii'⟩ : ∃ i' : Fin m, i ≠ i' := by
    by_cases hi : (i : ℕ) = 0
    · refine ⟨⟨1, by omega⟩, fun h => ?_⟩
      have : (i : ℕ) = 1 := congrArg Fin.val h
      omega
    · refine ⟨⟨0, by omega⟩, fun h => ?_⟩
      exact hi (congrArg Fin.val h)
  have hpar : ∀ k : Fin n,
      ParallelStripAntistrip G (S i) (T k) ∨ CoParallel G (S i) (T k) :=
    hL.2.2.2.2.2.2.2.2.2.2.2.1 i
  have hpar' : ∀ k : Fin n,
      ParallelStripAntistrip G (S i') (T k) ∨ CoParallel G (S i') (T k) :=
    hL.2.2.2.2.2.2.2.2.2.2.2.1 i'
  let Ag : Fin n → Prop := fun k => AgreeOn G (S i) (S i') (T k)
  let Ds : Fin n → Prop := fun k =>
    (ParallelStripAntistrip G (S i) (T k) ∧ CoParallel G (S i') (T k)) ∨
      (CoParallel G (S i) (T k) ∧ ParallelStripAntistrip G (S i') (T k))
  have hcover : ∀ k, Ag k ∨ Ds k := by
    intro k
    rcases hpar k with h | h <;> rcases hpar' k with h' | h' <;>
      simp only [Ag, Ds, AgreeOn] <;> tauto
  obtain ⟨c, d, hcd, htw'⟩ : ∃ c d : Fin n, c ≠ d ∧
      IsTwist G (S i) (S i') (T c) (T d) := by
    rcases lt_trichotomy i i' with hil | heq | hil
    · exact hL.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hil
    · exact absurd heq hii'
    · obtain ⟨c, d, hcd, htw⟩ :=
        hL.2.2.2.2.2.2.2.2.2.2.2.2.1 i' i hil
      refine ⟨c, d, hcd, ?_⟩
      simp only [IsTwist, AgreeOn] at htw ⊢
      tauto
  have htwCD : (Ag c ∧ Ds d) ∨ (Ag d ∧ Ds c) := by
    simpa only [IsTwist, Ag, Ds] using htw'
  have choose_partner : ∀ c d : Fin n, c ≠ d → Ag c → Ds d →
      ∃ j' : Fin n, j ≠ j' ∧ ((Ag j ∧ Ds j') ∨ (Ag j' ∧ Ds j)) := by
    intro c d hcd hc hd
    by_cases hjd : j = d
    · refine ⟨c, ?_, Or.inr ⟨hc, by simpa [hjd] using hd⟩⟩
      exact fun hjc => hcd (hjc.symm.trans hjd)
    · rcases hcover j with hj | hj
      · exact ⟨d, hjd, Or.inl ⟨hj, hd⟩⟩
      · by_cases hjc : j = c
        · exact ⟨d, hjd, Or.inl ⟨by simpa [hjc] using hc, hd⟩⟩
        · exact ⟨c, hjc, Or.inr ⟨hc, hj⟩⟩
  have hjex : ∃ j' : Fin n, j ≠ j' ∧ ((Ag j ∧ Ds j') ∨ (Ag j' ∧ Ds j)) := by
    rcases htwCD with ⟨hc, hd⟩ | ⟨hd, hc⟩
    · exact choose_partner c d hcd hc hd
    · exact choose_partner d c hcd.symm hd hc
  obtain ⟨j', hjj', htwj⟩ := hjex
  refine ⟨i', j', hii', hjj', ?_⟩
  simpa only [IsTwist, Ag, Ds] using htwj

/-- Reversal does not change the vertex set of a list. -/
private theorem mem_iff_of_eq_or_reverse {p q : List V} (h : q = p ∨ q = p.reverse) (v : V) :
    v ∈ q ↔ v ∈ p := by
  rcases h with rfl | rfl
  · exact Iff.rfl
  · exact List.mem_reverse

/-- Reading the third bullet of `IsKnot` "the other way round": the only vertex of `P` adjacent
to `c` is the end `a`. -/
private theorem edge_end {G : SimpleGraph V} {P : List V} {a a' c c' : V} (hcc : c ≠ c')
    (E : ∀ u ∈ P, ∀ w ∈ ({c, c'} : Set V),
      (G.Adj u w ↔ ((u = a ∧ w = c) ∨ (u = a' ∧ w = c')))) :
    ∀ u ∈ P, u ≠ a → ¬ G.Adj u c := by
  intro u hu hua hadj
  rcases (E u hu c (Set.mem_insert _ _)).mp hadj with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact hua h1
  · exact hcc h2

/-- The third bullet of `IsKnot` with the two ends of the antipath exchanged. -/
private theorem swap_E {G : SimpleGraph V} {P : List V} {a a' c c' : V}
    (E : ∀ u ∈ P, ∀ w ∈ ({c, c'} : Set V),
      (G.Adj u w ↔ ((u = a ∧ w = c) ∨ (u = a' ∧ w = c')))) :
    ∀ u ∈ P, ∀ w ∈ ({c', c} : Set V),
      (G.Adj u w ↔ ((u = a' ∧ w = c') ∨ (u = a ∧ w = c))) := by
  intro u hu w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  have h := E u hu w (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)
  tauto

/-- The fourth bullet of `IsKnot` with the two ends of the path exchanged. -/
private theorem swap_N {G : SimpleGraph V} {Q : List V} {a a' x x' : V}
    (N : ∀ u ∈ Q, ∀ w ∈ ({a, a'} : Set V),
      (¬ G.Adj u w ↔ ((w = a ∧ u = x') ∨ (w = a' ∧ u = x)))) :
    ∀ u ∈ Q, ∀ w ∈ ({a', a} : Set V),
      (¬ G.Adj u w ↔ ((w = a' ∧ u = x) ∨ (w = a ∧ u = x'))) := by
  intro u hu w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  have h := N u hu w (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)
  tauto

/-- Reading the fourth bullet of `IsKnot`: the end `x` of the antipath is adjacent to the end `a`
of the path. -/
private theorem adj_end {G : SimpleGraph V} {Q : List V} {a a' x x' : V}
    (haa : a ≠ a') (hxx : x ≠ x') (hxQ : x ∈ Q)
    (N : ∀ u ∈ Q, ∀ w ∈ ({a, a'} : Set V),
      (¬ G.Adj u w ↔ ((w = a ∧ u = x') ∨ (w = a' ∧ u = x)))) :
    G.Adj x a := by
  by_contra h
  rcases (N x hxQ a (Set.mem_insert _ _)).mp h with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact hxx h2
  · exact haa h1

/-- Reading the fourth bullet of `IsKnot`: every vertex of the antipath is adjacent to at least
one of the two ends of the path. -/
private theorem cover_ends {G : SimpleGraph V} {Q : List V} {a a' x x' : V}
    (haa : a ≠ a') (hxx : x ≠ x')
    (N : ∀ u ∈ Q, ∀ w ∈ ({a, a'} : Set V),
      (¬ G.Adj u w ↔ ((w = a ∧ u = x') ∨ (w = a' ∧ u = x)))) :
    ∀ u ∈ Q, G.Adj u a ∨ G.Adj u a' := by
  intro u hu
  by_contra h
  rw [not_or] at h
  obtain ⟨h1, h2⟩ := h
  rcases (N u hu a (Set.mem_insert _ _)).mp h1 with ⟨-, e1⟩ | ⟨e1, -⟩
  · rcases (N u hu a' (Set.mem_insert_of_mem _ rfl)).mp h2 with ⟨e2, -⟩ | ⟨-, e2⟩
    · exact haa e2.symm
    · exact hxx (e2.symm.trans e1)
  · exact haa e1

/-- The body of claim (2), with the two indices ordered so that the striation's twist axiom
applies. -/
private theorem claim2_aux {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {F : Set V}
    (hs : Setup Gx S T) (hF : Cand Gx S T F) (hmin : Minimal Gx S T F)
    (i i' : Fin m) (hlt : i < i')
    (hi : (attachments Gx F (striationVertices S T) ∩ stripVertices (S i)).Nonempty)
    (hi' : (attachments Gx F (striationVertices S T) ∩ stripVertices (S i')).Nonempty) :
    False := by
  obtain ⟨hberge, hnoenl, hnoover, hnoovercompl, hmax⟩ := hs
  have hL : IsStriation Gx S T := hmax.1
  have hne : i ≠ i' := ne_of_lt hlt
  obtain ⟨hstrip, hantis, -, -, -, -, -, -, -, -, -, -, htwist, -⟩ := id hL
  -- PAPER: *"We may assume that `(S₁,S₂,T₁,T₂)` is a twist."*
  obtain ⟨j, j', hjj, htw⟩ := htwist i i' hlt
  -- PAPER: *"choose an `Sᵢ`-rung `aᵢ-Pᵢ-bᵢ` such that `X` meets `Pᵢ`"*
  obtain ⟨v₁, hv₁X, hv₁S⟩ := hi
  obtain ⟨P₁, hP₁, hv₁P⟩ := exists_rung_through (hstrip i) hv₁S
  obtain ⟨v₂, hv₂X, hv₂S⟩ := hi'
  obtain ⟨P₂, hP₂, hv₂P⟩ := exists_rung_through (hstrip i') hv₂S
  -- PAPER: *"and for `j = 1,2` let `xⱼ-Qⱼ-yⱼ` be a `Tⱼ`-antirung"*
  obtain ⟨Q₁, hQ₁⟩ := exists_rung (hantis j : IsStrip Gxᶜ (T j))
  obtain ⟨Q₂, hQ₂⟩ := exists_rung (hantis j' : IsStrip Gxᶜ (T j'))
  -- PAPER: *"Then `(P₁,P₂,Q₁,Q₂)` is a knot `K`."*
  obtain ⟨P₁', P₂', Q₁', Q₂', e₁, e₂, e₃, e₄, hknot⟩ :=
    KnotFromTwist.exists_knot_of_twist hL hne hjj htw hP₁ hP₂ hQ₁ hQ₂
  have mP₁ : ∀ v : V, v ∈ P₁' ↔ v ∈ P₁ := mem_iff_of_eq_or_reverse e₁
  have mP₂ : ∀ v : V, v ∈ P₂' ↔ v ∈ P₂ := mem_iff_of_eq_or_reverse e₂
  have mQ₁ : ∀ v : V, v ∈ Q₁' ↔ v ∈ Q₁ := mem_iff_of_eq_or_reverse e₃
  have mQ₂ : ∀ v : V, v ∈ Q₂' ↔ v ∈ Q₂ := mem_iff_of_eq_or_reverse e₄
  -- the four lists live inside `V(L)`
  have hSmemP₁ : ∀ v ∈ P₁', v ∈ (⋃ k : Fin m, stripVertices (S k)) := fun v hv =>
    Set.mem_iUnion.mpr ⟨i, KnotFromTwist.mem_stripVertices_of_isSRung hP₁ ((mP₁ v).mp hv)⟩
  have hSmemP₂ : ∀ v ∈ P₂', v ∈ (⋃ k : Fin m, stripVertices (S k)) := fun v hv =>
    Set.mem_iUnion.mpr ⟨i', KnotFromTwist.mem_stripVertices_of_isSRung hP₂ ((mP₂ v).mp hv)⟩
  have hTmemQ₁ : ∀ v ∈ Q₁', v ∈ (⋃ k : Fin n, stripVertices (T k)) := fun v hv =>
    Set.mem_iUnion.mpr ⟨j, KnotFromTwist.mem_stripVertices_of_isSRung hQ₁ ((mQ₁ v).mp hv)⟩
  have hTmemQ₂ : ∀ v ∈ Q₂', v ∈ (⋃ k : Fin n, stripVertices (T k)) := fun v hv =>
    Set.mem_iUnion.mpr ⟨j', KnotFromTwist.mem_stripVertices_of_isSRung hQ₂ ((mQ₂ v).mp hv)⟩
  have hVP₁ : ∀ v ∈ P₁', v ∈ striationVertices S T := fun v hv =>
    Set.mem_union_left _ (hSmemP₁ v hv)
  have hVP₂ : ∀ v ∈ P₂', v ∈ striationVertices S T := fun v hv =>
    Set.mem_union_left _ (hSmemP₂ v hv)
  have hVQ₁ : ∀ v ∈ Q₁', v ∈ striationVertices S T := fun v hv =>
    Set.mem_union_right _ (hTmemQ₁ v hv)
  have hVQ₂ : ∀ v ∈ Q₂', v ∈ striationVertices S T := fun v hv =>
    Set.mem_union_right _ (hTmemQ₂ v hv)
  have hFK : F ⊆ ({v : V | v ∈ P₁'} ∪ {v : V | v ∈ P₂'} ∪ {v : V | v ∈ Q₁'} ∪
      {v : V | v ∈ Q₂'})ᶜ := by
    intro f hf hfK
    refine hF.1 hf ?_
    rcases hfK with ((hv | hv) | hv) | hv
    · exact hVP₁ f hv
    · exact hVP₂ f hv
    · exact hVQ₁ f hv
    · exact hVQ₂ f hv
  -- PAPER: *"and `X ∩ V(K)` is not local with respect to `K`"* — because `X` meets both rungs
  have hnl : ¬ LocalForKnot Gx P₁' P₂' Q₁' Q₂'
      (attachments Gx F ({v : V | v ∈ P₁'} ∪ {v : V | v ∈ P₂'} ∪ {v : V | v ∈ Q₁'} ∪
        {v : V | v ∈ Q₂'})) := by
    rintro ⟨hd, -, -, -⟩
    have h1 : v₁ ∈ attachments Gx F ({v : V | v ∈ P₁'} ∪ {v : V | v ∈ P₂'} ∪
        {v : V | v ∈ Q₁'} ∪ {v : V | v ∈ Q₂'}) :=
      ⟨Or.inl (Or.inl (Or.inl ((mP₁ v₁).mpr hv₁P))), hv₁X.2⟩
    have h2 : v₂ ∈ attachments Gx F ({v : V | v ∈ P₁'} ∪ {v : V | v ∈ P₂'} ∪
        {v : V | v ∈ Q₁'} ∪ {v : V | v ∈ Q₂'}) :=
      ⟨Or.inl (Or.inl (Or.inr ((mP₂ v₂).mpr hv₂P))), hv₂X.2⟩
    rcases hd with hd | hd
    · exact Set.disjoint_left.mp hd h1 ((mP₁ v₁).mpr hv₁P)
    · exact Set.disjoint_left.mp hd h2 ((mP₂ v₂).mpr hv₂P)
  -- the eight labels of the knot
  obtain ⟨a₁, b₁, a₂, b₂, x₁, y₁, x₂, y₂, hp1, hp2, hq1, hq2,
    d12, d1q1, d1q2, d2q1, d2q2, dqq, l1, l2, l3, l4, hanti, hcomp,
    E11, E12, E21, E22, N11, N12, N21, N22⟩ := id hknot
  obtain ⟨ha₁P, hb₁P⟩ := PathBasics.isPathFrom_ends_mem hp1
  obtain ⟨ha₂P, hb₂P⟩ := PathBasics.isPathFrom_ends_mem hp2
  obtain ⟨hx₁Q, hy₁Q⟩ := PathBasics.isPathFrom_ends_mem hq1
  obtain ⟨hx₂Q, hy₂Q⟩ := PathBasics.isPathFrom_ends_mem hq2
  have hab₁ : a₁ ≠ b₁ := PathBasics.isPathFrom_ends_ne hp1 l1
  have hab₂ : a₂ ≠ b₂ := PathBasics.isPathFrom_ends_ne hp2 l2
  have hxy₁ : x₁ ≠ y₁ := PathBasics.isPathFrom_ends_ne hq1 l3
  have hxy₂ : x₂ ≠ y₂ := PathBasics.isPathFrom_ends_ne hq2 l4
  -- the eight edges between the ends of the antipaths and the ends of the paths
  have ax1a1 : Gx.Adj x₁ a₁ := adj_end hab₁ hxy₁ hx₁Q N11
  have ay1b1 : Gx.Adj y₁ b₁ := adj_end hab₁.symm hxy₁.symm hy₁Q (swap_N N11)
  have ax1a2 : Gx.Adj x₁ a₂ := adj_end hab₂ hxy₁ hx₁Q N21
  have ay1b2 : Gx.Adj y₁ b₂ := adj_end hab₂.symm hxy₁.symm hy₁Q (swap_N N21)
  have ax2a1 : Gx.Adj x₂ a₁ := adj_end hab₁ hxy₂ hx₂Q N12
  have ay2b1 : Gx.Adj y₂ b₁ := adj_end hab₁.symm hxy₂.symm hy₂Q (swap_N N12)
  have ay2a2 : Gx.Adj y₂ a₂ := adj_end hab₂ hxy₂.symm hy₂Q N22
  have ax2b2 : Gx.Adj x₂ b₂ := adj_end hab₂.symm hxy₂ hx₂Q (swap_N N22)
  -- PAPER: *"there is a vertex `f ∈ F` with neighbours in `P₁` and in `P₂`.  Hence the set of
  -- neighbours of `f` in `V(L)` is not local with respect to `L`."*
  have key : ∀ f ∈ F, ∀ u ∈ P₁', ∀ w ∈ P₂', Gx.Adj f u → Gx.Adj f w → False := by
    intro f hf u hu w hw hfu hfw
    have hloc := hF.2.2 f hf
    exact hne (hloc.1 i i'
      ⟨u, ⟨hfu, hVP₁ u hu⟩, KnotFromTwist.mem_stripVertices_of_isSRung hP₁ ((mP₁ u).mp hu)⟩
      ⟨w, ⟨hfw, hVP₂ w hw⟩, KnotFromTwist.mem_stripVertices_of_isSRung hP₂ ((mP₂ w).mp hw)⟩)
  -- PAPER: *"From the minimality of `F`, `F` is minimal such that `X ∩ V(K)` is not local with
  -- respect to `K`."*  In outcomes 9.3.2 and 9.3.3 the path `R` provided has a non-local
  -- attachment set, so it must be all of `F`; but then `X` misses the other rung entirely.
  have endgame : ∀ (R : List V) (Pp' : List V), IsPathList Gx R → (∀ v ∈ R, v ∈ F) →
      (Pp' = P₁' ∨ Pp' = P₂') → (∀ f ∈ R, ∀ w ∈ Pp', ¬ Gx.Adj f w) →
      ¬ LocalForStriation Gx S T
          (attachments Gx {v : V | v ∈ R} (striationVertices S T)) → False := by
    intro R Pp' hRpath hRF hPp' hnoedge hRnl
    have hsub : {v : V | v ∈ R} ⊆ F := hRF
    have hcand : Cand Gx S T {v : V | v ∈ R} :=
      ⟨fun v hv => hF.1 (hRF v hv),
        InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hRpath,
        fun f hf => hF.2.2 f (hRF f hf)⟩
    have hnlt : ¬ ({v : V | v ∈ R}.ncard < F.ncard) := fun hlt' =>
      hRnl (hmin {v : V | v ∈ R} hsub hlt' hcand)
    have heq : {v : V | v ∈ R} = F :=
      Set.eq_of_subset_of_ncard_le hsub (not_lt.mp hnlt) (Set.toFinite F)
    rcases hPp' with rfl | rfl
    · obtain ⟨-, f, hfF, hadj⟩ := hv₁X
      have hfR : f ∈ R := by rw [← heq] at hfF; exact hfF
      exact hnoedge f hfR v₁ ((mP₁ v₁).mpr hv₁P) hadj.symm
    · obtain ⟨-, f, hfF, hadj⟩ := hv₂X
      have hfR : f ∈ R := by rw [← heq] at hfF; exact hfF
      exact hnoedge f hfR v₂ ((mP₂ v₂).mpr hv₂P) hadj.symm
  -- outcome 9.3.2: the attachment set of `V(R)` fails the third bullet of locality
  have out2 : ∀ (a c : V) (Pp Pp' R : List V) (r₁ r₂ : V),
      a ∈ Pp → c ∈ Q₁' → Gx.Adj a c → (∀ u ∈ Pp, u ≠ a → ¬ Gx.Adj u c) →
      (Pp = P₁' ∧ Pp' = P₂' ∨ Pp = P₂' ∧ Pp' = P₁') →
      IsPathFrom Gx R r₁ r₂ → (∀ v ∈ R, v ∈ F) →
      (∀ w ∈ ({v : V | v ∈ Pp'} ∪ {v : V | v ∈ Q₁'} ∪ {v : V | v ∈ Q₂'} : Set V),
        (Gx.Adj r₁ w ↔ Gx.Adj a w)) →
      Anticomplete Gx ({v : V | v ∈ R} \ {r₁})
        ({v : V | v ∈ Pp'} ∪ {v : V | v ∈ Q₁'} ∪ {v : V | v ∈ Q₂'}) →
      (∃ w ∈ ({v : V | v ∈ Pp} \ {a} : Set V), Gx.Adj r₂ w) → False := by
    intro a c Pp Pp' R r₁ r₂ haPp hcQ hac hnc hcases hRpath hRF hcopy hanticR hw2
    obtain ⟨w, ⟨hwPp, hwa⟩, hadjw⟩ := hw2
    obtain ⟨hr₁R, hr₂R⟩ := PathBasics.isPathFrom_ends_mem hRpath
    have hSPp : ∀ u ∈ Pp, u ∈ (⋃ k : Fin m, stripVertices (S k)) := by
      rcases hcases with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1]; exact hSmemP₁
      · rw [h1]; exact hSmemP₂
    have hantiPp : ∀ u ∈ Pp, ∀ z ∈ Pp', ¬ Gx.Adj u z := by
      rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact fun u hu z hz => hanti u hu z hz
      · rw [h1, h2]; exact fun u hu z hz h => hanti z hz u hu h.symm
    have hcAtt : c ∈ attachments Gx {v : V | v ∈ R} (striationVertices S T) :=
      ⟨hVQ₁ c hcQ, r₁, hr₁R, ((hcopy c (Or.inl (Or.inr hcQ))).mpr hac).symm⟩
    have hwAtt : w ∈ attachments Gx {v : V | v ∈ R} (striationVertices S T) :=
      ⟨Set.mem_union_left _ (hSPp w hwPp), r₂, hr₂R, hadjw.symm⟩
    refine endgame R Pp' hRpath.1 hRF
      (by rcases hcases with ⟨-, h2⟩ | ⟨-, h2⟩; exacts [Or.inr h2, Or.inl h2]) ?_ ?_
    · intro f hf z hz
      by_cases hfr : f = r₁
      · rw [hfr, hcopy z (Or.inl (Or.inl hz))]
        exact hantiPp a haPp z hz
      · exact hanticR f ⟨hf, hfr⟩ z (Or.inl (Or.inl hz))
    · rintro ⟨-, -, hcomp3⟩
      exact hnc w hwPp hwa (hcomp3 w ⟨hwAtt, hSPp w hwPp⟩ c ⟨hcAtt, hTmemQ₁ c hcQ⟩)
  -- outcome 9.3.3: the attachment set of `V(R)` contains a whole antirung
  have out3 : ∀ (a b : V) (Pp Pp' R : List V) (r₁ r₂ : V),
      a ∈ Pp → b ∈ Pp → (Pp = P₁' ∧ Pp' = P₂' ∨ Pp = P₂' ∧ Pp' = P₁') →
      (∀ u ∈ Q₁', Gx.Adj u a ∨ Gx.Adj u b) →
      IsPathFrom Gx R r₁ r₂ → (∀ v ∈ R, v ∈ F) →
      (∀ w ∈ ({v : V | v ∈ Pp'} ∪ {v : V | v ∈ Q₁'} ∪ {v : V | v ∈ Q₂'} : Set V),
        (Gx.Adj r₁ w ↔ Gx.Adj a w)) →
      (∀ w ∈ ({v : V | v ∈ Pp'} ∪ {v : V | v ∈ Q₁'} ∪ {v : V | v ∈ Q₂'} : Set V),
        (Gx.Adj r₂ w ↔ Gx.Adj b w)) →
      Anticomplete Gx {v : V | v ∈ SPGT.interior R}
        ({v : V | v ∈ Pp'} ∪ {v : V | v ∈ Q₁'} ∪ {v : V | v ∈ Q₂'}) → False := by
    intro a b Pp Pp' R r₁ r₂ haPp hbPp hcases hcover hRpath hRF hcopy₁ hcopy₂ hanticR
    obtain ⟨hr₁R, hr₂R⟩ := PathBasics.isPathFrom_ends_mem hRpath
    have hantiPp : ∀ u ∈ Pp, ∀ z ∈ Pp', ¬ Gx.Adj u z := by
      rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact fun u hu z hz => hanti u hu z hz
      · rw [h1, h2]; exact fun u hu z hz h => hanti z hz u hu h.symm
    have hQ₁att : ∀ u ∈ Q₁',
        u ∈ attachments Gx {v : V | v ∈ R} (striationVertices S T) := by
      intro u hu
      rcases hcover u hu with h | h
      · exact ⟨hVQ₁ u hu, r₁, hr₁R, ((hcopy₁ u (Or.inl (Or.inr hu))).mpr h.symm).symm⟩
      · exact ⟨hVQ₁ u hu, r₂, hr₂R, ((hcopy₂ u (Or.inl (Or.inr hu))).mpr h.symm).symm⟩
    refine endgame R Pp' hRpath.1 hRF
      (by rcases hcases with ⟨-, h2⟩ | ⟨-, h2⟩; exacts [Or.inr h2, Or.inl h2]) ?_ ?_
    · intro f hf z hz
      by_cases hfr₁ : f = r₁
      · rw [hfr₁, hcopy₁ z (Or.inl (Or.inl hz))]
        exact hantiPp a haPp z hz
      by_cases hfr₂ : f = r₂
      · rw [hfr₂, hcopy₂ z (Or.inl (Or.inl hz))]
        exact hantiPp b hbPp z hz
      · exact hanticR f ((PathBasics.mem_interior_iff_of_pathFrom hRpath).mpr ⟨hf, hfr₁, hfr₂⟩)
          z (Or.inl (Or.inl hz))
    · rintro ⟨-, hrung, -⟩
      obtain ⟨v, hvQ, hvnot⟩ := hrung j Q₁ hQ₁
      exact hvnot (hQ₁att v ((mQ₁ v).mpr hvQ))
  have cover₁ : ∀ u ∈ Q₁', Gx.Adj u a₁ ∨ Gx.Adj u b₁ := cover_ends hab₁ hxy₁ N11
  have cover₂ : ∀ u ∈ Q₁', Gx.Adj u a₂ ∨ Gx.Adj u b₂ := cover_ends hab₂ hxy₁ N21
  -- PAPER: *"Let us apply 9.3."*
  have h93 := _root_.Workspace.Statements.S09.SPGT.thm_9_3 Gx hberge P₁' P₂' Q₁' Q₂'
    a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hp1 hp2 hq1 hq2
    ({v : V | v ∈ P₁'} ∪ {v : V | v ∈ P₂'} ∪ {v : V | v ∈ Q₁'} ∪ {v : V | v ∈ Q₂'}) rfl
    hnoenl hnoover hnoovercompl F hFK hF.2.1 hnl
  rcases h93 with h1 | h2 | h3 | h4
  · -- 9.3.1: the neighbours of `f` resolve the knot, so `f` has neighbours in `P₁` and `P₂`
    obtain ⟨f, hfF, -, ⟨u, ⟨huN, -⟩, huP⟩, ⟨w, ⟨hwN, -⟩, hwP⟩, -⟩ := h1
    exact key f hfF u huP w hwP huN hwN
  · -- 9.3.2
    obtain ⟨a, P, P', hcase, R, r₁, r₂, hRpath, hRF, hcopy, hanticR, hw2, -⟩ := h2
    rcases hcase with h | h | h | h <;> simp only [Prod.mk.injEq] at h
    · exact out2 a x₁ P P' R r₁ r₂ (by rw [h.1, h.2.1]; exact ha₁P) hx₁Q
        (by rw [h.1]; exact ax1a1.symm)
        (by rw [h.1, h.2.1]; exact edge_end hxy₁ E11)
        (Or.inl ⟨h.2.1, h.2.2⟩) hRpath hRF hcopy hanticR hw2
    · exact out2 a y₁ P P' R r₁ r₂ (by rw [h.1, h.2.1]; exact hb₁P) hy₁Q
        (by rw [h.1]; exact ay1b1.symm)
        (by rw [h.1, h.2.1]; exact edge_end hxy₁.symm (swap_E E11))
        (Or.inl ⟨h.2.1, h.2.2⟩) hRpath hRF hcopy hanticR hw2
    · exact out2 a x₁ P P' R r₁ r₂ (by rw [h.1, h.2.1]; exact ha₂P) hx₁Q
        (by rw [h.1]; exact ax1a2.symm)
        (by rw [h.1, h.2.1]; exact edge_end hxy₁ E21)
        (Or.inr ⟨h.2.1, h.2.2⟩) hRpath hRF hcopy hanticR hw2
    · exact out2 a y₁ P P' R r₁ r₂ (by rw [h.1, h.2.1]; exact hb₂P) hy₁Q
        (by rw [h.1]; exact ay1b2.symm)
        (by rw [h.1, h.2.1]; exact edge_end hxy₁.symm (swap_E E21))
        (Or.inr ⟨h.2.1, h.2.2⟩) hRpath hRF hcopy hanticR hw2
  · -- 9.3.3
    obtain ⟨a, b, P, P', hcase, R, r₁, r₂, hRpath, hRF, -, hcopy₁, hcopy₂, hanticR, -⟩ := h3
    rcases hcase with h | h | h | h <;> simp only [Prod.mk.injEq] at h
    · exact out3 a b P P' R r₁ r₂ (by rw [h.1, h.2.2.1]; exact ha₁P)
        (by rw [h.2.1, h.2.2.1]; exact hb₁P) (Or.inl ⟨h.2.2.1, h.2.2.2⟩)
        (by rw [h.1, h.2.1]; exact cover₁) hRpath hRF hcopy₁ hcopy₂ hanticR
    · exact out3 a b P P' R r₁ r₂ (by rw [h.1, h.2.2.1]; exact hb₁P)
        (by rw [h.2.1, h.2.2.1]; exact ha₁P) (Or.inl ⟨h.2.2.1, h.2.2.2⟩)
        (by rw [h.1, h.2.1]; exact fun u hu => (cover₁ u hu).symm) hRpath hRF hcopy₁ hcopy₂
        hanticR
    · exact out3 a b P P' R r₁ r₂ (by rw [h.1, h.2.2.1]; exact ha₂P)
        (by rw [h.2.1, h.2.2.1]; exact hb₂P) (Or.inr ⟨h.2.2.1, h.2.2.2⟩)
        (by rw [h.1, h.2.1]; exact cover₂) hRpath hRF hcopy₁ hcopy₂ hanticR
    · exact out3 a b P P' R r₁ r₂ (by rw [h.1, h.2.2.1]; exact hb₂P)
        (by rw [h.2.1, h.2.2.1]; exact ha₂P) (Or.inr ⟨h.2.2.1, h.2.2.2⟩)
        (by rw [h.1, h.2.1]; exact fun u hu => (cover₂ u hu).symm) hRpath hRF hcopy₁ hcopy₂
        hanticR
  · -- 9.3.4: `f` copies an end of an antipath, which has neighbours in `P₁` and in `P₂`
    obtain ⟨x, y, Q', hcase, f, hfF, hcopy, -⟩ := h4
    have step : ∀ α ∈ P₁', ∀ β ∈ P₂', Gx.Adj x α → Gx.Adj x β → False := by
      intro α hα β hβ hxα hxβ
      exact key f hfF α hα β hβ
        ((hcopy α (Or.inl (Or.inl hα))).mpr hxα) ((hcopy β (Or.inl (Or.inr hβ))).mpr hxβ)
    rcases hcase with h | h | h | h <;> simp only [Prod.mk.injEq] at h
    · exact step a₁ ha₁P a₂ ha₂P (by rw [h.1]; exact ax1a1) (by rw [h.1]; exact ax1a2)
    · exact step b₁ hb₁P b₂ hb₂P (by rw [h.1]; exact ay1b1) (by rw [h.1]; exact ay1b2)
    · exact step a₁ ha₁P b₂ hb₂P (by rw [h.1]; exact ax2a1) (by rw [h.1]; exact ax2b2)
    · exact step b₁ hb₁P a₂ ha₂P (by rw [h.1]; exact ay2b1) (by rw [h.1]; exact ay2a2)

theorem claim2 {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {F : Set V}
    (hs : Setup Gx S T) (hF : Cand Gx S T F) (hmin : Minimal Gx S T F)
    (hnot : ¬ LocalForStriation Gx S T (attachments Gx F (striationVertices S T)))
    (i i' : Fin m)
    (hi : (attachments Gx F (striationVertices S T) ∩ stripVertices (S i)).Nonempty)
    (hi' : (attachments Gx F (striationVertices S T) ∩ stripVertices (S i')).Nonempty) :
    i = i' := by
  rcases lt_trichotomy i i' with h | h | h
  · exact (claim2_aux hs hF hmin i i' h hi hi').elim
  · exact h
  · exact (claim2_aux hs hF hmin i' i h hi' hi).elim

/-! ### Claim (3) -/

/-- The third alternative of 9.3, named so that the remaining maximality step in Claim (3) can
be isolated without hiding any of the data returned by 9.3. -/
def Outcome3ForKnot (Gx : SimpleGraph V) (P₁ P₂ Q₁ Q₂ : List V)
    (a₁ b₁ a₂ b₂ : V) (F : Set V) : Prop :=
  ∃ (a b : V) (P P' : List V),
    ((a, b, P, P') = (a₁, b₁, P₁, P₂) ∨
      (a, b, P, P') = (b₁, a₁, P₁, P₂) ∨
      (a, b, P, P') = (a₂, b₂, P₂, P₁) ∨
      (a, b, P, P') = (b₂, a₂, P₂, P₁)) ∧
    ∃ (R : List V) (r₁ r₂ : V),
      IsPathFrom Gx R r₁ r₂ ∧ ( ∀ v ∈ R, v ∈ F) ∧ Odd (pathLength R) ∧
      (∀ w ∈ ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
        (Gx.Adj r₁ w ↔ Gx.Adj a w)) ∧
      (∀ w ∈ ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
        (Gx.Adj r₂ w ↔ Gx.Adj b w)) ∧
      Anticomplete Gx {v : V | v ∈ SPGT.interior R}
        ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}) ∧
      (∀ u ∈ R, ∀ w ∈ P, Gx.Adj u w →
        ((u = r₁ ∧ w = a) ∨ (u = r₂ ∧ w = b)))

/-- Minimality identifies any connected subset whose attachments are already non-local. -/
theorem minimal_eq_of_nonlocal_subset {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    {F F' : Set V} (hF : Cand Gx S T F) (hmin : Minimal Gx S T F)
    (hsub : F' ⊆ F) (hconn : ConnectedSet Gx F')
    (hnot : ¬ LocalForStriation Gx S T (attachments Gx F' (striationVertices S T))) :
    F' = F := by
  apply Set.eq_of_subset_of_ncard_le hsub _ (Set.toFinite F)
  by_contra hcard
  exact hnot (hmin F' hsub (by omega)
    ⟨fun v hv => hF.1 (hsub hv), hconn, fun v hv => hF.2.2 v (hsub hv)⟩)

/-- PAPER (9.5(1)): "there is an odd path in F with vertices f₁,...,fₖ ...
Hence the set of attachments of {f₁,...,fₖ} is not local ... and so F = {f₁,...,fₖ}
from the minimality of F." This is the first consequence of 9.3.3, before splitting
the antistrips into offspring. -/
theorem no_strip_attachment_path {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {F : Set V}
    (hs : Setup Gx S T) (hF : Cand Gx S T F) (hmin : Minimal Gx S T F)
    (hno : ∀ i, Anticomplete Gx F (stripVertices (S i)))
    {j : Fin n} {Q : List V} (hQ : IsSRung Gxᶜ (T j) Q)
    (hQall : ∀ v ∈ Q, v ∈ attachments Gx F (striationVertices S T)) :
    ∃ R : List V, ∃ r s : V, IsPathFrom Gx R r s ∧ Odd (pathLength R) ∧
      {v : V | v ∈ R} = F := by
  have hL := hs.2.2.2.2.1
  have hm : 2 ≤ m := hL.2.2.2.2.2.2.2.1
  let i : Fin m := ⟨0, by omega⟩
  obtain ⟨i', j', hii', hjj', htw⟩ := exists_twist_through hL i j
  obtain ⟨P₀, hP₀⟩ := exists_rung (hL.1 i)
  obtain ⟨P₀', hP₀'⟩ := exists_rung (hL.1 i')
  obtain ⟨Q₀', hQ₀'⟩ := exists_rung (hL.2.1 j')
  obtain ⟨P₁, P₂, Q₁, Q₂, eP₁, eP₂, eQ₁, eQ₂, hknot⟩ :=
    KnotFromTwist.exists_knot_of_twist hL hii' hjj' htw hP₀ hP₀' hQ hQ₀'
  have mP₁ := mem_iff_of_eq_or_reverse eP₁
  have mP₂ := mem_iff_of_eq_or_reverse eP₂
  have mQ₁ := mem_iff_of_eq_or_reverse eQ₁
  have mQ₂ := mem_iff_of_eq_or_reverse eQ₂
  have hP₁S : ∀ v ∈ P₁, v ∈ stripVertices (S i) := fun v hv =>
    KnotFromTwist.mem_stripVertices_of_isSRung hP₀ ((mP₁ v).mp hv)
  have hP₂S : ∀ v ∈ P₂, v ∈ stripVertices (S i') := fun v hv =>
    KnotFromTwist.mem_stripVertices_of_isSRung hP₀' ((mP₂ v).mp hv)
  have hQ₁L : ∀ v ∈ Q₁, v ∈ striationVertices S T := fun v hv =>
    StriationCompl.mem_striationVertices_of_isSRung' hQ ((mQ₁ v).mp hv)
  have hQ₂L : ∀ v ∈ Q₂, v ∈ striationVertices S T := fun v hv =>
    StriationCompl.mem_striationVertices_of_isSRung' hQ₀' ((mQ₂ v).mp hv)
  let K : Set V := {v | v ∈ P₁} ∪ {v | v ∈ P₂} ∪ {v | v ∈ Q₁} ∪ {v | v ∈ Q₂}
  have hKL : K ⊆ striationVertices S T := by
    intro v hv
    rcases hv with ((hv | hv) | hv) | hv
    · exact StriationCompl.stripVertices_S_subset S T i (hP₁S v hv)
    · exact StriationCompl.stripVertices_S_subset S T i' (hP₂S v hv)
    · exact hQ₁L v hv
    · exact hQ₂L v hv
  have hnl : ¬ LocalForKnot Gx P₁ P₂ Q₁ Q₂ (attachments Gx F K) := by
    intro hloc
    apply hloc.2.1
    intro v hv
    exact ⟨Or.inl (Or.inr hv), (hQall v ((mQ₁ v).mp hv)).2⟩
  obtain ⟨a₁, b₁, a₂, b₂, x₁, y₁, x₂, y₂, hp₁, hp₂, hq₁, hq₂,
    d12, d1q1, d1q2, d2q1, d2q2, dqq, l1, l2, l3, l4, hantiP, hcompQ,
    E11, E12, E21, E22, N11, N12, N21, N22⟩ := id hknot
  have ha₁P := PathBasics.head_mem hp₁.2.1
  have hb₁P := PathBasics.getLast_mem hp₁.2.2
  have ha₂P := PathBasics.head_mem hp₂.2.1
  have hb₂P := PathBasics.getLast_mem hp₂.2.2
  have hx₁Q := PathBasics.head_mem hq₁.2.1
  have hy₁Q := PathBasics.getLast_mem hq₁.2.2
  have hx₂Q := PathBasics.head_mem hq₂.2.1
  have hy₂Q := PathBasics.getLast_mem hq₂.2.2
  have hab₁ := PathBasics.isPathFrom_ends_ne hp₁ l1
  have hab₂ := PathBasics.isPathFrom_ends_ne hp₂ l2
  have hxy₁ := PathBasics.isPathFrom_ends_ne hq₁ l3
  have hxy₂ := PathBasics.isPathFrom_ends_ne hq₂ l4
  have hno₁ : ∀ f ∈ F, ∀ v ∈ P₁, ¬ Gx.Adj f v :=
    fun f hf v hv => hno i f hf v (hP₁S v hv)
  have hno₂ : ∀ f ∈ F, ∀ v ∈ P₂, ¬ Gx.Adj f v :=
    fun f hf v hv => hno i' f hf v (hP₂S v hv)
  rcases Workspace.Statements.S09.SPGT.thm_9_3 Gx hs.1 P₁ P₂ Q₁ Q₂
      a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hp₁ hp₂ hq₁ hq₂ K rfl hs.2.1 hs.2.2.1
      hs.2.2.2.1 F (fun f hf hfk => hF.1 hf (hKL hfk)) hF.2.1 hnl with
    h1 | h2 | h3 | h4
  · obtain ⟨f, hf, hres⟩ := h1
    obtain ⟨v, hvN, hvP⟩ := hres.2.1
    exact (hno₁ f hf v hvP hvN.1).elim
  · obtain ⟨a, P, P', hcase, R, r, s, hR, hRF, _, _, hattach, _⟩ := h2
    obtain ⟨w, hw, hsw⟩ := hattach
    have hsF := hRF s (PathBasics.getLast_mem hR.2.2)
    rcases hcase with h | h | h | h <;> simp only [Prod.mk.injEq] at h
    · exact (hno₁ s hsF w (h.2.1 ▸ hw.1) hsw).elim
    · exact (hno₁ s hsF w (h.2.1 ▸ hw.1) hsw).elim
    · exact (hno₂ s hsF w (h.2.1 ▸ hw.1) hsw).elim
    · exact (hno₂ s hsF w (h.2.1 ▸ hw.1) hsw).elim
  · obtain ⟨a, b, P, P', hcase, R, r, s, hR, hRF, hodd, hcopyR, hcopyS, _, _⟩ := h3
    have hcover : ∀ v ∈ Q₁, Gx.Adj v a ∨ Gx.Adj v b := by
      rcases hcase with h | h | h | h <;> simp only [Prod.mk.injEq] at h
      · rw [h.1, h.2.1]; exact cover_ends hab₁ hxy₁ N11
      · rw [h.1, h.2.1]; exact cover_ends hab₁.symm hxy₁.symm (swap_N N11)
      · rw [h.1, h.2.1]; exact cover_ends hab₂ hxy₁ N21
      · rw [h.1, h.2.1]; exact cover_ends hab₂.symm hxy₁.symm (swap_N N21)
    have hRall : ∀ v ∈ Q, v ∈ attachments Gx {v | v ∈ R} (striationVertices S T) := by
      intro v hv
      have hvQ := (mQ₁ v).mpr hv
      refine ⟨hQ₁L v hvQ, ?_⟩
      rcases hcover v hvQ with hadj | hadj
      · exact ⟨r, PathBasics.head_mem hR.2.1,
          ((hcopyR v (Or.inl (Or.inr hvQ))).mpr hadj.symm).symm⟩
      · exact ⟨s, PathBasics.getLast_mem hR.2.2,
          ((hcopyS v (Or.inl (Or.inr hvQ))).mpr hadj.symm).symm⟩
    refine ⟨R, r, s, hR, hodd, minimal_eq_of_nonlocal_subset hF hmin hRF
      (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hR.1) ?_⟩
    intro hloc
    obtain ⟨v, hv, hvnot⟩ := hloc.2.1 j Q hQ
    exact hvnot (hRall v hv)
  · obtain ⟨x, y, Q', hcase, f, hf, hcopy, _⟩ := h4
    have step (v : V) (hv : v ∈ P₁) (hadj : Gx.Adj x v) : False :=
      hno₁ f hf v hv ((hcopy v (Or.inl (Or.inl hv))).mpr hadj)
    rcases hcase with h | h | h | h <;> simp only [Prod.mk.injEq] at h
    · exact (step a₁ ha₁P (by rw [h.1]; exact adj_end hab₁ hxy₁ hx₁Q N11)).elim
    · exact (step b₁ hb₁P (by rw [h.1]; exact adj_end hab₁.symm hxy₁.symm hy₁Q (swap_N N11))).elim
    · exact (step a₁ ha₁P (by rw [h.1]; exact adj_end hab₁ hxy₂ hx₂Q N12)).elim
    · exact (step b₁ hb₁P (by rw [h.1]; exact adj_end hab₁.symm hxy₂.symm hy₂Q (swap_N N12))).elim

/-- **Labelled gap: the offspring step in 9.5(1), after the odd path has been proved.**

PAPER: "Now if Mⱼ is nonempty, then (Mⱼ ∩ Xⱼ, Mⱼ ∩ Zⱼ, Mⱼ ∩ Yⱼ) is an
antistrip, and similarly if Nⱼ is nonempty it also induces an antistrip. We call these
the offspring of Tⱼ." The final sentence says the old strips, the new path strip,
and these offspring "forms a new striation". If the new strip agrees everywhere with
an old strip (up to reversal), the preceding bullet instead adds the path to that strip.

In either case the new vertex set is exactly V(L) ∪ F. Repetition of 9.3 over the
antirungs and the offspring construction remain here. The path reduction and the
strict-inclusion contradiction are proved outside this lemma. -/
theorem claim1_offspring_enlargement_gap {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {F : Set V}
    (hs : Setup Gx S T) (hF : Cand Gx S T F) (hmin : Minimal Gx S T F)
    (hno : ∀ i, Anticomplete Gx F (stripVertices (S i)))
    {j : Fin n} {Q R : List V} {r s : V}
    (hQ : IsSRung Gxᶜ (T j) Q)
    (hQall : ∀ v ∈ Q, v ∈ attachments Gx F (striationVertices S T))
    (hR : IsPathFrom Gx R r s) (hodd : Odd (pathLength R))
    (hRF : {v : V | v ∈ R} = F) :
    ∃ (m' n' : ℕ) (S' : Fin m' → Set V × Set V × Set V)
      (T' : Fin n' → Set V × Set V × Set V), IsStriation Gx S' T' ∧
      striationVertices S' T' = striationVertices S T ∪ F :=
  Thm95Offspring.claim1_enlargement hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 hF.1 hF.2.1
    (fun F' h1 h2 h3 => minimal_eq_of_nonlocal_subset hF hmin h1 h2 h3) hno hQ
    (fun v hv => (hQall v hv).2)

/-- **Remaining gap from 9.5, Claim (1), used in Claim (3).**

PAPER: *"(1) `X` is not a subset of `V(T₁) ∪ ⋯ ∪ V(T_n)`."*

Here a whole antirung is already in `X`, so the only consequence needed later is that `X`
also meets some strip. -/
theorem claim3_has_strip_attachment_gap {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {F : Set V}
    (hs : Setup Gx S T) (hF : Cand Gx S T F) (hmin : Minimal Gx S T F)
    (hnot : ¬ LocalForStriation Gx S T (attachments Gx F (striationVertices S T)))
    {j : Fin n} {Q : List V} (hQ : IsSRung Gxᶜ (T j) Q)
    (hQall : ∀ v ∈ Q, v ∈ attachments Gx F (striationVertices S T)) :
    ∃ i : Fin m,
      (attachments Gx F (striationVertices S T) ∩ stripVertices (S i)).Nonempty := by
  by_contra hhit
  have hno : ∀ i, Anticomplete Gx F (stripVertices (S i)) := by
    intro i f hf v hv hadj
    exact hhit ⟨i, v, ⟨StriationCompl.stripVertices_S_subset S T i hv,
      f, hf, hadj.symm⟩, hv⟩
  obtain ⟨R, r, s, hR, hodd, hRF⟩ := no_strip_attachment_path hs hF hmin hno hQ hQall
  obtain ⟨m', n', S', T', hL', hvertices⟩ :=
    claim1_offspring_enlargement_gap hs hF hmin hno hQ hQall hR hodd hRF
  have hrF : r ∈ F := hRF ▸ PathBasics.head_mem hR.2.1
  apply hs.2.2.2.2.2 ⟨m', n', S', T', hL', ?_⟩
  rw [hvertices]
  exact ⟨Set.subset_union_left, fun hback => hF.1 hrF (hback (Or.inr hrF))⟩

/-- Claim (2) makes F anticomplete to every strip other than the one it meets. -/
theorem anticomplete_other_strips {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {F : Set V}
    (hone : ∀ i i' : Fin m,
      (attachments Gx F (striationVertices S T) ∩ stripVertices (S i)).Nonempty →
      (attachments Gx F (striationVertices S T) ∩ stripVertices (S i')).Nonempty → i = i')
    {i : Fin m}
    (hi : (attachments Gx F (striationVertices S T) ∩ stripVertices (S i)).Nonempty) :
    ∀ k, k ≠ i → Anticomplete Gx F (stripVertices (S k)) := by
  intro k hki f hf v hv hadj
  exact hki (hone k i
    ⟨v, ⟨StriationCompl.stripVertices_S_subset S T k hv, f, hf, hadj.symm⟩, hv⟩ hi)

/-- **Labelled gap: repeating 9.3.3 over all antirungs in 9.5(3).**

PAPER: "Since this holds for all choices of Qⱼ and of j, it follows that f₁, a₁
have the same neighbours in V(T₁) ∪ ... ∪ V(Tₙ), and so do fₖ, b₁."
The preceding sentences give the odd path with vertex set F and say that its interior
is anticomplete to this union. The path is oriented so that a₁ belongs to Aᵢ.

Only these neighbourhood and path facts remain here. The enlarged strip, its rung
coverage, the parity of every new rung, and the maximality contradiction are proved
in Thm95StripExtension. -/
theorem claim3_global_path_gap {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {F : Set V}
    (hs : Setup Gx S T) (hF : Cand Gx S T F) (hmin : Minimal Gx S T F)
    (hone : ∀ i i' : Fin m,
      (attachments Gx F (striationVertices S T) ∩ stripVertices (S i)).Nonempty →
      (attachments Gx F (striationVertices S T) ∩ stripVertices (S i')).Nonempty → i = i')
    {i : Fin m} {j : Fin n} {Q : List V}
    (hi : (attachments Gx F (striationVertices S T) ∩ stripVertices (S i)).Nonempty)
    (hQ : IsSRung Gxᶜ (T j) Q)
    (hQall : ∀ v ∈ Q, v ∈ attachments Gx F (striationVertices S T)) :
    ∃ (R : List V) (r s a b : V), IsPathFrom Gx R r s ∧ Odd (pathLength R) ∧
      {v : V | v ∈ R} = F ∧ a ∈ (S i).1 ∧ b ∈ (S i).2.2 ∧
      (∀ j w, w ∈ stripVertices (T j) → (Gx.Adj r w ↔ Gx.Adj a w)) ∧
      (∀ j w, w ∈ stripVertices (T j) → (Gx.Adj s w ↔ Gx.Adj b w)) ∧
      (∀ j, Anticomplete Gx {v | v ∈ SPGT.interior R} (stripVertices (T j))) := by
  exact Thm95Claim3Propagate.claim3_global hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1
    hs.2.2.2.2.1 hF.1 hF.2.1
    (fun F' h1 h2 h3 => minimal_eq_of_nonlocal_subset hF hmin h1 h2 h3) hone hi hQ hQall

/-- **Remaining gap in 9.5, Claim (3).**

PAPER: *"By (2) and the minimality of `F` it follows that 9.3.3 holds.  This has several
consequences. ... Hence we can add `f₁` to `A₁`, `{f₂,…,f_{k-1}}` to `C₁` and `f_k` to
`B₁`, contrary to the maximality of the striation."*

The hypotheses below retain the chosen twist, all four oriented (anti)rungs, and the exact
9.3.3 alternative.  Thus the gap is only the printed repetition over the other antistrips and
the final construction of the enlarged striation. -/
theorem claim3_outcome3_maximality_gap {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {F : Set V}
    (hs : Setup Gx S T) (hF : Cand Gx S T F) (hmin : Minimal Gx S T F)
    (hone : ∀ i i' : Fin m,
      (attachments Gx F (striationVertices S T) ∩ stripVertices (S i)).Nonempty →
      (attachments Gx F (striationVertices S T) ∩ stripVertices (S i')).Nonempty → i = i')
    {i i' : Fin m} {j j' : Fin n} (hii' : i ≠ i') (hjj' : j ≠ j')
    {P₀ P₀' Q₀ Q₀' P₁ P₂ Q₁ Q₂ : List V}
    (hP₀ : IsSRung Gx (S i) P₀) (hP₀' : IsSRung Gx (S i') P₀')
    (hQ₀ : IsSRung Gxᶜ (T j) Q₀) (hQ₀' : IsSRung Gxᶜ (T j') Q₀')
    (mP₁ : ∀ v : V, v ∈ P₁ ↔ v ∈ P₀) (mP₂ : ∀ v : V, v ∈ P₂ ↔ v ∈ P₀')
    (mQ₁ : ∀ v : V, v ∈ Q₁ ↔ v ∈ Q₀) (mQ₂ : ∀ v : V, v ∈ Q₂ ↔ v ∈ Q₀')
    (hi : (attachments Gx F (striationVertices S T) ∩ stripVertices (S i)).Nonempty)
    (hQall : ∀ v ∈ Q₀, v ∈ attachments Gx F (striationVertices S T))
    {a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V}
    (hknot : IsKnot Gx P₁ P₂ Q₁ Q₂)
    (hp₁ : IsPathFrom Gx P₁ a₁ b₁) (hp₂ : IsPathFrom Gx P₂ a₂ b₂)
    (hq₁ : IsPathFrom Gxᶜ Q₁ x₁ y₁) (hq₂ : IsPathFrom Gxᶜ Q₂ x₂ y₂)
    (hout : Outcome3ForKnot Gx P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ F) : False := by
  obtain ⟨R, r, s, a, b, hR, hodd, hRF, ha, hb, hra, hsb, hantiT⟩ :=
    claim3_global_path_gap hs hF hmin hone hi hQ₀ hQall
  have hrs : r ≠ s := PathBasics.isPathFrom_ends_ne hR (by
    obtain ⟨k, hk⟩ := hodd
    omega)
  exact Thm95StripExtension.two_end_absurd hs.1 hs.2.2.2.2 hF.1 i
    (anticomplete_other_strips hone hi) hR hrs (fun v hv => hRF ▸ hv) ha hb hra hsb hantiT

theorem claim3 {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {F : Set V}
    (hs : Setup Gx S T) (hF : Cand Gx S T F) (hmin : Minimal Gx S T F)
    (hnot : ¬ LocalForStriation Gx S T (attachments Gx F (striationVertices S T)))
    (j : Fin n) (Q : List V) (hQ : IsSRung Gxᶜ (T j) Q) :
    ∃ v ∈ Q, v ∉ attachments Gx F (striationVertices S T) := by
  by_contra hcon
  push Not at hcon
  have hs0 := hs
  obtain ⟨hberge, hnoenl, hnoover, hnoovercompl, hmax⟩ := hs0
  have hL : IsStriation Gx S T := hmax.1
  have hone : ∀ i i' : Fin m,
      (attachments Gx F (striationVertices S T) ∩ stripVertices (S i)).Nonempty →
      (attachments Gx F (striationVertices S T) ∩ stripVertices (S i')).Nonempty → i = i' :=
    fun i i' hi hi' => claim2 hs hF hmin hnot i i' hi hi'
  obtain ⟨i, hi⟩ := claim3_has_strip_attachment_gap hs hF hmin hnot hQ hcon
  obtain ⟨i', j', hii', hjj', htwist⟩ := exists_twist_through hL i j
  obtain ⟨u, huX, huS⟩ := hi
  obtain ⟨P₀, hP₀, huP⟩ := exists_rung_through (hL.1 i) huS
  obtain ⟨P₀', hP₀'⟩ := exists_rung (hL.1 i')
  obtain ⟨Q₀', hQ₀'⟩ := exists_rung (hL.2.1 j')
  obtain ⟨P₁, P₂, Q₁, Q₂, eP₁, eP₂, eQ₁, eQ₂, hknot⟩ :=
    KnotFromTwist.exists_knot_of_twist hL hii' hjj' htwist hP₀ hP₀' hQ hQ₀'
  have mP₁ : ∀ v : V, v ∈ P₁ ↔ v ∈ P₀ := mem_iff_of_eq_or_reverse eP₁
  have mP₂ : ∀ v : V, v ∈ P₂ ↔ v ∈ P₀' := mem_iff_of_eq_or_reverse eP₂
  have mQ₁ : ∀ v : V, v ∈ Q₁ ↔ v ∈ Q := mem_iff_of_eq_or_reverse eQ₁
  have mQ₂ : ∀ v : V, v ∈ Q₂ ↔ v ∈ Q₀' := mem_iff_of_eq_or_reverse eQ₂
  have hSmemP₁ : ∀ v ∈ P₁, v ∈ (⋃ k : Fin m, stripVertices (S k)) := fun v hv =>
    Set.mem_iUnion.mpr ⟨i, KnotFromTwist.mem_stripVertices_of_isSRung hP₀ ((mP₁ v).mp hv)⟩
  have hSmemP₂ : ∀ v ∈ P₂, v ∈ (⋃ k : Fin m, stripVertices (S k)) := fun v hv =>
    Set.mem_iUnion.mpr ⟨i', KnotFromTwist.mem_stripVertices_of_isSRung hP₀' ((mP₂ v).mp hv)⟩
  have hTmemQ₁ : ∀ v ∈ Q₁, v ∈ (⋃ k : Fin n, stripVertices (T k)) := fun v hv =>
    Set.mem_iUnion.mpr ⟨j, KnotFromTwist.mem_stripVertices_of_isSRung hQ ((mQ₁ v).mp hv)⟩
  have hTmemQ₂ : ∀ v ∈ Q₂, v ∈ (⋃ k : Fin n, stripVertices (T k)) := fun v hv =>
    Set.mem_iUnion.mpr ⟨j', KnotFromTwist.mem_stripVertices_of_isSRung hQ₀' ((mQ₂ v).mp hv)⟩
  have hVP₁ : ∀ v ∈ P₁, v ∈ striationVertices S T := fun v hv =>
    Set.mem_union_left _ (hSmemP₁ v hv)
  have hVP₂ : ∀ v ∈ P₂, v ∈ striationVertices S T := fun v hv =>
    Set.mem_union_left _ (hSmemP₂ v hv)
  have hVQ₁ : ∀ v ∈ Q₁, v ∈ striationVertices S T := fun v hv =>
    Set.mem_union_right _ (hTmemQ₁ v hv)
  have hVQ₂ : ∀ v ∈ Q₂, v ∈ striationVertices S T := fun v hv =>
    Set.mem_union_right _ (hTmemQ₂ v hv)
  have hFK : F ⊆ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪
      {v : V | v ∈ Q₂})ᶜ := by
    intro f hf hfK
    refine hF.1 hf ?_
    rcases hfK with ((hv | hv) | hv) | hv
    · exact hVP₁ f hv
    · exact hVP₂ f hv
    · exact hVQ₁ f hv
    · exact hVQ₂ f hv
  have hQ₁att : ∀ v ∈ Q₁,
      v ∈ attachments Gx F
        ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪
          {v : V | v ∈ Q₂}) := by
    intro v hv
    obtain ⟨-, f, hfF, hvf⟩ := hcon v ((mQ₁ v).mp hv)
    exact ⟨Or.inl (Or.inr hv), f, hfF, hvf⟩
  have hnl : ¬ LocalForKnot Gx P₁ P₂ Q₁ Q₂
      (attachments Gx F
        ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪
          {v : V | v ∈ Q₂})) := by
    rintro ⟨-, hnQ₁, -, -⟩
    exact hnQ₁ hQ₁att
  obtain ⟨a₁, b₁, a₂, b₂, x₁, y₁, x₂, y₂, hp₁, hp₂, hq₁, hq₂,
    d12, d1q1, d1q2, d2q1, d2q2, dqq, l1, l2, l3, l4, hantiP, hcompQ,
    E11, E12, E21, E22, N11, N12, N21, N22⟩ := id hknot
  obtain ⟨ha₁P, hb₁P⟩ := PathBasics.isPathFrom_ends_mem hp₁
  obtain ⟨ha₂P, hb₂P⟩ := PathBasics.isPathFrom_ends_mem hp₂
  obtain ⟨hx₁Q, hy₁Q⟩ := PathBasics.isPathFrom_ends_mem hq₁
  obtain ⟨hx₂Q, hy₂Q⟩ := PathBasics.isPathFrom_ends_mem hq₂
  have hab₁ : a₁ ≠ b₁ := PathBasics.isPathFrom_ends_ne hp₁ l1
  have hab₂ : a₂ ≠ b₂ := PathBasics.isPathFrom_ends_ne hp₂ l2
  have hxy₁ : x₁ ≠ y₁ := PathBasics.isPathFrom_ends_ne hq₁ l3
  have hxy₂ : x₂ ≠ y₂ := PathBasics.isPathFrom_ends_ne hq₂ l4
  have ax1a1 : Gx.Adj x₁ a₁ := adj_end hab₁ hxy₁ hx₁Q N11
  have ay1b1 : Gx.Adj y₁ b₁ := adj_end hab₁.symm hxy₁.symm hy₁Q (swap_N N11)
  have ax1a2 : Gx.Adj x₁ a₂ := adj_end hab₂ hxy₁ hx₁Q N21
  have ay1b2 : Gx.Adj y₁ b₂ := adj_end hab₂.symm hxy₁.symm hy₁Q (swap_N N21)
  have ax2a1 : Gx.Adj x₂ a₁ := adj_end hab₁ hxy₂ hx₂Q N12
  have ay2b1 : Gx.Adj y₂ b₁ := adj_end hab₁.symm hxy₂.symm hy₂Q (swap_N N12)
  have ay2a2 : Gx.Adj y₂ a₂ := adj_end hab₂ hxy₂.symm hy₂Q N22
  have ax2b2 : Gx.Adj x₂ b₂ := adj_end hab₂.symm hxy₂ hx₂Q (swap_N N22)
  have key : ∀ f ∈ F, ∀ v ∈ P₁, ∀ w ∈ P₂,
      Gx.Adj f v → Gx.Adj f w → False := by
    intro f hf v hv w hw hfv hfw
    exact hii' ((hF.2.2 f hf).1 i i'
      ⟨v, ⟨hfv, hVP₁ v hv⟩,
        KnotFromTwist.mem_stripVertices_of_isSRung hP₀ ((mP₁ v).mp hv)⟩
      ⟨w, ⟨hfw, hVP₂ w hw⟩,
        KnotFromTwist.mem_stripVertices_of_isSRung hP₀' ((mP₂ w).mp hw)⟩)
  have out2 : ∀ (a c d : V) (P P' R : List V) (r₁ r₂ : V),
      a ∈ P → c ∈ Q₁ → d ∈ Q₁ → Gx.Adj a c → ¬ Gx.Adj a d →
      (∀ z ∈ P, z ≠ a → ¬ Gx.Adj z c) →
      (∀ z ∈ P, z ∈ ⋃ k : Fin m, stripVertices (S k)) →
      IsPathFrom Gx R r₁ r₂ → (∀ z ∈ R, z ∈ F) →
      (∀ z ∈ ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
        (Gx.Adj r₁ z ↔ Gx.Adj a z)) →
      Anticomplete Gx ({v : V | v ∈ R} \ {r₁})
        ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}) →
      (∃ z ∈ ({v : V | v ∈ P} \ {a} : Set V), Gx.Adj r₂ z) → False := by
    intro a c d P P' R r₁ r₂ haP hcQ hdQ hac hnad honly hPS hR hRF hcopy hantic hwit
    obtain ⟨w, ⟨hwP, hwa⟩, hr₂w⟩ := hwit
    obtain ⟨hr₁R, hr₂R⟩ := PathBasics.isPathFrom_ends_mem hR
    let Rset : Set V := {z : V | z ∈ R}
    have hRsub : Rset ⊆ F := hRF
    have hRcand : Cand Gx S T Rset :=
      ⟨fun z hz => hF.1 (hRF z hz),
        InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hR.1,
        fun z hz => hF.2.2 z (hRF z hz)⟩
    have hcatt : c ∈ attachments Gx Rset (striationVertices S T) :=
      ⟨hVQ₁ c hcQ, r₁, hr₁R, ((hcopy c (Or.inl (Or.inr hcQ))).mpr hac).symm⟩
    have hwatt : w ∈ attachments Gx Rset (striationVertices S T) :=
      ⟨Set.mem_union_left _ (hPS w hwP), r₂, hr₂R, hr₂w.symm⟩
    have hRnl : ¬ LocalForStriation Gx S T
        (attachments Gx Rset (striationVertices S T)) := by
      rintro ⟨-, -, hcomplete⟩
      exact honly w hwP hwa
        (hcomplete w ⟨hwatt, hPS w hwP⟩ c ⟨hcatt, hTmemQ₁ c hcQ⟩)
    have hnlt : ¬ Rset.ncard < F.ncard := fun hlt => hRnl (hmin Rset hRsub hlt hRcand)
    have heq : Rset = F :=
      Set.eq_of_subset_of_ncard_le hRsub (not_lt.mp hnlt) (Set.toFinite F)
    obtain ⟨-, f, hfF, hdf⟩ := hcon d ((mQ₁ d).mp hdQ)
    have hfR : f ∈ R := by
      change f ∈ Rset
      rw [heq]
      exact hfF
    have hfr₁ : f = r₁ := by
      by_contra hne
      exact hantic f ⟨hfR, hne⟩ d (Or.inl (Or.inr hdQ)) hdf.symm
    have hr₁d : Gx.Adj r₁ d := by rw [← hfr₁]; exact hdf.symm
    exact hnad ((hcopy d (Or.inl (Or.inr hdQ))).mp hr₁d)
  have h93 := _root_.Workspace.Statements.S09.SPGT.thm_9_3 Gx hberge P₁ P₂ Q₁ Q₂
    a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hp₁ hp₂ hq₁ hq₂
    ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪
      {v : V | v ∈ Q₂}) rfl hnoenl hnoover hnoovercompl F hFK hF.2.1 hnl
  rcases h93 with h1 | h2 | h3 | h4
  · obtain ⟨f, hfF, -, ⟨v, ⟨hfv, -⟩, hvP⟩, ⟨w, ⟨hfw, -⟩, hwP⟩, -⟩ := h1
    exact key f hfF v hvP w hwP hfv hfw
  · obtain ⟨a, P, P', hcase, R, r₁, r₂, hR, hRF, hcopy, hantic, hwit, -⟩ := h2
    rcases hcase with h | h | h | h <;> simp only [Prod.mk.injEq] at h
    · exact out2 a x₁ y₁ P P' R r₁ r₂
        (by rw [h.1, h.2.1]; exact ha₁P) hx₁Q hy₁Q
        (by rw [h.1]; exact ax1a1.symm)
        (by rw [h.1]; exact fun hadj =>
          ((N11 y₁ hy₁Q a₁ (Set.mem_insert _ _)).mpr (Or.inl ⟨rfl, rfl⟩)) hadj.symm)
        (by rw [h.1, h.2.1]; exact edge_end hxy₁ E11)
        (by rw [h.2.1]; exact hSmemP₁) hR hRF hcopy hantic hwit
    · exact out2 a y₁ x₁ P P' R r₁ r₂
        (by rw [h.1, h.2.1]; exact hb₁P) hy₁Q hx₁Q
        (by rw [h.1]; exact ay1b1.symm)
        (by rw [h.1]; exact fun hadj =>
          ((N11 x₁ hx₁Q b₁ (Set.mem_insert_of_mem _ rfl)).mpr
            (Or.inr ⟨rfl, rfl⟩)) hadj.symm)
        (by rw [h.1, h.2.1]; exact edge_end hxy₁.symm (swap_E E11))
        (by rw [h.2.1]; exact hSmemP₁) hR hRF hcopy hantic hwit
    · exact out2 a x₁ y₁ P P' R r₁ r₂
        (by rw [h.1, h.2.1]; exact ha₂P) hx₁Q hy₁Q
        (by rw [h.1]; exact ax1a2.symm)
        (by rw [h.1]; exact fun hadj =>
          ((N21 y₁ hy₁Q a₂ (Set.mem_insert _ _)).mpr (Or.inl ⟨rfl, rfl⟩)) hadj.symm)
        (by rw [h.1, h.2.1]; exact edge_end hxy₁ E21)
        (by rw [h.2.1]; exact hSmemP₂) hR hRF hcopy hantic hwit
    · exact out2 a y₁ x₁ P P' R r₁ r₂
        (by rw [h.1, h.2.1]; exact hb₂P) hy₁Q hx₁Q
        (by rw [h.1]; exact ay1b2.symm)
        (by rw [h.1]; exact fun hadj =>
          ((N21 x₁ hx₁Q b₂ (Set.mem_insert_of_mem _ rfl)).mpr
            (Or.inr ⟨rfl, rfl⟩)) hadj.symm)
        (by rw [h.1, h.2.1]; exact edge_end hxy₁.symm (swap_E E21))
        (by rw [h.2.1]; exact hSmemP₂) hR hRF hcopy hantic hwit
  · apply claim3_outcome3_maximality_gap hs hF hmin hone hii' hjj'
      hP₀ hP₀' hQ hQ₀' mP₁ mP₂ mQ₁ mQ₂ ⟨u, huX, huS⟩ hcon hknot hp₁ hp₂ hq₁ hq₂
    exact h3
  · obtain ⟨x, y, Q', hcase, f, hfF, hcopy, -⟩ := h4
    have step : ∀ v ∈ P₁, ∀ w ∈ P₂, Gx.Adj x v → Gx.Adj x w → False := by
      intro v hv w hw hxv hxw
      exact key f hfF v hv w hw
        ((hcopy v (Or.inl (Or.inl hv))).mpr hxv)
        ((hcopy w (Or.inl (Or.inr hw))).mpr hxw)
    rcases hcase with h | h | h | h <;> simp only [Prod.mk.injEq] at h
    · exact step a₁ ha₁P a₂ ha₂P (by rw [h.1]; exact ax1a1) (by rw [h.1]; exact ax1a2)
    · exact step b₁ hb₁P b₂ hb₂P (by rw [h.1]; exact ay1b1) (by rw [h.1]; exact ay1b2)
    · exact step a₁ ha₁P b₂ hb₂P (by rw [h.1]; exact ax2a1) (by rw [h.1]; exact ax2b2)
    · exact step b₁ hb₁P a₂ ha₂P (by rw [h.1]; exact ay2b1) (by rw [h.1]; exact ay2a2)

/-! ### The closing paragraph -/

/-- The second alternative of 9.3, named for the final reduction in the proof of 9.5. -/
def Outcome2ForKnot (Gx : SimpleGraph V) (P₁ P₂ Q₁ Q₂ : List V)
    (a₁ b₁ a₂ b₂ : V) (F : Set V) : Prop :=
  ∃ (a : V) (P P' : List V),
    ((a, P, P') = (a₁, P₁, P₂) ∨ (a, P, P') = (b₁, P₁, P₂) ∨
      (a, P, P') = (a₂, P₂, P₁) ∨ (a, P, P') = (b₂, P₂, P₁)) ∧
    ∃ (R : List V) (r₁ r₂ : V),
      IsPathFrom Gx R r₁ r₂ ∧ (∀ v ∈ R, v ∈ F) ∧
      (∀ w ∈ ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
        (Gx.Adj r₁ w ↔ Gx.Adj a w)) ∧
      Anticomplete Gx ({v : V | v ∈ R} \ {r₁})
        ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}) ∧
      (∃ w ∈ ({v : V | v ∈ P} \ {a} : Set V), Gx.Adj r₂ w) ∧
      Anticomplete Gx ({v : V | v ∈ R} \ {r₂}) ({v : V | v ∈ P} \ {a})

/-- **Labelled gap: repeating 9.3.2 over all antirungs in the closing paragraph of 9.5.**

PAPER: "For any other choice of Qⱼ the same happens, and f₁, fₖ cannot become
exchanged since f₁ has neighbours in Q₁ and fₖ has none." After exchanging T₁ and Tⱼ,
"it follows that a₁, f₁ have the same neighbours in V(T₁) ∪ ... ∪ V(Tₙ), and there
are no edges between {f₂,...,fₖ} and V(T₁) ∪ ... ∪ V(Tₙ)."

The statement retains the path and its attachment to an old rung from 9.3.2, allowing
the reversal in that outcome. The construction of a covering rung and of the enlarged
striation is proved separately in Thm95OneEndExtension. -/
theorem closing_global_path_gap {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {F : Set V}
    (hs : Setup Gx S T) (hF : Cand Gx S T F) (hmin : Minimal Gx S T F)
    (hone : ∀ i i' : Fin m,
      (attachments Gx F (striationVertices S T) ∩ stripVertices (S i)).Nonempty →
      (attachments Gx F (striationVertices S T) ∩ stripVertices (S i')).Nonempty → i = i')
    (hanti : ∀ (j : Fin n) (Q : List V), IsSRung Gxᶜ (T j) Q →
      ∃ v ∈ Q, v ∉ attachments Gx F (striationVertices S T))
    {i : Fin m} {j : Fin n} {u w : V}
    (hu : u ∈ attachments Gx F (striationVertices S T))
    (hw : w ∈ attachments Gx F (striationVertices S T))
    (huS : u ∈ stripVertices (S i)) (hwT : w ∈ stripVertices (T j))
    (huw : ¬ Gx.Adj u w) :
    ∃ (S₀ : Set V × Set V × Set V) (P R : List V) (a b r s : V),
      (S₀ = S i ∨ S₀ = reverseStrip (S i)) ∧ IsSRung Gx S₀ P ∧
      IsPathFrom Gx P a b ∧ IsPathFrom Gx R r s ∧ {v : V | v ∈ R} = F ∧
      (∃ v ∈ ({v | v ∈ P} \ {a} : Set V), Gx.Adj s v) ∧
      Anticomplete Gx ({v | v ∈ R} \ {s}) ({v | v ∈ P} \ {a}) ∧
      (∀ j w, w ∈ stripVertices (T j) → (Gx.Adj r w ↔ Gx.Adj a w)) ∧
      (∀ j, Anticomplete Gx ({v | v ∈ R} \ {r}) (stripVertices (T j))) := by
  have hanti' : ∀ (k : Fin n) (Qx : List V), IsSRung Gxᶜ (T k) Qx →
      ∃ v ∈ Qx, ¬ ∃ f ∈ F, Gx.Adj v f := by
    intro k Qx hQx
    obtain ⟨v, hv, hvnot⟩ := hanti k Qx hQx
    refine ⟨v, hv, fun hex => hvnot ⟨?_, hex⟩⟩
    exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨k,
      KnotFromTwist.mem_stripVertices_of_isSRung hQx hv⟩)
  exact Thm95ClosingPropagate.closing_global hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1
    hs.2.2.2.2.1 hF.1 hF.2.1
    (fun F' h1 h2 h3 => minimal_eq_of_nonlocal_subset hF hmin h1 h2 h3) hone hanti'
    hu.2 hw.2 huS hwT huw

/-- **Remaining gap in the closing paragraph of 9.5.**

PAPER: *"There is a path with vertex set in `F` satisfying 9.3.2.  From the minimality of
`F`, it follows that this path has vertex set `F` ... But then we can add `f₁` to `A₁` and
`{f₂,…,f_k}` to `C₁`, contrary to the maximality of the striation."*

All work before 9.3.2, including the choice of the twist and the non-local attachment set, is
outside this gap.  The gap contains the printed repetition over all antirungs and the final
enlarged-striation construction. -/
theorem closing_outcome2_maximality_gap {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {F : Set V}
    (hs : Setup Gx S T) (hF : Cand Gx S T F) (hmin : Minimal Gx S T F)
    (hone : ∀ i i' : Fin m,
      (attachments Gx F (striationVertices S T) ∩ stripVertices (S i)).Nonempty →
      (attachments Gx F (striationVertices S T) ∩ stripVertices (S i')).Nonempty → i = i')
    (hanti : ∀ (j : Fin n) (Q : List V), IsSRung Gxᶜ (T j) Q →
      ∃ v ∈ Q, v ∉ attachments Gx F (striationVertices S T))
    {i i' : Fin m} {j j' : Fin n} (hii' : i ≠ i') (hjj' : j ≠ j')
    {P₀ P₀' Q₀ Q₀' P₁ P₂ Q₁ Q₂ : List V}
    (hP₀ : IsSRung Gx (S i) P₀) (hP₀' : IsSRung Gx (S i') P₀')
    (hQ₀ : IsSRung Gxᶜ (T j) Q₀) (hQ₀' : IsSRung Gxᶜ (T j') Q₀')
    (mP₁ : ∀ v : V, v ∈ P₁ ↔ v ∈ P₀) (mP₂ : ∀ v : V, v ∈ P₂ ↔ v ∈ P₀')
    (mQ₁ : ∀ v : V, v ∈ Q₁ ↔ v ∈ Q₀) (mQ₂ : ∀ v : V, v ∈ Q₂ ↔ v ∈ Q₀')
    {u w : V} (hu : u ∈ attachments Gx F (striationVertices S T))
    (hw : w ∈ attachments Gx F (striationVertices S T)) (huP : u ∈ P₀) (hwQ : w ∈ Q₀)
    (huw : ¬ Gx.Adj u w) {W : List V} (hW : IsPathFrom Gx W u w)
    (hW3 : 3 ≤ W.length) (hWF : {z : V | z ∈ SPGT.interior W} = F)
    {a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V}
    (hknot : IsKnot Gx P₁ P₂ Q₁ Q₂)
    (hp₁ : IsPathFrom Gx P₁ a₁ b₁) (hp₂ : IsPathFrom Gx P₂ a₂ b₂)
    (hq₁ : IsPathFrom Gxᶜ Q₁ x₁ y₁) (hq₂ : IsPathFrom Gxᶜ Q₂ x₂ y₂)
    (hout : Outcome2ForKnot Gx P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ F) : False := by
  have huS : u ∈ stripVertices (S i) := KnotFromTwist.mem_stripVertices_of_isSRung hP₀ huP
  have hwT : w ∈ stripVertices (T j) := KnotFromTwist.mem_stripVertices_of_isSRung hQ₀ hwQ
  obtain ⟨S₀, P, R, a, b, r, s, hor, hP, hPend, hR, hRF, hattach, hantiR, hra, hantiT⟩ :=
    closing_global_path_gap hs hF hmin hone hanti hu hw huS hwT huw
  exact Thm95OneEndExtension.one_end_absurd hs.1 hs.2.2.2.2 hF.1 i
    (anticomplete_other_strips hone ⟨u, hu, huS⟩) S₀ hor hP hPend hR
    (fun v hv => hRF ▸ hv) hattach hantiR hra hantiT

theorem closing {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {F : Set V}
    (hs : Setup Gx S T) (hF : Cand Gx S T F) (hmin : Minimal Gx S T F)
    (hnot : ¬ LocalForStriation Gx S T (attachments Gx F (striationVertices S T)))
    (hone : ∀ i i' : Fin m,
      (attachments Gx F (striationVertices S T) ∩ stripVertices (S i)).Nonempty →
      (attachments Gx F (striationVertices S T) ∩ stripVertices (S i')).Nonempty → i = i')
    (hanti : ∀ (j : Fin n) (Q : List V), IsSRung Gxᶜ (T j) Q →
      ∃ v ∈ Q, v ∉ attachments Gx F (striationVertices S T)) :
    Complete Gx
      (attachments Gx F (striationVertices S T) ∩ (⋃ i : Fin m, stripVertices (S i)))
      (attachments Gx F (striationVertices S T) ∩
        (⋃ j : Fin n, stripVertices (T j))) := by
  intro u hu w hw
  by_contra huw
  have hs0 := hs
  obtain ⟨hberge, hnoenl, hnoover, hnoovercompl, hmax⟩ := hs0
  have hL : IsStriation Gx S T := hmax.1
  obtain ⟨W, hW, hW3, hWF⟩ :=
    minimal_path_between_attachments hL hF hmin hu.1 hw.1 hu.2 hw.2 huw
  obtain ⟨i, huS⟩ := Set.mem_iUnion.mp hu.2
  obtain ⟨j, hwT⟩ := Set.mem_iUnion.mp hw.2
  obtain ⟨P₀, hP₀, huP⟩ := exists_rung_through (hL.1 i) huS
  obtain ⟨Q₀, hQ₀, hwQ⟩ := exists_rung_through (hL.2.1 j) hwT
  obtain ⟨i', j', hii', hjj', htwist⟩ := exists_twist_through hL i j
  obtain ⟨P₀', hP₀'⟩ := exists_rung (hL.1 i')
  obtain ⟨Q₀', hQ₀'⟩ := exists_rung (hL.2.1 j')
  obtain ⟨P₁, P₂, Q₁, Q₂, eP₁, eP₂, eQ₁, eQ₂, hknot⟩ :=
    KnotFromTwist.exists_knot_of_twist hL hii' hjj' htwist hP₀ hP₀' hQ₀ hQ₀'
  have mP₁ : ∀ v : V, v ∈ P₁ ↔ v ∈ P₀ := mem_iff_of_eq_or_reverse eP₁
  have mP₂ : ∀ v : V, v ∈ P₂ ↔ v ∈ P₀' := mem_iff_of_eq_or_reverse eP₂
  have mQ₁ : ∀ v : V, v ∈ Q₁ ↔ v ∈ Q₀ := mem_iff_of_eq_or_reverse eQ₁
  have mQ₂ : ∀ v : V, v ∈ Q₂ ↔ v ∈ Q₀' := mem_iff_of_eq_or_reverse eQ₂
  have huP₁ : u ∈ P₁ := (mP₁ u).mpr huP
  have hwQ₁ : w ∈ Q₁ := (mQ₁ w).mpr hwQ
  have hSmemP₁ : ∀ v ∈ P₁, v ∈ (⋃ k : Fin m, stripVertices (S k)) := fun v hv =>
    Set.mem_iUnion.mpr ⟨i, KnotFromTwist.mem_stripVertices_of_isSRung hP₀ ((mP₁ v).mp hv)⟩
  have hSmemP₂ : ∀ v ∈ P₂, v ∈ (⋃ k : Fin m, stripVertices (S k)) := fun v hv =>
    Set.mem_iUnion.mpr ⟨i', KnotFromTwist.mem_stripVertices_of_isSRung hP₀' ((mP₂ v).mp hv)⟩
  have hTmemQ₁ : ∀ v ∈ Q₁, v ∈ (⋃ k : Fin n, stripVertices (T k)) := fun v hv =>
    Set.mem_iUnion.mpr ⟨j, KnotFromTwist.mem_stripVertices_of_isSRung hQ₀ ((mQ₁ v).mp hv)⟩
  have hTmemQ₂ : ∀ v ∈ Q₂, v ∈ (⋃ k : Fin n, stripVertices (T k)) := fun v hv =>
    Set.mem_iUnion.mpr ⟨j', KnotFromTwist.mem_stripVertices_of_isSRung hQ₀' ((mQ₂ v).mp hv)⟩
  have hVP₁ : ∀ v ∈ P₁, v ∈ striationVertices S T := fun v hv =>
    Set.mem_union_left _ (hSmemP₁ v hv)
  have hVP₂ : ∀ v ∈ P₂, v ∈ striationVertices S T := fun v hv =>
    Set.mem_union_left _ (hSmemP₂ v hv)
  have hVQ₁ : ∀ v ∈ Q₁, v ∈ striationVertices S T := fun v hv =>
    Set.mem_union_right _ (hTmemQ₁ v hv)
  have hVQ₂ : ∀ v ∈ Q₂, v ∈ striationVertices S T := fun v hv =>
    Set.mem_union_right _ (hTmemQ₂ v hv)
  have hFK : F ⊆ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪
      {v : V | v ∈ Q₂})ᶜ := by
    intro f hf hfK
    refine hF.1 hf ?_
    rcases hfK with ((hv | hv) | hv) | hv
    · exact hVP₁ f hv
    · exact hVP₂ f hv
    · exact hVQ₁ f hv
    · exact hVQ₂ f hv
  have huK : u ∈ attachments Gx F
      ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪
        {v : V | v ∈ Q₂}) := by
    obtain ⟨-, f, hfF, huf⟩ := hu.1
    exact ⟨Or.inl (Or.inl (Or.inl huP₁)), f, hfF, huf⟩
  have hwK : w ∈ attachments Gx F
      ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪
        {v : V | v ∈ Q₂}) := by
    obtain ⟨-, f, hfF, hwf⟩ := hw.1
    exact ⟨Or.inl (Or.inr hwQ₁), f, hfF, hwf⟩
  have hnl : ¬ LocalForKnot Gx P₁ P₂ Q₁ Q₂
      (attachments Gx F
        ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪
          {v : V | v ∈ Q₂})) := by
    rintro ⟨-, -, -, hcomplete⟩
    exact huw (hcomplete u ⟨huK, Or.inl huP₁⟩ w ⟨hwK, Or.inl hwQ₁⟩)
  obtain ⟨a₁, b₁, a₂, b₂, x₁, y₁, x₂, y₂, hp₁, hp₂, hq₁, hq₂,
    d12, d1q1, d1q2, d2q1, d2q2, dqq, l1, l2, l3, l4, hantiP, hcompQ,
    E11, E12, E21, E22, N11, N12, N21, N22⟩ := id hknot
  obtain ⟨ha₁P, hb₁P⟩ := PathBasics.isPathFrom_ends_mem hp₁
  obtain ⟨ha₂P, hb₂P⟩ := PathBasics.isPathFrom_ends_mem hp₂
  obtain ⟨hx₁Q, hy₁Q⟩ := PathBasics.isPathFrom_ends_mem hq₁
  obtain ⟨hx₂Q, hy₂Q⟩ := PathBasics.isPathFrom_ends_mem hq₂
  have hab₁ : a₁ ≠ b₁ := PathBasics.isPathFrom_ends_ne hp₁ l1
  have hab₂ : a₂ ≠ b₂ := PathBasics.isPathFrom_ends_ne hp₂ l2
  have hxy₁ : x₁ ≠ y₁ := PathBasics.isPathFrom_ends_ne hq₁ l3
  have hxy₂ : x₂ ≠ y₂ := PathBasics.isPathFrom_ends_ne hq₂ l4
  have ax1a1 : Gx.Adj x₁ a₁ := adj_end hab₁ hxy₁ hx₁Q N11
  have ay1b1 : Gx.Adj y₁ b₁ := adj_end hab₁.symm hxy₁.symm hy₁Q (swap_N N11)
  have ax1a2 : Gx.Adj x₁ a₂ := adj_end hab₂ hxy₁ hx₁Q N21
  have ay1b2 : Gx.Adj y₁ b₂ := adj_end hab₂.symm hxy₁.symm hy₁Q (swap_N N21)
  have ax2a1 : Gx.Adj x₂ a₁ := adj_end hab₁ hxy₂ hx₂Q N12
  have ay2b1 : Gx.Adj y₂ b₁ := adj_end hab₁.symm hxy₂.symm hy₂Q (swap_N N12)
  have ay2a2 : Gx.Adj y₂ a₂ := adj_end hab₂ hxy₂.symm hy₂Q N22
  have ax2b2 : Gx.Adj x₂ b₂ := adj_end hab₂.symm hxy₂ hx₂Q (swap_N N22)
  have key : ∀ f ∈ F, ∀ v ∈ P₁, ∀ z ∈ P₂,
      Gx.Adj f v → Gx.Adj f z → False := by
    intro f hf v hv z hz hfv hfz
    exact hii' ((hF.2.2 f hf).1 i i'
      ⟨v, ⟨hfv, hVP₁ v hv⟩,
        KnotFromTwist.mem_stripVertices_of_isSRung hP₀ ((mP₁ v).mp hv)⟩
      ⟨z, ⟨hfz, hVP₂ z hz⟩,
        KnotFromTwist.mem_stripVertices_of_isSRung hP₀' ((mP₂ z).mp hz)⟩)
  have cover₁ : ∀ z ∈ Q₁, Gx.Adj z a₁ ∨ Gx.Adj z b₁ := cover_ends hab₁ hxy₁ N11
  have cover₂ : ∀ z ∈ Q₁, Gx.Adj z a₂ ∨ Gx.Adj z b₂ := cover_ends hab₂ hxy₁ N21
  have out3 : ∀ (a b : V) (P' R : List V) (r₁ r₂ : V),
      (∀ z ∈ Q₁, Gx.Adj z a ∨ Gx.Adj z b) →
      IsPathFrom Gx R r₁ r₂ → (∀ z ∈ R, z ∈ F) →
      (∀ z ∈ ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
        (Gx.Adj r₁ z ↔ Gx.Adj a z)) →
      (∀ z ∈ ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
        (Gx.Adj r₂ z ↔ Gx.Adj b z)) → False := by
    intro a b P' R r₁ r₂ hcover hR hRF hcopy₁ hcopy₂
    obtain ⟨hr₁R, hr₂R⟩ := PathBasics.isPathFrom_ends_mem hR
    have hall : ∀ z ∈ Q₁, z ∈ attachments Gx F (striationVertices S T) := by
      intro z hz
      rcases hcover z hz with hza | hzb
      · exact ⟨hVQ₁ z hz, r₁, hRF r₁ hr₁R,
          ((hcopy₁ z (Or.inl (Or.inr hz))).mpr hza.symm).symm⟩
      · exact ⟨hVQ₁ z hz, r₂, hRF r₂ hr₂R,
          ((hcopy₂ z (Or.inl (Or.inr hz))).mpr hzb.symm).symm⟩
    obtain ⟨z, hzQ, hznot⟩ := hanti j Q₀ hQ₀
    exact hznot (hall z ((mQ₁ z).mpr hzQ))
  have h93 := _root_.Workspace.Statements.S09.SPGT.thm_9_3 Gx hberge P₁ P₂ Q₁ Q₂
    a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hp₁ hp₂ hq₁ hq₂
    ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪
      {v : V | v ∈ Q₂}) rfl hnoenl hnoover hnoovercompl F hFK hF.2.1 hnl
  rcases h93 with h1 | h2 | h3 | h4
  · obtain ⟨f, hfF, -, ⟨v, ⟨hfv, -⟩, hvP⟩, ⟨z, ⟨hfz, -⟩, hzP⟩, -⟩ := h1
    exact key f hfF v hvP z hzP hfv hfz
  · apply closing_outcome2_maximality_gap hs hF hmin hone hanti hii' hjj'
      hP₀ hP₀' hQ₀ hQ₀' mP₁ mP₂ mQ₁ mQ₂ hu.1 hw.1 huP hwQ huw hW hW3 hWF
      hknot hp₁ hp₂ hq₁ hq₂
    exact h2
  · obtain ⟨a, b, P, P', hcase, R, r₁, r₂, hR, hRF, -, hcopy₁, hcopy₂, -, -⟩ := h3
    rcases hcase with h | h | h | h <;> simp only [Prod.mk.injEq] at h
    · exact out3 a b P' R r₁ r₂ (by rw [h.1, h.2.1]; exact cover₁)
        hR hRF hcopy₁ hcopy₂
    · exact out3 a b P' R r₁ r₂
        (by rw [h.1, h.2.1]; exact fun z hz => (cover₁ z hz).symm)
        hR hRF hcopy₁ hcopy₂
    · exact out3 a b P' R r₁ r₂ (by rw [h.1, h.2.1]; exact cover₂)
        hR hRF hcopy₁ hcopy₂
    · exact out3 a b P' R r₁ r₂
        (by rw [h.1, h.2.1]; exact fun z hz => (cover₂ z hz).symm)
        hR hRF hcopy₁ hcopy₂
  · obtain ⟨x, y, Q', hcase, f, hfF, hcopy, -⟩ := h4
    have step : ∀ v ∈ P₁, ∀ z ∈ P₂, Gx.Adj x v → Gx.Adj x z → False := by
      intro v hv z hz hxv hxz
      exact key f hfF v hv z hz
        ((hcopy v (Or.inl (Or.inl hv))).mpr hxv)
        ((hcopy z (Or.inl (Or.inr hz))).mpr hxz)
    rcases hcase with h | h | h | h <;> simp only [Prod.mk.injEq] at h
    · exact step a₁ ha₁P a₂ ha₂P (by rw [h.1]; exact ax1a1) (by rw [h.1]; exact ax1a2)
    · exact step b₁ hb₁P b₂ hb₂P (by rw [h.1]; exact ay1b1) (by rw [h.1]; exact ay1b2)
    · exact step a₁ ha₁P b₂ hb₂P (by rw [h.1]; exact ax2a1) (by rw [h.1]; exact ax2b2)
    · exact step b₁ hb₁P a₂ ha₂P (by rw [h.1]; exact ay2b1) (by rw [h.1]; exact ay2a2)

/-! ### The minimal counterexample cannot exist -/

theorem local_of_minimal {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {F : Set V}
    (hs : Setup Gx S T) (hF : Cand Gx S T F) (hmin : Minimal Gx S T F) :
    LocalForStriation Gx S T (attachments Gx F (striationVertices S T)) := by
  by_contra hnot
  exact hnot
    ⟨fun i i' hi hi' => claim2 hs hF hmin hnot i i' hi hi',
      fun j Q hQ => claim3 hs hF hmin hnot j Q hQ,
      closing hs hF hmin hnot (fun i i' hi hi' => claim2 hs hF hmin hnot i i' hi hi')
        (fun j Q hQ => claim3 hs hF hmin hnot j Q hQ)⟩

end Workspace.ProofLemmas.Thm95Body
