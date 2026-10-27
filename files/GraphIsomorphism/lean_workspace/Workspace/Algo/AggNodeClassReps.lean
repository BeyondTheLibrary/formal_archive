import Workspace.Algo.AggNodeGuideRows

/-! # One explicit representative of each local-guide class

Choose the first tuple in each class. This changes only the order in which
the paper's classes are listed. The generic proof uses equality of class
values and applies later to the exact computed local-guide relation.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

section Lists
variable {α β : Type*} [DecidableEq α]

def aggnFirstBy (r : α → α → Bool) (L : List α) (a : α) : Option α :=
  (L.filter fun b => r b a).head?

def aggnClassReps (r : α → α → Bool) (L : List α) : List α :=
  L.filter fun a => decide (aggnFirstBy r L a = some a)

theorem aggnClassReps_mem {r : α → α → Bool} {L : List α} {a : α} :
    a ∈ aggnClassReps r L ↔ a ∈ L ∧ aggnFirstBy r L a = some a := by
  simp only [aggnClassReps,List.mem_filter,decide_eq_true_eq]

theorem aggnFirstBy_eq {r : α → α → Bool} {L : List α} {f : α → β}
    (hs : ∀ a ∈ L,∀ b ∈ L,r a b = true ↔ f a = f b)
    {a b : α} (ha : a ∈ L) (hb : b ∈ L) (he : f a = f b) :
    aggnFirstBy r L a = aggnFirstBy r L b := by
  apply congrArg List.head?
  apply List.filter_congr
  intro x hx
  apply Bool.eq_iff_iff.mpr
  rw [hs x hx a ha,hs x hx b hb,he]

theorem aggnFirstBy_some {r : α → α → Bool} {L : List α} {f : α → β}
    (hs : ∀ a ∈ L,∀ b ∈ L,r a b = true ↔ f a = f b)
    {a : α} (ha : a ∈ L) :
    ∃ b,aggnFirstBy r L a = some b ∧ b ∈ L ∧ f b = f a := by
  have hra : a ∈ L.filter (fun b => r b a) := List.mem_filter.mpr ⟨ha,(hs a ha a ha).mpr rfl⟩
  cases hh : aggnFirstBy r L a with
  | none =>
    have he : L.filter (fun b => r b a) = [] := List.head?_eq_none_iff.mp hh
    rw [he] at hra
    exact False.elim (List.not_mem_nil hra)
  | some b =>
    obtain ⟨hb,hr⟩ := List.mem_filter.mp (List.mem_of_mem_head? hh)
    exact ⟨b,rfl,hb,(hs b hb a ha).mp hr⟩

theorem aggnClassReps_complete {r : α → α → Bool} {L : List α} {f : α → β}
    (hs : ∀ a ∈ L,∀ b ∈ L,r a b = true ↔ f a = f b)
    {a : α} (ha : a ∈ L) : ∃ b ∈ aggnClassReps r L,f b = f a := by
  obtain ⟨b,hb,hbL,he⟩ := aggnFirstBy_some hs ha
  refine ⟨b,aggnClassReps_mem.mpr ⟨hbL,?_⟩,he⟩
  rw [aggnFirstBy_eq hs hbL ha he]
  exact hb

theorem aggnClassReps_unique {r : α → α → Bool} {L : List α} {f : α → β}
    (hs : ∀ a ∈ L,∀ b ∈ L,r a b = true ↔ f a = f b)
    {a b : α} (ha : a ∈ aggnClassReps r L) (hb : b ∈ aggnClassReps r L)
    (he : f a = f b) : a = b := by
  obtain ⟨ha,hea⟩ := aggnClassReps_mem.mp ha
  obtain ⟨hb,heb⟩ := aggnClassReps_mem.mp hb
  exact Option.some.inj (hea.symm.trans ((aggnFirstBy_eq hs ha hb he).trans heb))

theorem aggnClassReps_nodup {r : α → α → Bool} {L : List α} (hL : L.Nodup) :
    (aggnClassReps r L).Nodup := hL.filter _

end Lists

abbrev AggnGuideRepsInput := (RawAction × RawAggCompareTable) × List (List ℕ)

def aggnGuideFirst (p : AggnGuideRepsInput × List ℕ) : Option (List ℕ) :=
  aggnFirstBy (fun a b => aggnGuideTuple (p.1.1,false,a,b)) p.1.2 p.2

def aggnGuideRepTest (p : AggnGuideRepsInput × List ℕ) : Bool :=
  decide (aggnGuideFirst p = some p.2)

def aggnGuideReps (p : AggnGuideRepsInput) : List (List ℕ) :=
  aggnClassReps (fun a b => aggnGuideTuple (p.1,false,a,b)) p.2

private theorem fstP {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem sndP {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

theorem aggnPolyFun_guideFirst : PolyFun aggnGuideFirst := by
  have hi : PolyFun (fun p : (AggnGuideRepsInput × List ℕ) × List ℕ => p) := polyFun_id
  have ht : PolyFun (fun p : (AggnGuideRepsInput × List ℕ) × List ℕ =>
      aggnGuideTuple (p.1.1.1,false,p.2,p.1.2)) :=
    ((fstP (fstP (fstP hi))).pair ((polyFun_const false).pair
      ((sndP hi).pair (sndP (fstP hi))))).comp aggnPolyFun_guideTuple
  exact ((polyFun_id.pair (polyFun_fst.comp polyFun_snd)).comp
    (PolyFun.filterParam ht)).comp polyFun_headOption

theorem aggnPolyFun_guideRepTest : PolyFun aggnGuideRepTest := by
  have hopt : PolyFun (fun p : Option (List ℕ) × List ℕ => decide (p.1 = some p.2)) :=
    (PolyFun.optionElim (polyFun_const false) polyFun_listNatEq).of_eq (fun p => by
      rcases p with ⟨o,l⟩
      cases o <;> simp [Option.elim])
  exact (aggnPolyFun_guideFirst.pair polyFun_snd).comp hopt

theorem aggnPolyFun_guideReps : PolyFun aggnGuideReps :=
  (polyFun_id.pair polyFun_snd).comp (PolyFun.filterParam aggnPolyFun_guideRepTest)

end Algo
