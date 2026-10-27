import Workspace.Algo.TopMasterDescentLists
import Workspace.Algo.TopMasterSimulation

/-! # A bounded fold over representatives and kernel orbits
The two indices select a representative and its next orbit. Both cosets
are shortened after every update. Equality of decoded cosets is enough
to preserve the subsequent calls and the accumulated answer.
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv

 def masterDescFoldNorm (z : RawStr × AggnRecomputeState) : AggnRecomputeState :=
  (z.2.1, z.2.2.1, top2NormC z.1 z.2.2.2.1, top2NormC z.1 z.2.2.2.2)
 def masterDescFoldInit (P : AggnRecomputeInput) : AggnRecomputeState :=
  masterDescFoldNorm (P.1.2.2.2.1, aggnrInit (P, none))
 def masterDescFoldCombine (z : AggnRecomputeInput × ℕ × AggnRecomputeState × RawCoset) :
    AggnRecomputeState :=
  masterDescFoldNorm (z.1.1.2.2.2.1, aggnrCombine ((z.1, none), z.2))
 def masterDescFoldFinish (z : AggnRecomputeInput × AggnRecomputeState) : RawCoset :=
  top2NormC z.1.1.2.2.2.1 z.2.2.2.2
 def masterDescFoldRead (J : AggnRecomputeNode) : RawWinSI := J.2.getD J.1.1
 def masterDescFoldChild (z : AggnRecomputeInput × ℕ × AggnRecomputeState) : Option RawMasterSI :=
  (aggnrChild ((z.1, none), z.2)).map
    (fun J => masterCheckedCall (z.1.1.2.2.2.1, masterDescFoldRead J))
 def masterDescFoldWidth (P : AggnRecomputeInput) : ℕ := aggnrCount P * (aggnrWindows P).length

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

 theorem polyFun_masterDescFoldNorm : PolyFun masterDescFoldNorm := by
  have hs : PolyFun (fun z : RawStr × AggnRecomputeState => z.2) := polyFun_snd
  exact (pfst hs).pair ((pfst (psnd hs)).pair
    (((polyFun_fst.pair (pfst (psnd (psnd hs)))).comp polyFun_top2NormC).pair
      ((polyFun_fst.pair (psnd (psnd (psnd hs)))).comp polyFun_top2NormC)))
 theorem polyFun_masterDescFoldInit : PolyFun masterDescFoldInit := by
  have hx : PolyFun (fun P : AggnRecomputeInput => P.1.2.2.2.1) :=
    pfst (psnd (psnd (psnd polyFun_fst)))
  exact (hx.pair ((polyFun_id.pair (polyFun_const (none : Option RawWinSI))).comp
    aggnPolyFun_recomputeInit)).comp polyFun_masterDescFoldNorm
 theorem polyFun_masterDescFoldCombine : PolyFun masterDescFoldCombine := by
  have hx : PolyFun (fun z : AggnRecomputeInput × ℕ × AggnRecomputeState × RawCoset =>
      z.1.1.2.2.2.1) := pfst (psnd (psnd (psnd (pfst polyFun_fst))))
  exact (hx.pair ((((polyFun_fst.pair (polyFun_const (none : Option RawWinSI))).pair
    polyFun_snd).comp aggnPolyFun_recomputeCombine))).comp polyFun_masterDescFoldNorm
 theorem polyFun_masterDescFoldFinish : PolyFun masterDescFoldFinish := by
  have hx : PolyFun (fun z : AggnRecomputeInput × AggnRecomputeState => z.1.1.2.2.2.1) :=
    pfst (psnd (psnd (psnd (pfst polyFun_fst))))
  exact (hx.pair (psnd (psnd (psnd polyFun_snd)))).comp polyFun_top2NormC
 theorem polyFun_masterDescFoldRead : PolyFun masterDescFoldRead :=
  ((polyFun_snd.pair (polyFun_fst.comp polyFun_fst)).comp
    (PolyFun.optionElim polyFun_id polyFun_fst)).of_eq
      (fun J => by unfold masterDescFoldRead; cases J.2 <;> rfl)
 theorem polyFun_masterDescFoldChild : PolyFun masterDescFoldChild := by
  have h := (((polyFun_fst.pair (polyFun_const (none : Option RawWinSI))).pair
    polyFun_snd).comp aggnPolyFun_recomputeChild)
  have hx : PolyFun (fun z : AggnRecomputeInput × ℕ × AggnRecomputeState => z.1.1.2.2.2.1) :=
    pfst (psnd (psnd (psnd (pfst polyFun_fst))))
  have hh : PolyFun (fun z : AggnRecomputeNode × RawStr =>
      some (masterCheckedCall (z.2, masterDescFoldRead z.1))) :=
    ((polyFun_snd.pair (polyFun_fst.comp polyFun_masterDescFoldRead)).comp
      polyFun_masterCheckedCall).comp polyFun_some
  exact ((h.pair hx).comp (PolyFun.optionElim (polyFun_const none) hh)).of_eq
    (fun z => by unfold masterDescFoldChild; cases aggnrChild ((z.1, none), z.2) <;> rfl)
 theorem polyFun_masterDescFoldWidth : PolyFun masterDescFoldWidth :=
  ((pfst (psnd (psnd polyFun_id))).comp polyFun_length).mul
    ((psnd (psnd (psnd polyFun_id))).comp polyFun_length)

 def MasterDescFoldRel (n : ℕ) (s t : AggnRecomputeState) : Prop :=
  s.1 = t.1 ∧ s.2.1 = t.2.1 ∧ decCoset n s.2.2.1 = decCoset n t.2.2.1 ∧
    decCoset n s.2.2.2 = decCoset n t.2.2.2
 theorem masterDescFoldRel_refl (n : ℕ) (s : AggnRecomputeState) : MasterDescFoldRel n s s :=
  ⟨rfl, rfl, rfl, rfl⟩
 theorem masterDescFoldRel_trans {n : ℕ} {s t v : AggnRecomputeState}
    (h : MasterDescFoldRel n s t) (h' : MasterDescFoldRel n t v) : MasterDescFoldRel n s v :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1, h.2.2.2.trans h'.2.2.2⟩
 theorem masterDescFoldRel_norm {n : ℕ} {xs : RawStr} (hx : xs.length = n)
    (s : AggnRecomputeState) : MasterDescFoldRel n s (masterDescFoldNorm (xs, s)) :=
  ⟨rfl, rfl, (decCoset_top2NormC hx _).symm, (decCoset_top2NormC hx _).symm⟩
 theorem masterDescFoldRel_combine {n : ℕ} {P : AggnRecomputeInput}
    (hx : P.1.2.2.2.1.length = n) {s t : AggnRecomputeState}
    (h : MasterDescFoldRel n s t) (j : ℕ) (a : RawCoset) :
    MasterDescFoldRel n (aggnrCombine ((P, none), j, s, a))
      (masterDescFoldCombine (P, j, t, a)) := by
  apply masterDescFoldRel_trans (t := aggnrCombine ((P, none), j, t, a)) _
    (masterDescFoldRel_norm hx _)
  unfold aggnrCombine aggnrStep
  rw [h.1, h.2.1]
  split
  · exact ⟨rfl, rfl, rfl, h.2.2.2⟩
  · refine ⟨rfl, rfl, rfl, ?_⟩
    rw [decCoset_rawCosetJoin hx, decCoset_rawCosetJoin hx, h.2.2.2]

 theorem masterDescFoldRel_child {n : ℕ} {P : AggnRecomputeInput}
    (hx : P.1.2.2.2.1.length = n) {s t : AggnRecomputeState}
    (h : MasterDescFoldRel n s t) (j : ℕ) :
    (aggnrChild ((P, none), j, s)).map (aggnrDecode n) =
      (aggnrChild ((P, none), j, t)).map (aggnrDecode n) := by
  simp only [aggnrChild, Option.elim_none]
  rw [h.1, h.2.1]
  split
  · rw [Option.map_map, Option.map_map]
    cases hs : s.2.2.1 with
    | none =>
      have ht : t.2.2.1 = none := (decCoset_eq_empty_iff n _).mp (h.2.2.1.symm.trans (by rw [hs]; rfl))
      rw [ht]
    | some q =>
      cases ht : t.2.2.1 with
      | none =>
        have hh : s.2.2.1 = none := (decCoset_eq_empty_iff n _).mp (h.2.2.1.trans (by rw [ht]; rfl))
        rw [hs] at hh
        contradiction
      | some q' =>
        simp only [Option.map_some]
        congr 1
        dsimp only [Function.comp_apply]
        rw [aggnrDecode_leaf hx, aggnrDecode_leaf hx]
        rw [← hs, ← ht, h.2.2.1]
  · rfl

end Algo
