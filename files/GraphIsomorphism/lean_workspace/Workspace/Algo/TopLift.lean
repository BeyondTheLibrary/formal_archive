import Workspace.Algo.Extend
import Workspace.Algo.Luks
import Workspace.TopAction.Lifting

/-!
# Sec. 12: lifting a top permutation on the RAM

We put the action on the disjoint union of its two domains. The second domain
is then a window, so `rawPreimage` finds a lift. Proposition 12.0.1 uses this
lift to shift the source string and asks one instance for the kernel.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)
open scoped Pointwise

/-- An action given by two domain witnesses and the images of its generators. -/
abbrev RawAction := (List ℕ × RawGens) × (List ℕ × RawGens)

/-- Well-formed action data. The image assignment is certified by the supplied homomorphism. -/
def RawAction.WF (n m : ℕ) (p : RawAction)
    (ϕ : decGroup n p.1.2 →* Perm (Fin m)) : Prop :=
  p.1.1.length = n ∧ p.2.1.length = m ∧
    RawGens.WF n p.1.2 ∧ RawGens.WF m p.2.2 ∧
    ImgsOf (p.1.2.map (decPerm n)) (p.2.2.map (decPerm m)) ϕ

variable {n m : ℕ} {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}

/-- The second domain is invariant under the graph of the action. -/
theorem isInvariant_extWin {ϕ : genGroup gens →* Perm (Fin m)}
    (hI : ImgsOf gens imgs ϕ) :
    Babai.IsInvariant (genGroup (extGensOf n m gens imgs)) (winSet (n + m) (extWin n m)) := by
  apply (Babai.isInvariant_iff_mem _ _).2
  intro σ hσ x
  obtain ⟨a, ha, rfl⟩ := (mem_ext_group_iff hI).1 hσ
  constructor
  · intro hx
    obtain ⟨j, rfl⟩ := mem_extWinSet.1 hx
    rw [extPerm_natAdd]
    exact mem_extWinSet.2 ⟨_, rfl⟩
  · intro hx
    obtain ⟨j, hj⟩ := mem_extWinSet.1 hx
    have heq : x = Fin.natAdd n ((ϕ ⟨a, ha⟩)⁻¹ j) := by
      apply (extPerm n m a (ϕ ⟨a, ha⟩)).injective
      simpa using hj
    rw [heq]
    exact mem_extWinSet.2 ⟨_, rfl⟩

/-- Restricting the disjoint union to its second domain reads the second permutation. -/
theorem rawRestrictPerm_extPerm (a : Perm (Fin n)) (b : Perm (Fin m)) :
    rawRestrictPerm (extWin n m, encPerm (n + m) (extPerm n m a b)) = encPerm m b := by
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    have hkm : k < m := by simpa using hk'
    have hΔ : ∀ (j : ℕ) (hj : j < (extWin n m).length),
        (extWin n m)[j] = j + n := by
      intro j hj
      simp [extWin]
    show ((extWin n m).map (fun u => rawInvLookup ((extWin n m).zipIdx,
      rawApply (encPerm (n + m) (extPerm n m a b), u))))[k]'hk = _
    rw [List.getElem_map, hΔ k (by simpa using hkm)]
    rw [rawApply_encPerm _ _ (by omega)]
    have he : (⟨k + n, by omega⟩ : Fin (n + m)) = Fin.natAdd n ⟨k, hkm⟩ :=
      Fin.ext (by simp [Fin.natAdd, Nat.add_comm])
    rw [he, extPerm_natAdd, getElem_encPerm m b k hkm]
    have hj : ((b ⟨k, hkm⟩ : Fin m) : ℕ) < (extWin n m).length := by simp
    have hval : ((Fin.natAdd n (b ⟨k, hkm⟩) : Fin (n + m)) : ℕ)
        = (extWin n m)[((b ⟨k, hkm⟩ : Fin m) : ℕ)]'hj := by
      rw [hΔ]
      simp [Fin.natAdd, Nat.add_comm]
    rw [hval, rawInvLookup_getElem (nodup_extWin n m) hj]

/-- Sec. 2.2.3, Proposition 2.2.6 (b), used in Proposition 12.0.1:
find a preimage of a top permutation, or return `none`. -/
def actPreimage (p : RawAction × RawPerm) : Option RawPerm :=
  (rawPreimage ((rawExtDom (p.1.1.1, p.1.2.1), rawExtGens (p.1.1.2, p.1.2.2)),
    (rawExtWin (p.1.1.1, p.1.2.1), p.2))).map
      (fun r => rawProjPerm (r, p.1.1.1.length))

section Preimage

variable {dom gdom : List ℕ} {ϕ : genGroup gens →* Perm (Fin m)}

/-- A successful action lift is an encoded element of the group with the requested image. -/
theorem actPreimage_eq_some (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (τ : Perm (Fin m)) {r : RawPerm}
    (hr : actPreimage (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
      encPerm m τ) = some r) :
    ∃ (σ : Perm (Fin n)) (hσ : σ ∈ genGroup gens), r = encPerm n σ ∧ ϕ ⟨σ, hσ⟩ = τ := by
  have hlen : (dom ++ gdom).length = n + m := by simp [hd, hg]
  have ht : RawPerm.WF (extWin n m).length (encPerm m τ) := by
    simpa using wf_encPerm m τ
  have henc := encPerm_decPerm ht
  unfold actPreimage at hr
  rw [rawExtDom, rawExtGens_spec gens imgs hI.1, rawExtWin_eq dom gdom hd hg, hd] at hr
  obtain ⟨r', hr', hrout⟩ := Option.map_eq_some_iff.1 hr
  have hr'' : rawPreimage ((dom ++ gdom, (extGensOf n m gens imgs).map (encPerm (n + m))),
      (extWin n m, encPerm (extWin n m).length (decPerm (extWin n m).length (encPerm m τ))))
      = some r' := by rwa [henc]
  obtain ⟨σ', hσ', hrenc, hres⟩ := rawPreimage_eq_some hlen (nodup_extWin n m)
    (fun u hu => lt_extWin hu) (isInvariant_extWin hI) hr''
  obtain ⟨σ, hσ, hσeq⟩ := (mem_ext_group_iff hI).1 hσ'
  refine ⟨σ, hσ, ?_, ?_⟩
  · rw [← hrout, hrenc, hσeq, rawProjPerm_spec]
  · have hrest := rawRestrictPerm_spec (nodup_extWin n m) (fun u hu => lt_extWin hu)
      (isInvariant_extWin hI) hσ'
    rw [hres, henc, hσeq, rawRestrictPerm_extPerm] at hrest
    exact encPerm_injective m hrest

/-- An action lift fails exactly when the requested image is outside the image group. -/
theorem actPreimage_eq_none_iff (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (τ : Perm (Fin m)) :
    actPreimage (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), encPerm m τ)
      = none ↔ τ ∉ ϕ.range := by
  constructor
  · intro hr hτ
    obtain ⟨σ, hσ⟩ := hτ
    have hlen : (dom ++ gdom).length = n + m := by simp [hd, hg]
    have ht : RawPerm.WF (extWin n m).length (encPerm m τ) := by
      simpa using wf_encPerm m τ
    have henc := encPerm_decPerm ht
    unfold actPreimage at hr
    rw [rawExtDom, rawExtGens_spec gens imgs hI.1, rawExtWin_eq dom gdom hd hg] at hr
    have hr' := Option.map_eq_none_iff.1 hr
    have hmem : extPerm n m (σ : Perm (Fin n)) (ϕ σ)
        ∈ genGroup (extGensOf n m gens imgs) :=
      (mem_ext_group_iff hI).2 ⟨σ, σ.2, rfl⟩
    have hrest := rawRestrictPerm_spec (nodup_extWin n m) (fun u hu => lt_extWin hu)
      (isInvariant_extWin hI) hmem
    rw [rawRestrictPerm_extPerm] at hrest
    have heq := encPerm_injective (extWin n m).length
      (hrest.symm.trans ((congrArg (encPerm m) hσ).trans henc.symm))
    apply rawPreimage_eq_none hlen (nodup_extWin n m) (fun u hu => lt_extWin hu)
      (isInvariant_extWin hI) (hw := decPerm (extWin n m).length (encPerm m τ))
      (by rwa [henc]) _ hmem heq
  · intro hτ
    cases hr : actPreimage (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
        encPerm m τ) with
    | none => rfl
    | some r =>
      obtain ⟨σ, hσ, _, hϕ⟩ := actPreimage_eq_some hd hg hI τ hr
      exact False.elim (hτ ⟨⟨σ, hσ⟩, hϕ⟩)

end Preimage

/-- The action lift runs in polynomial time on the unit-cost RAM. -/
theorem polyFun_actPreimage : PolyFun actPreimage := by
  have hdom : PolyFun (fun p : RawAction × RawPerm => (p.1.1.1, p.1.2.1)) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)
  have hgens : PolyFun (fun p : RawAction × RawPerm => (p.1.1.2, p.1.2.2)) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_snd).pair
      ((polyFun_fst.comp polyFun_snd).comp polyFun_snd)
  have hlift : PolyFun (fun p : RawAction × RawPerm =>
      rawPreimage ((rawExtDom (p.1.1.1, p.1.2.1), rawExtGens (p.1.1.2, p.1.2.2)),
        (rawExtWin (p.1.1.1, p.1.2.1), p.2))) :=
    (((hdom.comp polyFun_rawExtDom).pair (hgens.comp polyFun_rawExtGens)).pair
      ((hdom.comp polyFun_rawExtWin).pair polyFun_snd)).comp polyFun_rawPreimage
  have hn : PolyFun (fun p : RawAction × RawPerm => p.1.1.1.length) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_length
  have hs : PolyFun (fun p : RawPerm × ℕ => some (rawProjPerm p)) :=
    polyFun_rawProjPerm.comp polyFun_some
  refine ((hlift.pair hn).comp (PolyFun.optionElim (polyFun_const none) hs)).of_eq ?_
  intro p
  cases h : rawPreimage ((rawExtDom (p.1.1.1, p.1.2.1), rawExtGens (p.1.1.2, p.1.2.2)),
    (rawExtWin (p.1.1.1, p.1.2.1), p.2)) <;> simp [actPreimage, h]

/-! ## The single kernel instance -/

/-- The input of Proposition 12.0.1: an action, a top permutation and two strings. -/
abbrev RawTopLift := RawAction × RawPerm × RawStr × RawStr

/-- Well-formed input for Proposition 12.0.1. No giant or transitivity assumption is needed. -/
def RawTopLift.WF (n m : ℕ) (p : RawTopLift)
    (ϕ : decGroup n p.1.1.2 →* Perm (Fin m)) : Prop :=
  RawAction.WF n m p.1 ϕ ∧ RawPerm.WF m p.2.1 ∧
    p.2.2.1.length = n ∧ p.2.2.2.length = n

/-- The lift and the one kernel instance passed to the recursive solver. -/
abbrev TopLiftPlan := RawPerm × RawSI

/-- A full-domain instance decoded from its generators and two strings. -/
noncomputable def decFullSI (n : ℕ) (I : RawSI) : Babai.SIInstance (Fin n) ℕ :=
  ⟨decGroup n I.1, Set.univ, decStrN n I.2.1, decStrN n I.2.2⟩

/-- Sec. 12, Proposition 12.0.1: prepare `Iso_(ker ϕ)(x^σ,y)`, or reject a
top permutation outside the image. The kernel generators are shortened. -/
def topLiftPrepare (p : RawTopLift) : Option TopLiftPlan :=
  (actPreimage (p.1, p.2.1)).map (fun σ =>
    (σ, tidyGens (p.1.1.1, actKerGens p.1), rawStrAct (σ, p.2.2.1), p.2.2.2))

section Prepare

variable {dom gdom : List ℕ} {ϕ : genGroup gens →* Perm (Fin m)}

/-- The prepared child uses exactly the kernel and the source string shifted by the
computed lift. Its generating list is well formed and has at most `n²` entries. -/
theorem topLiftPrepare_spec (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (τ : Perm (Fin m)) (x y : Fin n → ℕ)
    {q : TopLiftPlan}
    (hq : topLiftPrepare (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
      encPerm m τ, encStrN x, encStrN y) = some q) :
    ∃ σ : genGroup gens, q.1 = encPerm n σ ∧ ϕ σ = τ ∧
      q.2.2.1 = encStrN (Babai.strAct x σ) ∧ q.2.2.2 = encStrN y ∧
      decGroup n q.2.1 = Babai.kerSubgroup ϕ ∧
      RawGens.WF n q.2.1 ∧ q.2.1.length ≤ n * n := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hq
  obtain ⟨σ, hσ, rfl, hϕ⟩ := actPreimage_eq_some hd hg hI τ hr
  refine ⟨⟨σ, hσ⟩, rfl, hϕ, rawStrAct_encStrN σ x, rfl, ?_,
    wf_tidyGens hd _, length_tidyGens hd _⟩
  rw [decGroup_tidyGens hd, decGroup_actKerGens hd hg hI]
  rfl

/-- Preparation makes no child exactly when the requested top permutation is absent. -/
theorem topLiftPrepare_eq_none_iff (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (τ : Perm (Fin m)) (x y : Fin n → ℕ) :
    topLiftPrepare (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
      encPerm m τ, encStrN x, encStrN y) = none ↔ τ ∉ ϕ.range := by
  exact Option.map_eq_none_iff.trans (actPreimage_eq_none_iff hd hg hI τ)

/-- Sec. 12, Proposition 12.0.1: the one child decodes to the stated kernel instance. -/
theorem topLiftPrepare_child (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (τ : Perm (Fin m)) (x y : Fin n → ℕ)
    {q : TopLiftPlan}
    (hq : topLiftPrepare (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
      encPerm m τ, encStrN x, encStrN y) = some q) :
    ∃ σ : genGroup gens, q.1 = encPerm n σ ∧ ϕ σ = τ ∧
      decFullSI n q.2 =
        ⟨Babai.kerSubgroup ϕ, Set.univ, Babai.strAct x σ, y⟩ := by
  obtain ⟨σ, hσ, hϕ, hx, hy, hK, _, _⟩ := topLiftPrepare_spec hd hg hI τ x y hq
  refine ⟨σ, hσ, hϕ, ?_⟩
  simp only [decFullSI, hx, hy, hK, decStrN_encStrN]

end Prepare

/-- Preparing the single kernel instance takes polynomial time on the unit-cost RAM. -/
theorem polyFun_topLiftPrepare : PolyFun topLiftPrepare := by
  have hp : PolyFun (fun p : RawTopLift => actPreimage (p.1, p.2.1)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_actPreimage
  have hk : PolyFun (fun p : RawTopLift => tidyGens (p.1.1.1, actKerGens p.1)) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair
      (polyFun_fst.comp polyFun_actKerGens)).comp polyFun_tidyGens
  have hx : PolyFun (fun p : RawTopLift => p.2.2.1) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_fst
  have hy : PolyFun (fun p : RawTopLift => p.2.2.2) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_snd
  have hs : PolyFun (fun z : RawPerm × RawTopLift =>
      (some (z.1, tidyGens (z.2.1.1.1, actKerGens z.2.1),
        rawStrAct (z.1, z.2.2.2.1), z.2.2.2.2) : Option TopLiftPlan)) :=
    (polyFun_fst.pair ((polyFun_snd.comp hk).pair
      (((polyFun_fst.pair (polyFun_snd.comp hx)).comp polyFun_rawStrAct).pair
        (polyFun_snd.comp hy)))).comp polyFun_some
  refine ((hp.pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const none) hs)).of_eq ?_
  intro p
  cases h : actPreimage (p.1, p.2.1) <;> simp [topLiftPrepare, h]

/-! ## Translating the answer back -/

/-- Conjugation of well-formed raw generators decodes to conjugation of their group. -/
theorem decGroup_rawConj {r : RawPerm} {gs : RawGens}
    (hr : RawPerm.WF n r) (hgs : RawGens.WF n gs) :
    decGroup n (rawConj (r, gs)) =
      (decGroup n gs).map (MulAut.conj (decPerm n r)⁻¹).toMonoidHom := by
  conv_lhs => rw [← map_encPerm_decPerm hgs]
  rw [rawConj_spec hr, decGroup_map_encPerm, genGroup_map_conj]
  rfl

/-- Sec. 12, Proposition 12.0.1: right translation changes both fields of a left coset. -/
theorem rightTranslate_smul_subgroup (M : Subgroup (Perm (Fin n))) (ρ σ : Perm (Fin n)) :
    (ρ * σ) • (M.map (MulAut.conj σ⁻¹).toMonoidHom : Set (Perm (Fin n))) =
      Babai.rightTranslate (ρ • (M : Set (Perm (Fin n)))) σ := by
  ext τ
  constructor
  · rintro ⟨a, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨ρ * g, ⟨g, hg, rfl⟩, ?_⟩
    change (ρ * g) * σ = (ρ * σ) * (σ⁻¹ * g * σ⁻¹⁻¹)
    simp [mul_assoc]
  · rintro ⟨a, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨_, ⟨g, hg, rfl⟩, ?_⟩
    change (ρ * σ) * (σ⁻¹ * g * σ⁻¹⁻¹) = (ρ * g) * σ
    simp [mul_assoc]

/-- Sec. 12, Proposition 12.0.1: translate an answer on the right by the lift.
For `ρ • M`, return `(ρ σ) • (σ⁻¹ M σ)`. Normalize raw inputs and shorten the group. -/
def rawRightTranslate (p : List ℕ × RawPerm × RawCoset) : RawCoset :=
  p.2.2.map (fun q =>
    (tidyGens (p.1, rawConj (normPerm (p.1, p.2.1), normGens (p.1, q.1))),
      rawMul (normPerm (p.1, q.2), normPerm (p.1, p.2.1))))

/-- The translated answer decodes correctly even when the raw answer is not well formed. -/
theorem decCoset_rawRightTranslate {dom : List ℕ} (hd : dom.length = n)
    (r : RawPerm) (c : RawCoset) :
    decCoset n (rawRightTranslate (dom, r, c)) =
      Babai.rightTranslate (decCoset n c) (decPerm n r) := by
  cases c with
  | none => simp [rawRightTranslate, decCoset, Babai.rightTranslate]
  | some q =>
    obtain ⟨gs, ρ⟩ := q
    have hr := wf_normPerm hd r
    have hρ := wf_normPerm hd ρ
    have hgs := wf_normGens hd gs
    change decCoset n (some (_, _)) = _
    rw [decCoset_some, decGroup_tidyGens hd, decGroup_rawConj hr hgs,
      decGroup_normGens hd, rawMul_of_wf hρ hr, decPerm_encPerm,
      decPerm_normPerm hd, decPerm_normPerm hd, decCoset_some]
    exact rightTranslate_smul_subgroup _ _ _

/-- Translation returns at most `n²` well-formed generators and a well-formed representative. -/
theorem rawRightTranslate_wf {dom : List ℕ} (hd : dom.length = n)
    (r : RawPerm) (c : RawCoset) {gs : RawGens} {ρ : RawPerm}
    (h : rawRightTranslate (dom, r, c) = some (gs, ρ)) :
    RawGens.WF n gs ∧ gs.length ≤ n * n ∧ RawPerm.WF n ρ := by
  obtain ⟨q, _, hq⟩ := Option.map_eq_some_iff.1 h
  cases hq
  exact ⟨wf_tidyGens hd _, length_tidyGens hd _,
    wf_rawMul (wf_normPerm hd _) (wf_normPerm hd _)⟩

/-- Right translation of a raw answer takes polynomial time on the unit-cost RAM. -/
theorem polyFun_rawRightTranslate : PolyFun rawRightTranslate := by
  have hd : PolyFun (fun p : List ℕ × RawPerm × RawCoset => p.1) := polyFun_fst
  have hr : PolyFun (fun p : List ℕ × RawPerm × RawCoset => normPerm (p.1, p.2.1)) :=
    (hd.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_normPerm
  have hs : PolyFun (fun z : (RawGens × RawPerm) × (List ℕ × RawPerm × RawCoset) =>
      (some (tidyGens (z.2.1,
        rawConj (normPerm (z.2.1, z.2.2.1), normGens (z.2.1, z.1.1))),
        rawMul (normPerm (z.2.1, z.1.2), normPerm (z.2.1, z.2.2.1))) : RawCoset)) := by
    have hd' : PolyFun (fun z : (RawGens × RawPerm) × (List ℕ × RawPerm × RawCoset) =>
        z.2.1) := polyFun_snd.comp hd
    have hr' : PolyFun (fun z : (RawGens × RawPerm) × (List ℕ × RawPerm × RawCoset) =>
        normPerm (z.2.1, z.2.2.1)) := polyFun_snd.comp hr
    have hgs : PolyFun (fun z : (RawGens × RawPerm) × (List ℕ × RawPerm × RawCoset) =>
        normGens (z.2.1, z.1.1)) :=
      (hd'.pair (polyFun_fst.comp polyFun_fst)).comp polyFun_normGens
    have hρ : PolyFun (fun z : (RawGens × RawPerm) × (List ℕ × RawPerm × RawCoset) =>
        normPerm (z.2.1, z.1.2)) :=
      (hd'.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_normPerm
    exact (((hd'.pair ((hr'.pair hgs).comp polyFun_rawConj)).comp polyFun_tidyGens).pair
      ((hρ.pair hr').comp polyFun_rawMul)).comp polyFun_some
  refine ((((polyFun_snd.comp polyFun_snd).pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const none) hs))).of_eq ?_
  intro p
  cases h : p.2.2 <;> simp [rawRightTranslate, h]

/-! ## The complete one-call interface -/

/-- Sec. 12, Proposition 12.0.1: reconstruct from the prepared lift and the child's answer. -/
def topLiftFinish (p : List ℕ × Option TopLiftPlan × RawCoset) : RawCoset :=
  p.2.1.elim none (fun q => rawRightTranslate (p.1, q.1, p.2.2))

/-- Sec. 12, Proposition 12.0.1 on the RAM: a correct answer to the prepared
kernel instance gives exactly the set of liftings to isomorphisms. -/
theorem topLift_spec {dom gdom : List ℕ} {ϕ : genGroup gens →* Perm (Fin m)}
    (hd : dom.length = n) (hg : gdom.length = m) (hI : ImgsOf gens imgs ϕ)
    (τ : Perm (Fin m)) (x y : Fin n → ℕ) (ans : RawCoset)
    (hans : ∀ q, topLiftPrepare
      (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
        encPerm m τ, encStrN x, encStrN y) = some q →
      decCoset n ans = (decFullSI n q.2).answer) :
    decCoset n (topLiftFinish (dom, topLiftPrepare
      (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
        encPerm m τ, encStrN x, encStrN y), ans)) = Babai.liftingSet ϕ x y τ := by
  cases hp : topLiftPrepare
      (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
        encPerm m τ, encStrN x, encStrN y) with
  | none =>
    have hτ := (topLiftPrepare_eq_none_iff hd hg hI τ x y).1 hp
    exact (Babai.liftingSet_eq_empty ϕ x y hτ).symm
  | some q =>
    obtain ⟨σ, hσ, hϕ, hchild⟩ := topLiftPrepare_child hd hg hI τ x y hp
    change decCoset n (rawRightTranslate (dom, q.1, ans)) = _
    rw [decCoset_rawRightTranslate hd, hσ, decPerm_encPerm, hans q hp, hchild,
      Babai.SIInstance.answer, Babai.wIso_univ]
    rw [← hϕ]
    exact (Babai.Proposition_12_0_1_lifting ϕ x y σ).symm

/-- The complete raw lifting interface has the value of `Babai.liftingReduction`.
This is a value equality, not an equality of its chosen child instances. -/
theorem topLift_eq_run_liftingReduction {dom gdom : List ℕ}
    {ϕ : genGroup gens →* Perm (Fin m)}
    (hd : dom.length = n) (hg : gdom.length = m) (hI : ImgsOf gens imgs ϕ)
    (τ : Perm (Fin m)) (x y : Fin n → ℕ) (ans : RawCoset)
    (hans : ∀ q, topLiftPrepare
      (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
        encPerm m τ, encStrN x, encStrN y) = some q →
      decCoset n ans = (decFullSI n q.2).answer) :
    decCoset n (topLiftFinish (dom, topLiftPrepare
      (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
        encPerm m τ, encStrN x, encStrN y), ans)) =
      (Babai.liftingReduction ϕ x y τ).run := by
  rw [Babai.run_liftingReduction]
  exact topLift_spec hd hg hI τ x y ans hans

/-- Reconstruction takes polynomial time, including the empty branch. -/
theorem polyFun_topLiftFinish : PolyFun topLiftFinish := by
  have hs : PolyFun (fun z : TopLiftPlan × (List ℕ × Option TopLiftPlan × RawCoset) =>
      rawRightTranslate (z.2.1, z.1.1, z.2.2.2)) :=
    ((polyFun_snd.comp polyFun_fst).pair ((polyFun_fst.comp polyFun_fst).pair
      ((polyFun_snd.comp polyFun_snd).comp polyFun_snd))).comp polyFun_rawRightTranslate
  exact (((polyFun_snd.comp polyFun_fst).pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const none) hs)).of_eq (fun _ => rfl)

/-- Sec. 12, Proposition 12.0.1 for arbitrary well-formed raw input. The only
oracle premise is correctness of the answer to the one prepared child, if present. -/
theorem topLift_spec_of_wf (p : RawTopLift)
    (ϕ : decGroup n p.1.1.2 →* Perm (Fin m)) (hp : RawTopLift.WF n m p ϕ)
    (ans : RawCoset)
    (hans : ∀ q, topLiftPrepare p = some q → decCoset n ans = (decFullSI n q.2).answer) :
    decCoset n (topLiftFinish (p.1.1.1, topLiftPrepare p, ans)) =
      Babai.liftingSet ϕ (decStrN n p.2.2.1) (decStrN n p.2.2.2) (decPerm m p.2.1) := by
  obtain ⟨⟨hd, hg, hgs, his, hI⟩, hτ, hx, hy⟩ := hp
  have he : (((p.1.1.1, (p.1.1.2.map (decPerm n)).map (encPerm n)),
      (p.1.2.1, (p.1.2.2.map (decPerm m)).map (encPerm m))),
      encPerm m (decPerm m p.2.1), encStrN (decStrN n p.2.2.1),
      encStrN (decStrN n p.2.2.2)) = p := by
    rw [map_encPerm_decPerm hgs, map_encPerm_decPerm his, encPerm_decPerm hτ,
      encStrN_decStrN hx, encStrN_decStrN hy]
  have h := topLift_spec hd hg hI (decPerm m p.2.1)
    (decStrN n p.2.2.1) (decStrN n p.2.2.2) ans
    (fun q hq => hans q (by rwa [he] at hq))
  rwa [he] at h

end Algo
