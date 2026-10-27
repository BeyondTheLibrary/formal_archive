/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Proposition 10.5.4, proved.
-/
import Workspace.Algo.TpointRaw

/-!
# Proposition 10.5.4 as a theorem (§10.5)

> **Proposition 10.5.4.** Given a giant representation `ϕ : G → S_k`, we can find the
> standard blocks in each `G`-orbit in polynomial time.  *Proof.* Standard.

The paper gives no proof and no citation.  Until A12 session 7 this statement was an axiom
of the project (`Babai.Proposition_10_5_4`, by a decision of the user, the corrected paper
entry 104), for one reason only: nobody had computed the sets `T(u)` of
Theorem 10.5.1 (a), and the standard block of `u` is defined from `T(u)` (Eq. (55)):

> the standard block of `u` is `{y ∈ u^G | T(y) = T(u)}`.

`Algo.rawTpoint` (`Workspace/Algo/TpointRaw.lean`) now computes `T(u)` in polynomial time,
and `Algo.rawOrbit` computes the orbit of `u`.  So the labelling the axiom asks for is
immediate: label `u` by the first point `v` of the domain that lies in the orbit of `u`
and has `T(v) = T(u)`.  Two points get the same label exactly when they lie in the same
standard block, because "same orbit and same `T`" is an equivalence relation and the
label is the least point of the class.

`Algo.proposition_10_5_4` below is the statement of the former axiom, word for word, as a
theorem.  The axiom is deleted, and `Workspace/Algo/StdBlocks.lean` now rests on this
theorem.

## How the statement is read

* *"Given a giant representation `ϕ : G → S_k`"*.  The group is given by a list of generators
  and `ϕ` by the images of these generators, which is the input of Proposition 2.2.6
  (`Algo.ImgsOf`, the input of the proved routine `Algo.actKerGens`).  The lists `dom` and
  `gdom` are the domain witnesses of that convention: they have lengths `n` and `k`, so that
  the size of the input is at least `n + k`.
* *"the standard blocks in each `G`-orbit"*.  The standard blocks are defined in
  Theorem 10.5.1 (e) and only under the hypotheses of that theorem: `ϕ` is a giant
  representation and `k ≥ max{9, 2 log₂ n₀}`, with `n₀` the length of the largest orbit.
  Outside these hypotheses `T(x)` has no meaning (`Babai.Tpoint` is then a junk value), so
  nothing is claimed there.  This is `Babai.VeryLargeK k (maxOrbitLength G)`.
* *"we can find"*.  The output is a labelling of the points: two points get the same label
  exactly when they lie in the same standard block, that is, in the same `G`-orbit and with
  the same `T(x)`.  This one list holds the standard blocks of every orbit.
* *"in polynomial time"*.  `RAM.PolyFun`: polynomial time on the unit-cost RAM in the size of
  the input, at the calling convention of the workspace, with an output of polynomial size.

## Main results

* `Algo.tptSameBlock` — the test "same orbit and same `T`";
* `Algo.tptLabel`, `Algo.tptLabels` — the labelling and the table;
* `Algo.tptLabel_eq_iff` — two points get the same label exactly when they lie in one
  standard block;
* `Algo.proposition_10_5_4` — Proposition 10.5.4, proved.

No axiom, no `sorry`.
-/

namespace Algo

open RAM RAM.Targets MulAction
open Equiv (Perm)

variable {n m : ℕ} {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}

/-! ## The test and the labelling -/

/-- **Eq. (55) on raw data**: `v` lies in the standard block of `u` when `v` lies in the
orbit of `u` and `T(v) = T(u)`.  `q.1.1` is the action, `q.1.2` is `u`, `q.2` is `v`. -/
def tptSameBlock (q : (RawAction × ℕ) × ℕ) : Bool :=
  if decide (q.2 ∈ rawOrbit (q.1.1.1.2, q.1.2)) = true then
    decide (rawTpoint (q.1.1, q.1.2) = rawTpoint (q.1.1, q.2))
  else false

/-- **The label of a point**: the first point of the domain that lies in the same standard
block.  The points are read off the *length* of the domain witness of `Ω`. -/
def tptLabel (p : RawAction × ℕ) : ℕ :=
  ((List.range p.1.1.1.length).filter (fun v => tptSameBlock (p, v))).headD p.2

/-- **The table of labels**, one entry per point of `Ω`. -/
def tptLabels (p : RawAction) : List ℕ :=
  (List.range p.1.1.length).map (fun u => tptLabel (p, u))

/-- Reading an entry of a table built from `List.range`. -/
theorem getD_map_range {α : Type*} (g : ℕ → α) {N u : ℕ} (hu : u < N) (d : α) :
    ((List.range N).map g).getD u d = g u := by
  rw [List.getD_eq_getElem _ _ (by simpa using hu), List.getElem_map, List.getElem_range]

theorem getD_tptLabels {p : RawAction} {u : ℕ} (hu : u < p.1.1.length) :
    (tptLabels p).getD u 0 = tptLabel (p, u) :=
  getD_map_range _ hu 0

/-! ## The specification -/

section Spec

variable {ϕ : genGroup gens →* Perm (Fin m)} {dom gdom : List ℕ}

/-- **Eq. (55) on raw data**: the test decides membership in the standard block. -/
theorem tptSameBlock_eq_true_iff (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK m (Babai.maxOrbitLength (genGroup gens))) (u v : Fin n) :
    tptSameBlock (((((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))) : RawAction),
        (u : ℕ)), (v : ℕ)) = true
      ↔ (v : Fin n) ∈ Babai.standardBlock ϕ u := by
  have hwf : RawGens.WF n (gens.map (encPerm n)) := wf_map_encPerm n gens
  have horb : ((v : ℕ)) ∈ rawOrbit (gens.map (encPerm n), (u : ℕ))
      ↔ v ∈ orbit (genGroup gens) u := by
    rw [mem_rawOrbit_iff hwf u.isLt]
    constructor
    · rintro ⟨h, hv⟩
      rw [decGroup_map_encPerm] at hv
      have he : (⟨(v : ℕ), h⟩ : Fin n) = v := Fin.eta _ _
      have hu : (⟨(u : ℕ), u.isLt⟩ : Fin n) = u := Fin.eta _ _
      rwa [he, hu] at hv
    · intro hv
      refine ⟨v.isLt, ?_⟩
      rw [decGroup_map_encPerm]
      have he : (⟨(v : ℕ), v.isLt⟩ : Fin n) = v := Fin.eta _ _
      have hu : (⟨(u : ℕ), u.isLt⟩ : Fin n) = u := Fin.eta _ _
      rw [he, hu]
      exact hv
  rw [tptSameBlock]
  show (if decide ((v : ℕ) ∈ rawOrbit (gens.map (encPerm n), (u : ℕ))) = true then
      decide (rawTpoint ((((dom, gens.map (encPerm n)),
          (gdom, imgs.map (encPerm m))) : RawAction), (u : ℕ))
        = rawTpoint ((((dom, gens.map (encPerm n)),
          (gdom, imgs.map (encPerm m))) : RawAction), (v : ℕ)))
      else false) = true ↔ _
  rw [Babai.standardBlock, Set.mem_setOf_eq]
  by_cases hmem : ((v : ℕ)) ∈ rawOrbit (gens.map (encPerm n), (u : ℕ))
  · rw [if_pos (by simp [hmem]), decide_eq_true_iff,
      rawTpoint_eq_iff hd hg hI hϕ hk u v]
    constructor
    · intro h
      exact ⟨horb.1 hmem, h.symm⟩
    · rintro ⟨-, h⟩
      exact h.symm
  · rw [if_neg (by simp [hmem])]
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨h, -⟩
    exact hmem (horb.2 h)

/-- The test is symmetric on the points of `Ω`: lying in one standard block is a symmetric
relation. -/
theorem tptSameBlock_symm (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK m (Babai.maxOrbitLength (genGroup gens))) (u v : Fin n)
    (h : tptSameBlock (((((dom, gens.map (encPerm n)),
      (gdom, imgs.map (encPerm m))) : RawAction), (u : ℕ)), (v : ℕ)) = true) :
    tptSameBlock (((((dom, gens.map (encPerm n)),
      (gdom, imgs.map (encPerm m))) : RawAction), (v : ℕ)), (u : ℕ)) = true := by
  rw [tptSameBlock_eq_true_iff hd hg hI hϕ hk] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2.symm⟩
  exact orbit_eq_iff.1 (orbit_eq_iff.2 h1).symm

/-- The test is transitive on the points of `Ω`. -/
theorem tptSameBlock_trans (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK m (Babai.maxOrbitLength (genGroup gens))) (u v w : Fin n)
    (h1 : tptSameBlock (((((dom, gens.map (encPerm n)),
      (gdom, imgs.map (encPerm m))) : RawAction), (u : ℕ)), (v : ℕ)) = true)
    (h2 : tptSameBlock (((((dom, gens.map (encPerm n)),
      (gdom, imgs.map (encPerm m))) : RawAction), (v : ℕ)), (w : ℕ)) = true) :
    tptSameBlock (((((dom, gens.map (encPerm n)),
      (gdom, imgs.map (encPerm m))) : RawAction), (u : ℕ)), (w : ℕ)) = true := by
  rw [tptSameBlock_eq_true_iff hd hg hI hϕ hk] at h1 h2 ⊢
  refine ⟨?_, h2.2.trans h1.2⟩
  have : orbit (genGroup gens) v = orbit (genGroup gens) u := orbit_eq_iff.2 h1.1
  exact this ▸ h2.1

/-- The test holds of a point and itself. -/
theorem tptSameBlock_refl (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK m (Babai.maxOrbitLength (genGroup gens))) (u : Fin n) :
    tptSameBlock (((((dom, gens.map (encPerm n)),
      (gdom, imgs.map (encPerm m))) : RawAction), (u : ℕ)), (u : ℕ)) = true := by
  rw [tptSameBlock_eq_true_iff hd hg hI hϕ hk]
  exact Babai.mem_standardBlock_self ϕ u

/-- The label of a point is a point of its own class: the filtered list is not empty. -/
theorem tptSameBlock_tptLabel (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK m (Babai.maxOrbitLength (genGroup gens))) (u : Fin n) :
    ∃ w : Fin n,
      tptLabel ((((dom, gens.map (encPerm n)),
          (gdom, imgs.map (encPerm m))) : RawAction), (u : ℕ)) = (w : ℕ) ∧
        tptSameBlock (((((dom, gens.map (encPerm n)),
          (gdom, imgs.map (encPerm m))) : RawAction), (u : ℕ)), (w : ℕ)) = true := by
  set p : RawAction × ℕ := ((((dom, gens.map (encPerm n)),
    (gdom, imgs.map (encPerm m))) : RawAction), (u : ℕ)) with hp
  have hself : (u : ℕ) ∈ (List.range p.1.1.1.length).filter
      (fun v => tptSameBlock (p, v)) := by
    refine List.mem_filter.2 ⟨List.mem_range.2 ?_, ?_⟩
    · show (u : ℕ) < dom.length
      rw [hd]; exact u.isLt
    · exact tptSameBlock_refl hd hg hI hϕ hk u
  obtain ⟨a, t, hat⟩ :=
    List.exists_cons_of_ne_nil (List.ne_nil_of_mem hself)
  have hlab : tptLabel p = a := by rw [tptLabel, hat]; rfl
  have hamem : a ∈ (List.range p.1.1.1.length).filter (fun v => tptSameBlock (p, v)) := by
    rw [hat]; exact List.mem_cons_self
  obtain ⟨harange, hatest⟩ := List.mem_filter.1 hamem
  have hpl : p.1.1.1.length = n := by rw [hp]; exact hd
  have han : a < n := by
    rw [← hpl]
    exact List.mem_range.1 harange
  exact ⟨⟨a, han⟩, hlab, hatest⟩

/-- **The labelling is correct**: two points get the same label exactly when one lies in
the standard block of the other. -/
theorem tptLabel_eq_iff (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK m (Babai.maxOrbitLength (genGroup gens))) (u v : Fin n) :
    tptLabel ((((dom, gens.map (encPerm n)),
          (gdom, imgs.map (encPerm m))) : RawAction), (u : ℕ))
        = tptLabel ((((dom, gens.map (encPerm n)),
          (gdom, imgs.map (encPerm m))) : RawAction), (v : ℕ))
      ↔ (v : Fin n) ∈ Babai.standardBlock ϕ u := by
  obtain ⟨wu, hwu, hwut⟩ := tptSameBlock_tptLabel hd hg hI hϕ hk u
  obtain ⟨wv, hwv, hwvt⟩ := tptSameBlock_tptLabel hd hg hI hϕ hk v
  constructor
  · intro heq
    rw [hwu, hwv] at heq
    have hww : wu = wv := Fin.ext heq
    subst hww
    -- `u` and `v` both lie in the class of `wu`
    have h1 : tptSameBlock (((((dom, gens.map (encPerm n)),
        (gdom, imgs.map (encPerm m))) : RawAction), (wu : ℕ)), (v : ℕ)) = true :=
      tptSameBlock_symm hd hg hI hϕ hk v wu hwvt
    have := tptSameBlock_trans hd hg hI hϕ hk u wu v hwut h1
    exact (tptSameBlock_eq_true_iff hd hg hI hϕ hk u v).1 this
  · intro hmem
    have huv : tptSameBlock (((((dom, gens.map (encPerm n)),
        (gdom, imgs.map (encPerm m))) : RawAction), (u : ℕ)), (v : ℕ)) = true :=
      (tptSameBlock_eq_true_iff hd hg hI hϕ hk u v).2 hmem
    have hvu : tptSameBlock (((((dom, gens.map (encPerm n)),
        (gdom, imgs.map (encPerm m))) : RawAction), (v : ℕ)), (u : ℕ)) = true :=
      tptSameBlock_symm hd hg hI hϕ hk u v huv
    -- the two filtered lists agree entry by entry
    have hcongr : ∀ w ∈ List.range dom.length,
        tptSameBlock (((((dom, gens.map (encPerm n)),
            (gdom, imgs.map (encPerm m))) : RawAction), (u : ℕ)), w)
          = tptSameBlock (((((dom, gens.map (encPerm n)),
            (gdom, imgs.map (encPerm m))) : RawAction), (v : ℕ)), w) := by
      intro w hw
      have hwn : w < n := by
        have := List.mem_range.1 hw
        simpa [hd] using this
      have hleft : tptSameBlock (((((dom, gens.map (encPerm n)),
          (gdom, imgs.map (encPerm m))) : RawAction), (u : ℕ)), w) = true →
          tptSameBlock (((((dom, gens.map (encPerm n)),
            (gdom, imgs.map (encPerm m))) : RawAction), (v : ℕ)), w) = true := by
        intro h
        exact tptSameBlock_trans hd hg hI hϕ hk v u ⟨w, hwn⟩ hvu h
      have hright : tptSameBlock (((((dom, gens.map (encPerm n)),
          (gdom, imgs.map (encPerm m))) : RawAction), (v : ℕ)), w) = true →
          tptSameBlock (((((dom, gens.map (encPerm n)),
            (gdom, imgs.map (encPerm m))) : RawAction), (u : ℕ)), w) = true := by
        intro h
        exact tptSameBlock_trans hd hg hI hϕ hk u v ⟨w, hwn⟩ huv h
      rw [Bool.eq_iff_iff]
      exact ⟨hleft, hright⟩
    have hlists : (List.range dom.length).filter
          (fun w => tptSameBlock (((((dom, gens.map (encPerm n)),
            (gdom, imgs.map (encPerm m))) : RawAction), (u : ℕ)), w))
        = (List.range dom.length).filter
          (fun w => tptSameBlock (((((dom, gens.map (encPerm n)),
            (gdom, imgs.map (encPerm m))) : RawAction), (v : ℕ)), w)) :=
      List.filter_congr hcongr
    -- the two lists are equal and not empty, so the two heads agree
    have hne : (List.range dom.length).filter
        (fun w => tptSameBlock (((((dom, gens.map (encPerm n)),
          (gdom, imgs.map (encPerm m))) : RawAction), (u : ℕ)), w)) ≠ [] := by
      refine List.ne_nil_of_mem (a := (u : ℕ)) (List.mem_filter.2 ⟨?_, ?_⟩)
      · exact List.mem_range.2 (by rw [hd]; exact u.isLt)
      · exact tptSameBlock_refl hd hg hI hϕ hk u
    obtain ⟨a, t, hat⟩ := List.exists_cons_of_ne_nil hne
    rw [tptLabel, tptLabel]
    show ((List.range dom.length).filter
        (fun w => tptSameBlock (((((dom, gens.map (encPerm n)),
          (gdom, imgs.map (encPerm m))) : RawAction), (u : ℕ)), w))).headD (u : ℕ)
      = ((List.range dom.length).filter
        (fun w => tptSameBlock (((((dom, gens.map (encPerm n)),
          (gdom, imgs.map (encPerm m))) : RawAction), (v : ℕ)), w))).headD (v : ℕ)
    rw [← hlists, hat]
    rfl

end Spec

/-! ## The running time -/

theorem polyFun_tptSameBlock : PolyFun tptSameBlock := by
  have hcond : PolyFun (fun q : (RawAction × ℕ) × ℕ =>
      decide (q.2 ∈ rawOrbit (q.1.1.1.2, q.1.2))) := by
    have hgs : PolyFun (fun q : (RawAction × ℕ) × ℕ => q.1.1.1.2) :=
      ((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd
    have hu : PolyFun (fun q : (RawAction × ℕ) × ℕ => q.1.2) :=
      polyFun_fst.comp polyFun_snd
    exact (polyFun_snd.pair ((hgs.pair hu).comp polyFun_rawOrbit)).comp polyFun_natListMem
  have hthen : PolyFun (fun q : (RawAction × ℕ) × ℕ =>
      decide (rawTpoint (q.1.1, q.1.2) = rawTpoint (q.1.1, q.2))) := by
    have hp : PolyFun (fun q : (RawAction × ℕ) × ℕ => q.1.1) :=
      polyFun_fst.comp polyFun_fst
    have h1 : PolyFun (fun q : (RawAction × ℕ) × ℕ => rawTpoint (q.1.1, q.1.2)) :=
      (hp.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_rawTpoint
    have h2 : PolyFun (fun q : (RawAction × ℕ) × ℕ => rawTpoint (q.1.1, q.2)) :=
      (hp.pair polyFun_snd).comp polyFun_rawTpoint
    exact (h1.pair h2).comp polyFun_listNatEq
  have hcond' : PolyFun (fun q : (RawAction × ℕ) × ℕ =>
      (decide (q.2 ∈ rawOrbit (q.1.1.1.2, q.1.2)) = true : Bool)) :=
    hcond.of_eq (fun q => by simp)
  exact (PolyFun.ite hcond' hthen (polyFun_const false)).of_eq (fun q => by
    rw [tptSameBlock]
    by_cases h : decide (q.2 ∈ rawOrbit (q.1.1.1.2, q.1.2)) = true <;> simp [h])

theorem polyFun_tptLabel : PolyFun tptLabel := by
  have hrange : PolyFun (fun p : RawAction × ℕ => List.range p.1.1.1.length) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_rangeLength
  have hfil : PolyFun (fun p : RawAction × ℕ =>
      (List.range p.1.1.1.length).filter (fun v => tptSameBlock (p, v))) :=
    ((polyFun_id.pair hrange).comp (PolyFun.filterParam polyFun_tptSameBlock)).of_eq
      (fun _ => rfl)
  have hhead : PolyFun (fun p : RawAction × ℕ =>
      ((List.range p.1.1.1.length).filter (fun v => tptSameBlock (p, v))).head?) :=
    hfil.comp polyFun_headOption
  exact ((hhead.pair polyFun_snd).comp polyFun_optionGetD).of_eq (fun p => by
    rw [tptLabel, List.headD_eq_head?])

theorem polyFun_tptLabels : PolyFun tptLabels := by
  have hrange : PolyFun (fun p : RawAction => List.range p.1.1.length) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_rangeLength
  have hf : PolyFun (fun z : RawAction × ℕ => tptLabel (z.1, z.2)) :=
    (polyFun_fst.pair polyFun_snd).comp polyFun_tptLabel
  exact ((polyFun_id.pair hrange).comp (PolyFun.mapParam hf)).of_eq (fun _ => rfl)

/-! ## Proposition 10.5.4 -/

/-- §10.5, **Proposition 10.5.4**, proved.

Quoted from the paper (version 2.5, lines 4749–4752):

> Finally, and algorithmic observation.
> **Proposition 10.5.4.** Given a giant representation `ϕ : G → S_k`, we can find the
> standard blocks in each `G`-orbit in polynomial time.
> *Proof.* Standard.

This is the statement of the former axiom `Babai.Proposition_10_5_4`, word for word.  The
routine is `Algo.tptLabels`: label a point `u` by the first point of the domain that lies in
the orbit of `u` and has the same `T` (Theorem 10.5.1 (a), computed by `Algo.rawTpoint`).
The module docstring says how each phrase of the paper is read. -/
theorem proposition_10_5_4 :
    ∃ f : (List ℕ × RawGens) × (List ℕ × RawGens) → List ℕ, RAM.PolyFun f ∧
      ∀ (n k : ℕ) (dom gdom : List ℕ) (gens : List (Perm (Fin n)))
        (imgs : List (Perm (Fin k))) (ϕ : genGroup gens →* Perm (Fin k)),
        dom.length = n → gdom.length = k → ImgsOf gens imgs ϕ → Babai.IsGiantRep ϕ →
        Babai.VeryLargeK k (Babai.maxOrbitLength (genGroup gens)) →
        ∀ u v : Fin n,
          (f ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm k)))).getD u 0 =
              (f ((dom, gens.map (encPerm n)),
                (gdom, imgs.map (encPerm k)))).getD v 0 ↔
            v ∈ Babai.standardBlock ϕ u := by
  refine ⟨tptLabels, polyFun_tptLabels, ?_⟩
  intro n k dom gdom gens imgs ϕ hd hg hI hϕ hk u v
  have hu : (u : ℕ) < (((dom, gens.map (encPerm n)),
      (gdom, imgs.map (encPerm k))) : RawAction).1.1.length := by
    show (u : ℕ) < dom.length
    rw [hd]; exact u.isLt
  have hv : (v : ℕ) < (((dom, gens.map (encPerm n)),
      (gdom, imgs.map (encPerm k))) : RawAction).1.1.length := by
    show (v : ℕ) < dom.length
    rw [hd]; exact v.isLt
  rw [getD_tptLabels hu, getD_tptLabels hv]
  exact tptLabel_eq_iff hd hg hI hϕ hk u v

end Algo
