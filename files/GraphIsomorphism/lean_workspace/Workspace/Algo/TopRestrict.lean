/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Sec. 12, the top action restricted to a color class `C ⊆ Γ`.
-/
import Workspace.Algo.TopStab
import Workspace.TopAction.TopAction4

/-!
# Sec. 12: the top action restricted to a color class

The proof of Cor. 12.0.10 passes from the giant representation `ϕ : G → S(Γ)` to the
representation of the setwise stabilizer `G_C` on a color class `C ⊆ Γ`.  This file computes
that representation on the unit-cost RAM.

The routine works inside the **extended group** on `Ω ⊔ Γ` of `Workspace/Algo/Extend.lean`,
where one element carries both a permutation of `Ω` and its `ϕ`-image at once.  That is what
keeps the two output lists aligned, which is what `Algo.ImgsOf` asks for.

* `Algo.topRExt` — generators of `G_C` in the extended group: lifts of the explicit
  generators of `(G^ϕ)_C` of Prop. 12.0.9 (`Algo.topImageStab`), plus generators of the
  kernel of `ϕ`.
* `Algo.topRGens` — the same generators read on `Ω`; this is `Algo.actLiftGens` applied to
  `Algo.topImageStab`, that is `Algo.topStab` before the shortening step.
* `Algo.topRImgs` — the same generators read on `C`, renumbered to `[0, |C|)` by the
  position in the list `C`.
* `Algo.topRAction` — the two lists packaged as action data.

The homomorphism they describe is `Algo.psiCFin`: apply `ϕ`, then restrict to `C`, then
renumber.  It is `Babai.psiC` carried along the labelling of `C` by the list
(`Algo.psiCFin_eq_psiC`).  `Babai.phiCFin` of the paper's proof is the same map read on the
window `Ω(C)` instead of on `Ω`; `Algo.psiCFin_eq_phiC` records the link, which is
`Babai.phiC_restrictHom`.

No axiom, no `sorry`, no `native_decide`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

variable {n m : ℕ}

/-! ## A list whose entries all lie in the image of a map -/

/-- A list all of whose entries are values of `f` is the image of a list. -/
theorem list_eq_map_of_forall_mem {α β : Type*} {f : α → β} {l : List β}
    (h : ∀ b ∈ l, ∃ a, f a = b) : ∃ M : List α, l = M.map f := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons b t ih =>
      obtain ⟨a, ha⟩ := h b (by simp)
      obtain ⟨M, hM⟩ := ih (fun c hc => h c (by simp [hc]))
      exact ⟨a :: M, by rw [List.map_cons, ha, ← hM]⟩

/-! ## The representation `ψ_C` -/

section Psi

variable {gens : List (Perm (Fin n))}

/-- **The representation of `G_C` on `C`, in the labels of the list `C`.**

Apply `ϕ` — the result stabilizes `C` setwise, by the definition of `G_C` — and restrict it
to `C`, where the label of a point is its position in the list `C`.  This is `Babai.psiC`
of the proof of Cor. 12.0.10, read with the labelling the machine uses. -/
noncomputable def psiCFin (ϕ : genGroup gens →* Perm (Fin m)) (C : List ℕ) (hnd : C.Nodup)
    (hlt : ∀ u ∈ C, u < m) :
    Babai.stabOn ϕ (winSet m C) →* Perm (Fin C.length) :=
  (winRestrictHom m C hnd hlt (Babai.setwiseStabilizer ⊤ (winSet m C))
      (Babai.isInvariant_setwiseStabilizer ⊤ (winSet m C))).comp
    (Babai.phiStar ϕ (Babai.setwiseStabilizer ⊤ (winSet m C)))

/-- `ψ_C` is `Babai.psiC` carried along the labelling of `C` by the list. -/
theorem psiCFin_eq_psiC (ϕ : genGroup gens →* Perm (Fin m)) (C : List ℕ) (hnd : C.Nodup)
    (hlt : ∀ u ∈ C, u < m) (g : Babai.stabOn ϕ (winSet m C)) :
    psiCFin ϕ C hnd hlt g =
      (winEquiv m C hnd hlt).symm.permCongr (Babai.psiC ϕ (winSet m C) g) := rfl

/-- The value of `ψ_C` at a point of `C`, read in `Γ`: the point of `C` with the label
`ψ_C(g)(k)` is the `ϕ`-image of the point of `C` with the label `k`. -/
theorem psiCFin_val (ϕ : genGroup gens →* Perm (Fin m)) (C : List ℕ) (hnd : C.Nodup)
    (hlt : ∀ u ∈ C, u < m) (g : Babai.stabOn ϕ (winSet m C)) (k : Fin C.length) :
    C.getD ((psiCFin ϕ C hnd hlt g k : Fin C.length) : ℕ) 0
      = (ϕ ⟨(g : Perm (Fin n)), Babai.stabOn_le ϕ _ g.2⟩
          ((winEquiv m C hnd hlt k : ↥(winSet m C)) : Fin m) : ℕ) :=
  winRestrictHom_val C hnd hlt _ _ k

/-- **`ψ_C` is a giant representation** (the proof of Cor. 12.0.10, the step
"the restriction of `G_C` to `C` includes `A(C)`").

An even permutation of `[0, |C|)` is transported to an even permutation `β` of `C` and
extended by the identity to an even permutation `α` of `Γ`.  Since `ϕ` is giant, some
`g ∈ G` has `ϕ(g) = α`; that `α` fixes `C` setwise, so `g ∈ G_C`, and `ψ_C(g) = δ`. -/
theorem isGiantRep_psiCFin (ϕ : genGroup gens →* Perm (Fin m)) (hϕ : Babai.IsGiantRep ϕ)
    (C : List ℕ) (hnd : C.Nodup) (hlt : ∀ u ∈ C, u < m) :
    Babai.IsGiantRep (psiCFin ϕ C hnd hlt) := by
  classical
  intro δ hδ
  set e := winEquiv m C hnd hlt with he
  set β : Perm ↥(winSet m C) := e.permCongr δ with hβdef
  have hβ : β ∈ alternatingGroup ↥(winSet m C) := by
    rw [Equiv.Perm.mem_alternatingGroup, hβdef, Equiv.Perm.sign_permCongr]
    exact hδ
  set α : Perm (Fin m) := Equiv.Perm.ofSubtype β with hαdef
  have hval : ∀ γ (hγ : γ ∈ winSet m C), α γ = ((β ⟨γ, hγ⟩ : ↥(winSet m C)) : Fin m) :=
    fun γ hγ => Equiv.Perm.ofSubtype_apply_of_mem β hγ
  have hαalt : α ∈ alternatingGroup (Fin m) := by
    rw [Equiv.Perm.mem_alternatingGroup, hαdef, Equiv.Perm.sign_ofSubtype]
    exact hβ
  obtain ⟨g, hg⟩ := hϕ hαalt
  have hsub : α '' winSet m C ⊆ winSet m C := by
    rintro _ ⟨γ, hγ, rfl⟩
    rw [hval γ hγ]
    exact (β ⟨γ, hγ⟩).2
  have himg : α '' winSet m C = winSet m C :=
    Set.eq_of_subset_of_ncard_le hsub
      (le_of_eq (Set.ncard_image_of_injective _ α.injective).symm) (Set.toFinite _)
  have hgmem : (g : Perm (Fin n)) ∈ Babai.stabOn ϕ (winSet m C) :=
    Babai.mem_stabOn.2 ⟨g.2, by
      rw [show (⟨(g : Perm (Fin n)), g.2⟩ : genGroup gens) = g from rfl, hg]; exact himg⟩
  refine ⟨⟨(g : Perm (Fin n)), hgmem⟩, ?_⟩
  refine Equiv.ext fun k => ?_
  have hstep : psiCFin ϕ C hnd hlt ⟨(g : Perm (Fin n)), hgmem⟩ k
      = e.symm ⟨α (e k : ↥(winSet m C)), by
          rw [show α ((e k : ↥(winSet m C)) : Fin m) = _ from hval _ (e k).2]
          exact (β (e k)).2⟩ := by
    refine congrArg e.symm (Subtype.ext ?_)
    show (ϕ ⟨(g : Perm (Fin n)), Babai.stabOn_le ϕ _ hgmem⟩ ((e k : ↥(winSet m C)) : Fin m))
      = α ((e k : ↥(winSet m C)) : Fin m)
    rw [show (⟨(g : Perm (Fin n)), Babai.stabOn_le ϕ _ hgmem⟩ : genGroup gens) = g from rfl, hg]
  rw [hstep]
  have hβval : (⟨α ((e k : ↥(winSet m C)) : Fin m), by
        rw [show α ((e k : ↥(winSet m C)) : Fin m) = _ from hval _ (e k).2]
        exact (β (e k)).2⟩ : ↥(winSet m C)) = β (e k) :=
    Subtype.ext (hval _ (e k).2)
  rw [hβval, hβdef]
  show e.symm (e (δ (e.symm (e k)))) = δ k
  rw [e.symm_apply_apply, e.symm_apply_apply]

/-- §12, **the link to the paper's `ϕ_C`.**  `Babai.phiC` is the representation of the group
that `G_C` induces on the window `Ω(C)`; `ψ_C` is the representation of `G_C` itself.  The
two agree: `ϕ_C` applied to the restriction of `g` to `Ω(C)` is `ψ_C(g)`, up to the labelling
of `C` by the list.  This is `Babai.phiC_restrictHom`.  `Babai.phiCFin` is `Babai.phiC` read
with the labelling `Babai.colorEquivFin` in place of the list's. -/
theorem psiCFin_eq_phiC (ϕ : genGroup gens →* Perm (Fin m)) (hG : Babai.IsTransitive (genGroup gens))
    (hϕ : Babai.IsGiantRep ϕ)
    (hk : Babai.VeryLargeK m (Babai.maxOrbitLength (genGroup gens))) (C : List ℕ)
    (hC : m < 2 * (winSet m C).ncard) (hnd : C.Nodup) (hlt : ∀ u ∈ C, u < m)
    (g : Babai.stabOn ϕ (winSet m C)) :
    psiCFin ϕ C hnd hlt g =
      (winEquiv m C hnd hlt).symm.permCongr
        (Babai.phiC hG ϕ hϕ hk (winSet m C) hC
          ⟨Babai.restrictHom (Babai.stabOn ϕ (winSet m C)) (Babai.omegaOf ϕ (winSet m C))
              (Babai.isInvariant_omegaOf_stabOn ϕ hϕ hk (winSet m C)) g, ⟨g, rfl⟩⟩) := by
  rw [psiCFin_eq_psiC, Babai.phiC_restrictHom]

end Psi

/-! ## The routines -/

/-- **Generators of `G_C` inside the extended group on `Ω ⊔ Γ`.**  The lifts of the explicit
generators of `(G^ϕ)_C` (Prop. 12.0.9, `Algo.topImageStab`), together with generators of
`ker ϕ`.  Every entry is one permutation of `Ω` *together with* its `ϕ`-image. -/
def topRExt (p : RawAction × List ℕ) : RawGens :=
  (topImageStab (p.1.2, p.2)).map (fun r =>
      (rawPreimage ((rawExtDom (p.1.1.1, p.1.2.1), rawExtGens (p.1.1.2, p.1.2.2)),
        (rawExtWin (p.1.1.1, p.1.2.1), r))).getD (rawOne (rawExtDom (p.1.1.1, p.1.2.1))))
    ++ rawKerGens ((rawExtDom (p.1.1.1, p.1.2.1), rawExtGens (p.1.1.2, p.1.2.2)),
        rawExtWin (p.1.1.1, p.1.2.1))

/-- **The generators of `G_C`, read on `Ω`.** -/
def topRGens (p : RawAction × List ℕ) : RawGens :=
  (topRExt p).map (fun r => rawProjPerm (r, p.1.1.1.length))

/-- **The images of those generators on `C`**, renumbered to `[0, |C|)` by the position in
the list `C`. -/
def topRImgs (p : RawAction × List ℕ) : RawGens :=
  (topRExt p).map (fun r =>
    rawRestrictPerm (p.2, rawRestrictPerm (rawExtWin (p.1.1.1, p.1.2.1), r)))

/-- **The restricted action data**: `G_C` on `Ω` with the images of its generators on `C`. -/
def topRAction (p : RawAction × List ℕ) : RawAction :=
  ((p.1.1.1, topRGens p), (rawOne p.2, topRImgs p))

/-! ## `topRGens` is `topStab` without the shortening step -/

/-- The identity on the extended domain, read back on `Ω`, is the identity on `Ω`. -/
theorem rawProjPerm_rawOne_extDom (dom gdom : List ℕ) :
    rawProjPerm (rawOne (rawExtDom (dom, gdom)), dom.length) = rawOne dom := by
  show rowsBefore (List.range (dom ++ gdom).length, dom.length) = List.range dom.length
  rw [rowsBefore_eq_take, List.length_append, List.range_add]
  exact List.take_left' (by simp)

/-- The extended generators of `G_C`, read on `Ω`, are exactly the lifted generators of
`Algo.topStab` before the shortening step. -/
theorem topRGens_eq_actLiftGens (p : RawAction × List ℕ) :
    topRGens p = actLiftGens (p.1, topImageStab (p.1.2, p.2)) := by
  rw [topRGens, topRExt, List.map_append, actLiftGens, List.map_map, actKerGens,
    rawProjGens]
  congr 1
  refine List.map_congr_left fun r _ => ?_
  show rawProjPerm ((rawPreimage _).getD (rawOne (rawExtDom (p.1.1.1, p.1.2.1))),
    p.1.1.1.length) = (actPreimage (p.1, r)).getD (rawOne p.1.1.1)
  rw [actPreimage]
  cases hr : rawPreimage ((rawExtDom (p.1.1.1, p.1.2.1), rawExtGens (p.1.1.2, p.1.2.2)),
      (rawExtWin (p.1.1.1, p.1.2.1), r)) with
  | none => simpa using rawProjPerm_rawOne_extDom p.1.1.1 p.1.2.1
  | some s => rfl

/-! ## The specification -/

section Spec

variable {dom gdom C : List ℕ} {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
  {ϕ : genGroup gens →* Perm (Fin m)}

/-- The extended element `g ⊔ ϕ(g)` of a member of `G_C`. -/
noncomputable def extOfStab (ϕ : genGroup gens →* Perm (Fin m)) (C : List ℕ)
    (g : ↥(Babai.stabOn ϕ (winSet m C))) : Perm (Fin (n + m)) :=
  extPerm n m (g : Perm (Fin n)) (ϕ ⟨(g : Perm (Fin n)), Babai.stabOn_le ϕ _ g.2⟩)

/-- Every entry of `Algo.topRExt` is an extended element `g ⊔ ϕ(g)` with `g ∈ G_C`. -/
theorem topRExt_mem_repr (hd : dom.length = n) (hm : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) {r : RawPerm}
    (hr : r ∈ topRExt (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C)) :
    ∃ g : Babai.stabOn ϕ (winSet m C), encPerm (n + m) (extOfStab ϕ C g) = r := by
  classical
  have hlen : (dom ++ gdom).length = n + m := by simp [hd, hm]
  have hraw : rawExtGens (gens.map (encPerm n), imgs.map (encPerm m))
      = (extGensOf n m gens imgs).map (encPerm (n + m)) := rawExtGens_spec gens imgs hI.1
  have hwin : rawExtWin (dom, gdom) = extWin n m := rawExtWin_eq dom gdom hd hm
  have hwinlen : (extWin n m).length = m := by simp [extWin]
  rw [topRExt] at hr
  rcases List.mem_append.1 hr with h | h
  · -- a lift of a generator of `(G^ϕ)_C`
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
    obtain ⟨s, hs, hts⟩ := (mem_topCandidates hm).1 (List.mem_filter.1 ht).1
    -- `s` stabilizes `C` setwise
    have hsC : s '' winSet m C = winSet m C := by
      rcases hs with hs | ⟨a, b, ha, hb, rfl⟩
      · exact hs.image
      · exact ((Babai.setwiseStabilizer ⊤ (winSet m C)).mul_mem
          ⟨Subgroup.mem_top _, ha.image⟩ ⟨Subgroup.mem_top _, hb.image⟩).2
    have hswf : RawPerm.WF (extWin n m).length (encPerm m s) := by
      simpa [hwinlen] using wf_encPerm m s
    have henc : encPerm (extWin n m).length
        (decPerm (extWin n m).length (encPerm m s)) = encPerm m s := encPerm_decPerm hswf
    show ∃ g : Babai.stabOn ϕ (winSet m C), encPerm (n + m) (extOfStab ϕ C g)
      = (rawPreimage ((rawExtDom (dom, gdom),
        rawExtGens (gens.map (encPerm n), imgs.map (encPerm m))),
        (rawExtWin (dom, gdom), t))).getD (rawOne (rawExtDom (dom, gdom)))
    rw [show rawExtDom (dom, gdom) = dom ++ gdom from rfl, hraw, hwin, hts, ← henc]
    cases hpre : rawPreimage ((dom ++ gdom, (extGensOf n m gens imgs).map (encPerm (n + m))),
        (extWin n m, encPerm (extWin n m).length
          (decPerm (extWin n m).length (encPerm m s)))) with
    | none =>
        refine ⟨1, ?_⟩
        show encPerm (n + m) (extPerm n m 1 (ϕ 1)) = _
        rw [map_one, extPerm_one, Option.getD_none, rawOne_eq, hlen, encPerm_one]
    | some sres =>
        obtain ⟨σ, hσ, hσenc, hσres⟩ := rawPreimage_eq_some hlen (nodup_extWin n m)
          (fun u hu => lt_extWin hu) (isInvariant_extWin hI) hpre
        obtain ⟨a, ha, rfl⟩ := (mem_ext_group_iff hI).1 hσ
        -- the top half of the lift is `s`
        have htop : ϕ ⟨a, ha⟩ = s := by
          have h1 := rawRestrictPerm_spec (n := n + m) (nodup_extWin n m)
            (fun u hu => lt_extWin hu) (isInvariant_extWin hI) hσ
          rw [rawRestrictPerm_extPerm, hσres, henc] at h1
          exact encPerm_injective m h1
        have hamem : a ∈ Babai.stabOn ϕ (winSet m C) :=
          Babai.mem_stabOn.2 ⟨ha, by rw [htop]; exact hsC⟩
        refine ⟨⟨a, hamem⟩, ?_⟩
        rw [Option.getD_some, hσenc]
        rfl
  · -- a generator of `ker ϕ`
    simp only [show rawExtDom (dom, gdom) = dom ++ gdom from rfl, hraw, hwin] at h
    have hwf := wf_rawKerGens hlen (nodup_extWin n m) (fun u hu => lt_extWin hu)
      (extGensOf n m gens imgs)
    have hmem : decPerm (n + m) r ∈ decGroup (n + m)
        (rawKerGens ((dom ++ gdom, (extGensOf n m gens imgs).map (encPerm (n + m))),
          extWin n m)) :=
      Subgroup.subset_closure (List.mem_map.2 ⟨r, h, rfl⟩)
    rw [decGroup_rawKerGens hlen (nodup_extWin n m) (fun u hu => lt_extWin hu)] at hmem
    obtain ⟨a, ha, hrep⟩ := (mem_ext_group_iff hI).1 hmem.1
    have hϕfix : ϕ ⟨a, ha⟩ = 1 := by
      refine Equiv.ext fun γ => ?_
      have hγ : (Fin.natAdd n γ : Fin (n + m)) ∈ {x : Fin (n + m) | (x : ℕ) ∈ extWin n m} :=
        mem_extWinSet.2 ⟨γ, rfl⟩
      have hfix := hmem.2 _ hγ
      rw [hrep, extPerm_natAdd] at hfix
      have hv : ((ϕ ⟨a, ha⟩) γ : ℕ) = (γ : ℕ) := by
        simpa [Fin.natAdd] using congrArg Fin.val hfix
      show (ϕ ⟨a, ha⟩) γ = γ
      exact Fin.ext hv
    have hamem : a ∈ Babai.stabOn ϕ (winSet m C) :=
      Babai.mem_stabOn.2 ⟨ha, by rw [hϕfix]; simp⟩
    refine ⟨⟨a, hamem⟩, ?_⟩
    show encPerm (n + m) (extPerm n m a (ϕ ⟨a, Babai.stabOn_le ϕ _ hamem⟩)) = r
    rw [show (⟨a, Babai.stabOn_le ϕ _ hamem⟩ : genGroup gens) = ⟨a, ha⟩ from rfl, ← hrep,
      encPerm_decPerm (hwf r h)]

/-- **The extended generators of `G_C`, as an explicit list.**  Every entry is `g ⊔ ϕ(g)`
for one `g ∈ G_C`, and the list of those `g` is what the two output lists are read off. -/
theorem topRExt_repr (hd : dom.length = n) (hm : gdom.length = m) (hI : ImgsOf gens imgs ϕ) :
    ∃ M : List ↥(Babai.stabOn ϕ (winSet m C)),
      topRExt (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C) =
        M.map (fun g => encPerm (n + m) (extOfStab ϕ C g)) :=
  list_eq_map_of_forall_mem (fun _ hr => topRExt_mem_repr hd hm hI hr)

/-- The generators of `G_C`, read on `Ω`, are the members of the list of `Algo.topRExt_repr`. -/
theorem topRGens_repr (hd : dom.length = n)
    {M : List ↥(Babai.stabOn ϕ (winSet m C))}
    (hM : topRExt (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C) =
      M.map (fun g => encPerm (n + m) (extOfStab ϕ C g))) :
    topRGens (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C) =
      (M.map (fun g : ↥(Babai.stabOn ϕ (winSet m C)) => (g : Perm (Fin n)))).map (encPerm n) := by
  rw [topRGens, hM, List.map_map, List.map_map]
  refine List.map_congr_left fun g _ => ?_
  show rawProjPerm (encPerm (n + m) (extPerm n m _ _), dom.length) = _
  rw [hd]
  exact rawProjPerm_spec _ _

/-- The images of the generators on `C` are the values of `ψ_C` at those members. -/
theorem topRImgs_repr (hd : dom.length = n) (hm : gdom.length = m)
    (hnd : C.Nodup) (hlt : ∀ u ∈ C, u < m)
    {M : List ↥(Babai.stabOn ϕ (winSet m C))}
    (hM : topRExt (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C) =
      M.map (fun g => encPerm (n + m) (extOfStab ϕ C g))) :
    topRImgs (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C) =
      (M.map (psiCFin ϕ C hnd hlt)).map (encPerm C.length) := by
  rw [topRImgs, hM, List.map_map, List.map_map]
  refine List.map_congr_left fun g _ => ?_
  have hwin : rawExtWin (dom, gdom) = extWin n m := rawExtWin_eq dom gdom hd hm
  show rawRestrictPerm (C, rawRestrictPerm (rawExtWin (dom, gdom),
    encPerm (n + m) (extPerm n m _ _))) = _
  rw [hwin, rawRestrictPerm_extPerm]
  have hmem : ϕ ⟨(g : Perm (Fin n)), Babai.stabOn_le ϕ _ g.2⟩
      ∈ Babai.setwiseStabilizer ⊤ (winSet m C) :=
    ⟨Subgroup.mem_top _, (Babai.mem_stabOn.1 g.2).choose_spec⟩
  rw [rawRestrictPerm_spec hnd hlt
    (Babai.isInvariant_setwiseStabilizer ⊤ (winSet m C)) hmem]
  rfl

/-- **The two output lists, read off one list of elements of `G_C`.**  This is the whole
specification of the routines: the generators on `Ω`, the images on `C`, in the same
order. -/
theorem topRestrict_repr (hd : dom.length = n) (hm : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hnd : C.Nodup) (hlt : ∀ u ∈ C, u < m) :
    ∃ M : List ↥(Babai.stabOn ϕ (winSet m C)),
      topRGens (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C) =
          (M.map (fun g : ↥(Babai.stabOn ϕ (winSet m C)) =>
            (g : Perm (Fin n)))).map (encPerm n) ∧
        topRImgs (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C) =
          (M.map (psiCFin ϕ C hnd hlt)).map (encPerm C.length) := by
  obtain ⟨M, hM⟩ := topRExt_repr (C := C) hd hm hI
  exact ⟨M, topRGens_repr hd hM, topRImgs_repr hd hm hnd hlt hM⟩

/-! ### Well-formedness, the group, and the action data -/

/-- The generators of `G_C` are well-formed permutations of `Ω`. -/
theorem wf_topRGens (hd : dom.length = n) (hm : gdom.length = m) (hI : ImgsOf gens imgs ϕ) :
    RawGens.WF n (topRGens (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C)) := by
  obtain ⟨M, hM⟩ := topRExt_repr (C := C) hd hm hI
  exact (topRGens_repr hd hM) ▸ wf_map_encPerm n _

/-- The images of the generators are well-formed permutations of `[0, |C|)`. -/
theorem wf_topRImgs (hd : dom.length = n) (hm : gdom.length = m) (hI : ImgsOf gens imgs ϕ)
    (hnd : C.Nodup) (hlt : ∀ u ∈ C, u < m) :
    RawGens.WF C.length
      (topRImgs (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C)) := by
  obtain ⟨M, -, h⟩ := topRestrict_repr hd hm hI hnd hlt
  exact h ▸ wf_map_encPerm C.length _

/-- **The generators decode to `G_C`** (Prop. 12.0.9).  This is `Algo.decGroup_topStab`
without the shortening step. -/
theorem decGroup_topRGens (hd : dom.length = n) (hm : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hgiant : Babai.IsGiantRep ϕ) :
    decGroup n (topRGens (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C))
      = Babai.stabOn ϕ (winSet m C) := by
  classical
  set ts := topImageStab ((gdom, imgs.map (encPerm m)), C) with hts_def
  have hts : RawGens.WF m ts := wf_topImageStab hm _
  have htop : decGroup m ts = Babai.setwiseStabilizer ϕ.range (winSet m C) := by
    rw [hts_def, hI.range_eq_genGroup]
    exact decGroup_topImageStab hm imgs (by rw [← hI.range_eq_genGroup]; exact hgiant)
  have hsub : genGroup (ts.map (decPerm m)) ≤ ϕ.range := by
    change decGroup m ts ≤ _
    rw [htop]
    exact fun _ h => h.1
  rw [topRGens_eq_actLiftGens]
  show decGroup n (actLiftGens (((dom, gens.map (encPerm n)),
    (gdom, imgs.map (encPerm m))), ts)) = _
  conv_lhs => rw [← map_encPerm_decPerm hts]
  rw [decGroup_actLiftGens hd hm hI _ hsub]
  change (Subgroup.comap ϕ (decGroup m ts)).map _ = _
  rw [htop, ← Babai.Proposition_12_0_9 ϕ hgiant]
  rfl

/-- **The restricted action data is well formed**, and its image assignment is the
representation `Algo.psiCFin` of `G_C` on `C`.

This is the `Algo.RawAction.WF` statement that the window form of Cor. 12.0.8 asks for: the
group is `G_C`, the second domain has `|C|` points, and the `i`-th image is the value of
`ψ_C` at the `i`-th generator. -/
theorem topRAction_WF (hd : dom.length = n) (hm : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) (hgiant : Babai.IsGiantRep ϕ)
    (hnd : C.Nodup) (hlt : ∀ u ∈ C, u < m) :
    RawAction.WF n C.length
        (topRAction (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C))
      ((psiCFin ϕ C hnd hlt).comp
        (Subgroup.inclusion (le_of_eq (decGroup_topRGens hd hm hI hgiant)))) := by
  classical
  obtain ⟨M, hg, hi⟩ := topRestrict_repr hd hm hI hnd hlt
  have hgd : (topRGens (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C)).map
      (decPerm n) = M.map (fun g : ↥(Babai.stabOn ϕ (winSet m C)) => (g : Perm (Fin n))) := by
    rw [hg, List.map_map]
    simp [Function.comp_def]
  have hid : (topRImgs (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), C)).map
      (decPerm C.length) = M.map (psiCFin ϕ C hnd hlt) := by
    rw [hi, List.map_map]
    simp [Function.comp_def]
  simp only [RawAction.WF, topRAction]
  refine ⟨hd, by simp [rawOne], ?_, ?_, ?_, ?_⟩
  · rw [hg]; exact wf_map_encPerm n _
  · rw [hi]; exact wf_map_encPerm C.length _
  · rw [hgd, hid, List.length_map, List.length_map]
  · intro i hi1 hi2
    have hiM : i < M.length := by
      have h := hi1
      rw [hgd] at h
      simpa using h
    have e1 := List.getElem_of_eq hid hi2
    have e2 := List.getElem_of_eq hgd hi1
    rw [e1, show (M.map (psiCFin ϕ C hnd hlt))[i]'(by simpa using hiM)
        = psiCFin ϕ C hnd hlt (M[i]'hiM) from by simp]
    refine congrArg (psiCFin ϕ C hnd hlt) (Subtype.ext ?_)
    show ((M[i]'hiM : ↥(Babai.stabOn ϕ (winSet m C))) : Perm (Fin n))
      = (List.map (decPerm n) (topRGens (((dom, gens.map (encPerm n)),
          (gdom, imgs.map (encPerm m))), C)))[i]'hi1
    rw [e2]
    simp

end Spec

/-! ## The running time -/

section Poly

private theorem polyFun_extDomOf :
    PolyFun (fun p : RawAction × List ℕ => rawExtDom (p.1.1.1, p.1.2.1)) :=
  (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair
    ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)).comp polyFun_rawExtDom

private theorem polyFun_extGensOf :
    PolyFun (fun p : RawAction × List ℕ => rawExtGens (p.1.1.2, p.1.2.2)) :=
  (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).pair
    ((polyFun_fst.comp polyFun_snd).comp polyFun_snd)).comp polyFun_rawExtGens

private theorem polyFun_extWinOf :
    PolyFun (fun p : RawAction × List ℕ => rawExtWin (p.1.1.1, p.1.2.1)) :=
  (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair
    ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)).comp polyFun_rawExtWin

theorem polyFun_topRExt : PolyFun topRExt := by
  have hpre : PolyFun (fun z : (RawAction × List ℕ) × RawPerm =>
      (rawPreimage ((rawExtDom (z.1.1.1.1, z.1.1.2.1), rawExtGens (z.1.1.1.2, z.1.1.2.2)),
        (rawExtWin (z.1.1.1.1, z.1.1.2.1), z.2))).getD
          (rawOne (rawExtDom (z.1.1.1.1, z.1.1.2.1)))) :=
    (((((polyFun_fst.comp polyFun_extDomOf).pair (polyFun_fst.comp polyFun_extGensOf)).pair
      ((polyFun_fst.comp polyFun_extWinOf).pair polyFun_snd)).comp polyFun_rawPreimage).pair
        ((polyFun_fst.comp polyFun_extDomOf).comp polyFun_rawOne)).comp polyFun_optionGetD
  have hts : PolyFun (fun p : RawAction × List ℕ => topImageStab (p.1.2, p.2)) :=
    ((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp polyFun_topImageStab
  have hmap : PolyFun (fun p : RawAction × List ℕ =>
      (topImageStab (p.1.2, p.2)).map (fun r =>
        (rawPreimage ((rawExtDom (p.1.1.1, p.1.2.1), rawExtGens (p.1.1.2, p.1.2.2)),
          (rawExtWin (p.1.1.1, p.1.2.1), r))).getD
            (rawOne (rawExtDom (p.1.1.1, p.1.2.1))))) :=
    (polyFun_id.pair hts).comp (PolyFun.mapParam hpre)
  have hker : PolyFun (fun p : RawAction × List ℕ =>
      rawKerGens ((rawExtDom (p.1.1.1, p.1.2.1), rawExtGens (p.1.1.2, p.1.2.2)),
        rawExtWin (p.1.1.1, p.1.2.1))) :=
    ((polyFun_extDomOf.pair polyFun_extGensOf).pair polyFun_extWinOf).comp polyFun_rawKerGens
  exact ((hmap.pair hker).comp polyFun_append).of_eq (fun _ => rfl)

theorem polyFun_topRGens : PolyFun topRGens := by
  have h : PolyFun (fun z : ℕ × RawPerm => rawProjPerm (z.2, z.1)) :=
    (polyFun_snd.pair polyFun_fst).comp polyFun_rawProjPerm
  have hn : PolyFun (fun p : RawAction × List ℕ => p.1.1.1.length) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_length
  exact ((hn.pair polyFun_topRExt).comp (PolyFun.mapParam h)).of_eq (fun _ => rfl)

theorem polyFun_topRImgs : PolyFun topRImgs := by
  have h1 : PolyFun (fun z : (List ℕ × List ℕ) × RawPerm =>
      rawRestrictPerm (z.1.2, z.2)) :=
    ((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp polyFun_rawRestrictPerm
  have h : PolyFun (fun z : (List ℕ × List ℕ) × RawPerm =>
      rawRestrictPerm (z.1.1, rawRestrictPerm (z.1.2, z.2))) :=
    ((polyFun_fst.comp polyFun_fst).pair h1).comp polyFun_rawRestrictPerm
  exact (((polyFun_snd.pair polyFun_extWinOf).pair polyFun_topRExt).comp
    (PolyFun.mapParam h)).of_eq (fun _ => rfl)

theorem polyFun_topRAction : PolyFun topRAction :=
  ((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair polyFun_topRGens).pair
    ((polyFun_snd.comp polyFun_rawOne).pair polyFun_topRImgs)).of_eq (fun _ => rfl)

end Poly

end Algo

