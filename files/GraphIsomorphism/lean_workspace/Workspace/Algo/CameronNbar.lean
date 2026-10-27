import Workspace.Algo.CameronRecover
import Workspace.Algo.CameronAxiom

/-!
# Raw generators of the alternating base group

Section 11.2 descends to the alternating base group. We recover the point maps,
compute their signs, and run the action-kernel routine of Proposition 2.2.6.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

/-- A list witnesses the size of the signed coordinate domain on every input. -/
def camSignDom (c : RawCameron) : List ℕ := camCoordDom c ++ camCoordDom c

/-- One entry in the signed permutation table. -/
def camSignAt (p : (RawCameron × RawPerm) × ℕ) : ℕ :=
  (if topEven (camPointPerm (p.1, p.2 / 2)) then p.2 % 2 else 1 - p.2 % 2) +
    2 * (camRecover (p.1, p.2 / 2, 0)).1

/-- Raw images on the two copies of each coordinate. -/
def camSignPerm (p : RawCameron × RawPerm) : RawPerm :=
  (rawOne (camSignDom p.1)).map (fun u => camSignAt (p, u))

/-- Images are kept in the same order as the input generators. -/
def camSignImgs (p : RawCameron × RawGens) : RawGens :=
  p.2.map (fun g => camSignPerm (p.1, g))

/-- The input format of `actKerGens`. -/
def camSignInput (p : RawCameron × RawGens) : RawAction :=
  ((camDom p.1, p.2), (camSignDom p.1, camSignImgs p))

/-- Theorem 11.2.1: compute and shorten generators of the alternating base group. -/
def rawNbar (p : RawCameron × RawGens) : RawGens :=
  tidyGens (camDom p.1, actKerGens (camSignInput p))

theorem camPoly_signDom : PolyFun camSignDom :=
  (camPoly_coordDom.pair camPoly_coordDom).comp polyFun_append

theorem camPoly_signAt : PolyFun camSignAt := by
  have hi : PolyFun (fun p : (RawCameron × RawPerm) × ℕ => p.2 / 2) :=
    polyFun_snd.div (polyFun_const 2)
  have hb : PolyFun (fun p : (RawCameron × RawPerm) × ℕ => p.2 % 2) :=
    polyFun_snd.mod (polyFun_const 2)
  have heven := (polyFun_fst.pair hi).comp camPoly_pointPerm |>.comp polyFun_topEven
  have hcoord := ((polyFun_fst.pair (hi.pair (polyFun_const 0))).comp
    camPoly_recover).comp polyFun_fst
  exact (PolyFun.ite heven hb ((polyFun_const 1).sub hb)).add
    ((polyFun_const 2).mul hcoord)

theorem camPoly_signPerm : PolyFun camSignPerm :=
  (polyFun_id.pair ((polyFun_fst.comp camPoly_signDom).comp polyFun_rawOne)).comp
    (PolyFun.mapParam camPoly_signAt)

theorem camPoly_signImgs : PolyFun camSignImgs := PolyFun.mapParam camPoly_signPerm

theorem camPoly_signInput : PolyFun camSignInput :=
  ((polyFun_fst.comp camPoly_dom).pair polyFun_snd).pair
    ((polyFun_fst.comp camPoly_signDom).pair camPoly_signImgs)

theorem camPoly_rawNbar : PolyFun rawNbar :=
  ((polyFun_fst.comp camPoly_dom).pair (camPoly_signInput.comp polyFun_actKerGens)).comp
    polyFun_tidyGens

theorem camSignDom_length {n : ℕ} {c : RawCameron} (h : c.WF n) :
    (camSignDom c).length = c.s * 2 := by simp [camSignDom, camCoordDom_eq h, Nat.mul_two]

@[simp] theorem camSignNumbering_val {s : ℕ} (x : Fin s × ℤˣ) :
    (camSignNumbering s x).val = (camUnitBit x.2).val + 2 * x.1.val := rfl

theorem camSignNumbering_div {s : ℕ} (x : Fin s × ℤˣ) :
    (camSignNumbering s x).val / 2 = x.1.val := by
  rw [camSignNumbering_val, Nat.add_mul_div_left _ _ (by decide)]
  simp [Nat.div_eq_of_lt (camUnitBit x.2).isLt]

theorem camSignNumbering_mod {s : ℕ} (x : Fin s × ℤˣ) :
    (camSignNumbering s x).val % 2 = (camUnitBit x.2).val := by
  simp [camSignNumbering_val, Nat.mod_eq_of_lt (camUnitBit x.2).isLt]

/-- A raw entry is the signed coordinate action at the same numbered point. -/
theorem camSignAt_spec {n : ℕ} {c : RawCameron} (h : c.WF n)
    (g : Perm (Fin n)) (p : Fin c.s → Perm (Fin c.k)) (σ : Perm (Fin c.s))
    (he : (Equiv.permCongrHom (decCameron c h)) g =
      Babai.wreathPerm (fun i => Babai.tAction c.t (p i)) σ) (x : Fin c.s × ℤˣ) :
    camSignAt ((c, encPerm n g), (camSignNumbering c.s x).val) =
      (camSignNumbering c.s (camSignedPerm p σ x)).val := by
  have hk : 0 < c.k := by have := h.k_gt; omega
  rw [camSignAt, camSignNumbering_div, camSignNumbering_mod,
    camPointPerm_spec h g p σ he x.1,
    camRecover_spec h g p σ he x.1 ⟨0, hk⟩]
  change (if topEven (encPerm c.k (p (σ x.1))) then (camUnitBit x.2).val
    else 1 - (camUnitBit x.2).val) + 2 * (σ x.1).val =
      (camUnitBit ((p (σ x.1)).sign * x.2)).val + 2 * (σ x.1).val
  rw [camUnitBit_mul]
  have hv := (topEven_encPerm (p (σ x.1))).trans Perm.mem_alternatingGroup
  simp only [hv]

/-- The raw signed table is the encoding of the signed permutation. -/
theorem camSignPerm_spec {n : ℕ} {c : RawCameron} (h : c.WF n)
    (g : Perm (Fin n)) (p : Fin c.s → Perm (Fin c.k)) (σ : Perm (Fin c.s))
    (he : (Equiv.permCongrHom (decCameron c h)) g =
      Babai.wreathPerm (fun i => Babai.tAction c.t (p i)) σ) :
    camSignPerm (c, encPerm n g) = encPerm (c.s * 2)
      ((Equiv.permCongrHom (camSignNumbering c.s)) (camSignedPerm p σ)) := by
  have hdom : rawOne (camSignDom c) = List.range (c.s * 2) := by
    change List.range (camSignDom c).length = _
    rw [camSignDom_length h]
  apply List.ext_getElem
  · simp [camSignPerm, hdom]
  · intro u hu hv
    have hus : u < c.s * 2 := by simpa using hv
    change ((rawOne (camSignDom c)).map _)[u] = _
    simp only [hdom, List.getElem_map, List.getElem_range,
      getElem_encPerm (c.s * 2) _ u hus]
    simpa only [Equiv.apply_symm_apply] using
      camSignAt_spec h g p σ he ((camSignNumbering c.s).symm ⟨u, hus⟩)

/-- The computed signed table agrees with the action defined on the whole group. -/
theorem camSignPerm_action {n : ℕ} {c : RawCameron} (h : c.WF n)
    (G : Subgroup (Perm (Fin n)))
    (hhi : G.map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ≤
      Babai.wreathProduct (Babai.JohnsonS c.k c.t) c.s) (g : G) :
    camSignPerm (c, encPerm n g.val) = encPerm (c.s * 2) (camSignActionFin h G hhi g) :=
  camSignPerm_spec h g.val (camWreathPoints (camIntoWreath h G hhi g))
    (camWreathCoords (camIntoWreath h G hhi g))
    (camWreath_decomp (camIntoWreath h G hhi g))

/-- The generator images satisfy the exact input contract of Proposition 2.2.6. -/
theorem camSignImgs_spec {n : ℕ} {c : RawCameron} (h : c.WF n)
    {gs : RawGens} (hw : RawGens.WF n gs)
    (hhi : (decGroup n gs).map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ≤
      Babai.wreathProduct (Babai.JohnsonS c.k c.t) c.s) :
    RawGens.WF (c.s * 2) (camSignImgs (c, gs)) ∧
      ImgsOf (gs.map (decPerm n)) ((camSignImgs (c, gs)).map (decPerm (c.s * 2)))
        (camSignActionFin h (decGroup n gs) hhi) := by
  have he : ∀ (g : RawPerm) (hg : g ∈ gs), camSignPerm (c, g) = encPerm (c.s * 2)
      (camSignActionFin h (decGroup n gs) hhi
        ⟨decPerm n g, Subgroup.subset_closure (List.mem_map_of_mem hg)⟩) := by
    intro g hg
    have hv := camSignPerm_action h (decGroup n gs) hhi
      ⟨decPerm n g, Subgroup.subset_closure (List.mem_map_of_mem hg)⟩
    rwa [encPerm_decPerm (hw g hg)] at hv
  constructor
  · intro r hr
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hr
    rw [he g hg]
    exact wf_encPerm _ _
  · refine ⟨by simp [camSignImgs], ?_⟩
    intro i hi hj
    have hig : i < gs.length := by simpa using hi
    simp only [camSignImgs, List.getElem_map, he gs[i] (List.getElem_mem hig), decPerm_encPerm]
    rfl

/-- The kernel of the computed action is exactly the specified alternating base. -/
theorem camSign_actKer {n : ℕ} {c : RawCameron} (h : c.WF n)
    {gs : RawGens}
    (hlo : Babai.basePower (Babai.JohnsonA c.k c.t) c.s ≤
      (decGroup n gs).map (Equiv.permCongrHom (decCameron c h)).toMonoidHom)
    (hhi : (decGroup n gs).map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ≤
      Babai.wreathProduct (Babai.JohnsonS c.k c.t) c.s) :
    actKer (gs.map (decPerm n)) (camSignActionFin h (decGroup n gs) hhi) = camNbar c h := by
  ext g
  rw [mem_actKer]
  constructor
  · rintro ⟨hg, hv⟩
    exact (camSignActionFin_eq_one h _ hhi ⟨g, hg⟩).1 hv
  · intro hg
    have hG : g ∈ decGroup n gs := (camNbar_normal h _ hlo hhi).le hg
    exact ⟨hG, (camSignActionFin_eq_one h _ hhi ⟨g, hG⟩).2 hg⟩

/-- Theorem 11.2.1: the raw routine returns the alternating base group itself. -/
theorem rawNbar_spec {n : ℕ} {c : RawCameron} (h : c.WF n)
    {gs : RawGens} (hw : RawGens.WF n gs)
    (hlo : Babai.basePower (Babai.JohnsonA c.k c.t) c.s ≤
      (decGroup n gs).map (Equiv.permCongrHom (decCameron c h)).toMonoidHom)
    (hhi : (decGroup n gs).map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ≤
      Babai.wreathProduct (Babai.JohnsonS c.k c.t) c.s) :
    decGroup n (rawNbar (c, gs)) = camNbar c h := by
  obtain ⟨hwi, hI⟩ := camSignImgs_spec h hw hhi
  have hk := decGroup_actKerGens (camDom_length h) (camSignDom_length h) hI
  rw [map_encPerm_decPerm hw, map_encPerm_decPerm hwi] at hk
  rw [rawNbar, decGroup_tidyGens (camDom_length h)]
  exact hk.trans (camSign_actKer h hlo hhi)

/-- Shortening supplies well-formed generators even on raw action data. -/
theorem rawNbar_wf {n : ℕ} {c : RawCameron} (h : c.WF n) (gs : RawGens) :
    RawGens.WF n (rawNbar (c, gs)) := wf_tidyGens (camDom_length h) _

theorem rawNbar_length {n : ℕ} {c : RawCameron} (h : c.WF n) (gs : RawGens) :
    (rawNbar (c, gs)).length ≤ n * n := length_tidyGens (camDom_length h) _

/-- Recognize the table and return its alternating-base generators. -/
def camRecognizeNbar (cameron : RawGens × List ℕ → Option RawCameron)
    (p : RawGens × List ℕ) : Option (RawCameron × RawGens) :=
  (cameron p).map (fun c => (c, rawNbar (c, p.1)))

/-- The output contract includes the containments needed by the descent. -/
def CameronNbarSpec (f : RawGens × List ℕ → Option (RawCameron × RawGens)) : Prop :=
  ∀ (n : ℕ) (gs : RawGens) (dom : List ℕ), dom.length = n → RawGens.WF n gs →
    25 ≤ n → Babai.IsPrimitive (decGroup n gs) →
    (n : ℝ) ^ (1 + Real.logb 2 n) ≤ Nat.card (decGroup n gs) →
    ∃ (c : RawCameron) (h : c.WF n) (ng : RawGens),
      f (gs, dom) = some (c, ng) ∧ RawGens.WF n ng ∧ ng.length ≤ n * n ∧
      decGroup n ng = camNbar c h ∧
      Babai.basePower (Babai.JohnsonA c.k c.t) c.s ≤
        (decGroup n gs).map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ∧
      (decGroup n gs).map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ≤
        Babai.wreathProduct (Babai.JohnsonS c.k c.t) c.s

/-- Theorem 11.2.1, with the supplied recognition routine kept as a parameter. -/
theorem camRecognizeNbar_correct
    (cameron : RawGens × List ℕ → Option RawCameron)
    (hpoly : PolyFun cameron) (hspec : CameronSpec cameron) :
    PolyFun (camRecognizeNbar cameron) ∧ CameronNbarSpec (camRecognizeNbar cameron) := by
  constructor
  · have hf : PolyFun (fun q : RawCameron × (RawGens × List ℕ) =>
        some (q.1, rawNbar (q.1, q.2.1))) :=
      (polyFun_fst.pair ((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp
        camPoly_rawNbar)).comp polyFun_some
    exact ((hpoly.pair polyFun_id).comp (PolyFun.optionElim (polyFun_const none) hf)).of_eq
      (fun p => by unfold camRecognizeNbar; cases cameron p <;> rfl)
  · intro n gs dom hd hw hn hp hb
    obtain ⟨c, h, he, _, hlo, hhi⟩ := hspec n gs dom hd hw hn hp hb
    exact ⟨c, h, rawNbar (c, gs), by simp [camRecognizeNbar, he], rawNbar_wf h gs,
      rawNbar_length h gs, rawNbar_spec h hw hlo hhi, hlo, hhi⟩

/-- Closed form of the alternating-base routine, using only the allowed cited recognition. -/
theorem exists_polyFun_cameronNbarSpec :
    ∃ f : RawGens × List ℕ → Option (RawCameron × RawGens), PolyFun f ∧ CameronNbarSpec f := by
  obtain ⟨cameron, hpoly, hspec⟩ := exists_polyFun_cameronSpec
  exact ⟨camRecognizeNbar cameron, camRecognizeNbar_correct cameron hpoly hspec⟩

end Algo

#print axioms Algo.camPoly_rawNbar
#print axioms Algo.camSignImgs_spec
#print axioms Algo.rawNbar_spec
#print axioms Algo.camRecognizeNbar_correct
#print axioms Algo.exists_polyFun_cameronNbarSpec
