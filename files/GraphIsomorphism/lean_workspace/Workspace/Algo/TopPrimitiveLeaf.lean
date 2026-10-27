import Workspace.Algo.AlignG1
import Workspace.Algo.AlignParity
import Workspace.Algo.TopWindowRound
import Workspace.Master.Hypergraph
import Workspace.Coherent.JohnsonCliques

/-! # The direct answer in Section 15, line 4a
For `t = 1` the primitive action contains the alternating group on the
string positions. The color classes give its string stabilizer. The
partition isomorphism routine also checks parity, as required by the
recorded correction to the paper's multiplicity parenthesis.
-/
namespace Algo
set_option maxHeartbeats 1000000
open RAM RAM.Targets Babai Equiv
open scoped Classical Pointwise

def primitiveLeafAction (p : RawSI) : RawAction :=
  ((p.2.1, p.1), (p.2.1, p.1))
def primitiveLeafPerm (p : RawSI) : Option RawPerm :=
  alignColPartIso (topAllEven (primitiveLeafAction p), ((p.2.1, []), (p.2.2, [])))
def primitiveLeafAut (p : RawSI) : RawGens :=
  alignAutGens (primitiveLeafAction p, (p.2.1, []))
def primitiveLeaf (p : RawSI) : RawCoset :=
  top2NormC p.2.1 ((primitiveLeafPerm p).map (fun r => (primitiveLeafAut p, r)))

theorem colPartIso_string (n : ℕ) (x y : RawStr) (r : Perm (Fin n)) :
    ColPartIso n (x, []) (y, []) r ↔ strAct (decStrN n x) r = decStrN n y := by
  rw [strAct_eq_iff]
  constructor
  · exact fun h u => (h.1 u).symm
  · intro h
    refine ⟨fun u => (h u).symm, fun u v => ?_⟩
    change (x.getD u.val 0, ([] : List ℕ).getD u.val 0) =
      (x.getD v.val 0, ([] : List ℕ).getD v.val 0) ↔
      (y.getD (r u).val 0, ([] : List ℕ).getD (r u).val 0) =
      (y.getD (r v).val 0, ([] : List ℕ).getD (r v).val 0)
    simpa only [List.getD_nil, Prod.mk.injEq, and_true] using
      (show decStrN n x u = decStrN n x v ↔ decStrN n y (r u) = decStrN n y (r v) by
        rw [h u, h v])

theorem primitiveLeaf_even {n : ℕ} {p : RawSI} (hgs : RawGens.WF n p.1) :
    topAllEven (primitiveLeafAction p) = true ↔ decGroup n p.1 ≤ alternatingGroup (Fin n) := by
  have hI : ImgsOf (p.1.map (decPerm n)) (p.1.map (decPerm n))
      (decGroup n p.1).subtype := ⟨rfl, fun _ _ _ => rfl⟩
  have h := topAllEven_spec p.2.1 p.2.1 hI
  change topAllEven _ = true ↔ (decGroup n p.1).subtype.range ≤ alternatingGroup (Fin n) at h
  rw [Subgroup.range_subtype] at h
  simpa only [map_encPerm_decPerm hgs, primitiveLeafAction,
    Subgroup.range_subtype] using h

theorem primitiveLeaf_aut {n : ℕ} {p : RawSI} (hgs : RawGens.WF n p.1)
    (hx : p.2.1.length = n) (hgiant : alternatingGroup (Fin n) ≤ decGroup n p.1) :
    (decGroup n (primitiveLeafAut p) : Set (Perm (Fin n))) =
      strAut (decGroup n p.1 : Set (Perm (Fin n))) (decStrN n p.2.1) := by
  have hI : ImgsOf (p.1.map (decPerm n)) (p.1.map (decPerm n))
      (decGroup n p.1).subtype := ⟨rfl, fun _ _ _ => rfl⟩
  have hg : IsGiantRep (decGroup n p.1).subtype := by
    simpa only [IsGiantRep, Subgroup.range_subtype] using hgiant
  have h := decGroup_alignAutGens (dom := p.2.1) (gdom := p.2.1) hI hg (P := (p.2.1, [])) hx
  change decGroup n _ = _ ⊓ (decGroup n p.1).subtype.range at h
  rw [Subgroup.range_subtype] at h
  simp only [map_encPerm_decPerm hgs] at h
  change (↑(decGroup n (alignAutGens _)) : Set (Perm (Fin n))) = _
  unfold primitiveLeafAction
  rw [h]
  ext r
  change (r ∈ structAut (decColStruct n (p.2.1, [])) ∧ r ∈ decGroup n p.1) ↔
    (r ∈ decGroup n p.1 ∧ strAct (decStrN n p.2.1) r = decStrN n p.2.1)
  rw [mem_structAut, ← colPartIso_iff_smul, colPartIso_string]
  exact and_comm

theorem primitiveLeaf_spec {n : ℕ} {p : RawSI} (hgs : RawGens.WF n p.1)
    (hx : p.2.1.length = n) (hy : p.2.2.length = n)
    (hgiant : alternatingGroup (Fin n) ≤ decGroup n p.1) :
    decCoset n (primitiveLeaf p) =
      strIso (decGroup n p.1 : Set (Perm (Fin n))) (decStrN n p.2.1) (decStrN n p.2.2) := by
  rw [primitiveLeaf, decCoset_top2NormC hx]
  cases hr : primitiveLeafPerm p with
  | none =>
    simp only [Option.map_none, decCoset]
    symm
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro r ⟨hg, hi⟩
    obtain ⟨he, ho⟩ := alignColPartIso_eq_none (P := (p.2.1, [])) (Q := (p.2.2, []))
      (g := topAllEven (primitiveLeafAction p)) hx hy hr r ((colPartIso_string _ _ _ _).mpr hi)
    have ha := (primitiveLeaf_even hgs).mp he hg
    rw [Equiv.Perm.mem_alternatingGroup.mp ha] at ho
    exact (by decide : (1 : ℤˣ) ≠ -1) ho
  | some r =>
    obtain ⟨_, hi, he⟩ := alignColPartIso_some (P := (p.2.1, [])) (Q := (p.2.2, []))
      (g := topAllEven (primitiveLeafAction p)) hx hy hr
    have hg : decPerm n r ∈ decGroup n p.1 := by
      by_cases ha : topAllEven (primitiveLeafAction p) = true
      · exact hgiant (Equiv.Perm.mem_alternatingGroup.mpr (he ha))
      · rcases (isGiant_iff_alternating_le (decGroup n p.1)).mpr hgiant with ht | ht
        · rw [ht]; trivial
        · exact (ha ((primitiveLeaf_even hgs).mpr ht.le)).elim
    rw [Option.map_some, decCoset_some, primitiveLeaf_aut hgs hx hgiant]
    exact (strIso_eq_smul_strAut ⟨hg, (colPartIso_string _ _ _ _).mp hi⟩).symm

theorem polyFun_primitiveLeafAction : PolyFun primitiveLeafAction :=
  ((polyFun_snd.comp polyFun_fst).pair polyFun_fst).pair
    ((polyFun_snd.comp polyFun_fst).pair polyFun_fst)
theorem polyFun_primitiveLeafPerm : PolyFun primitiveLeafPerm :=
  ((polyFun_primitiveLeafAction.comp polyFun_topAllEven).pair
    (((polyFun_snd.comp polyFun_fst).pair (polyFun_const [])).pair
      ((polyFun_snd.comp polyFun_snd).pair (polyFun_const [])))).comp polyFun_alignColPartIso
theorem polyFun_primitiveLeafAut : PolyFun primitiveLeafAut :=
  (polyFun_primitiveLeafAction.pair
    ((polyFun_snd.comp polyFun_fst).pair (polyFun_const []))).comp polyFun_alignAutGens
theorem polyFun_primitiveLeaf : PolyFun primitiveLeaf := by
  have hm : PolyFun (fun p : RawSI =>
      (primitiveLeafPerm p).map (fun r => (primitiveLeafAut p, r))) :=
    ((polyFun_primitiveLeafPerm.pair polyFun_primitiveLeafAut).comp
      (PolyFun.optionElim (polyFun_const none)
        ((polyFun_snd.pair polyFun_fst).comp polyFun_some))).of_eq
      (fun p => by cases primitiveLeafPerm p <;> rfl)
  exact ((polyFun_snd.comp polyFun_fst).pair hm).comp polyFun_top2NormC

theorem primitiveLeaf_size (p : RawSI) : Enc.size (primitiveLeaf p) ≤ chainBound p.2.1.length :=
  size_top2NormC_le rfl le_rfl _

section Primitive
variable {Ω Γ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
    {G : Subgroup (Perm Ω)} {ϕ : G →* Perm Γ}

/-- The singleton labels of Theorem 10.5.1 identify the source action with
the giant action on `Γ`. Thus the direct leaf's group hypothesis follows
from line 4a's actual test. -/
theorem primitiveCase_one_giant (id : PrimitiveCaseId ϕ 1) (hϕ : IsGiantRep ϕ) :
    alternatingGroup Ω ≤ G := by
  let e : Ω ≃ Γ := id.label.trans (Johnson.oneEquiv Γ).symm
  have he (g : G) (u : Ω) : e ((g : Perm Ω) u) = ϕ g (e u) := by
    apply (Johnson.oneEquiv Γ).injective
    have hleft : Johnson.oneEquiv Γ (e ((g : Perm Ω) u)) = id.label ((g : Perm Ω) u) := by
      simp [e]
    rw [hleft, id.equivariant]
    apply Subtype.ext
    rw [tAction_apply_coe]
    have hu : (id.label u : Finset Γ) = {e u} := by
      have hh : Johnson.oneEquiv Γ (e u) = id.label u := by simp [e]
      exact (congrArg Subtype.val hh).symm
    rw [hu, Finset.image_singleton, Johnson.oneEquiv_apply]
  intro a ha
  have hga : e.permCongr a ∈ alternatingGroup Γ := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_permCongr]
    exact Equiv.Perm.mem_alternatingGroup.mp ha
  obtain ⟨g, hg⟩ := hϕ hga
  have hEq : (g : Perm Ω) = a := by
    ext u
    apply e.injective
    rw [he, hg]
    simp
  exact hEq ▸ g.property

end Primitive
end Algo
