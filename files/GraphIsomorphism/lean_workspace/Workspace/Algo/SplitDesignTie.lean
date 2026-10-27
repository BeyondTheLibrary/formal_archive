import Workspace.Algo.SplitDesignSelect
import Workspace.Algo.NormalizeSI

/-! # Section 9.7: the two-class tie hint

The equal-size twin classes are retained together. The hint colors each
pair as equal, distinct twins, or non-twins, without choosing either class.
-/
namespace Algo
open Babai RAM

def designBlockIndex (z : RawUpccCase × ℕ) : ℕ := rawLetterIndex (z.1.2.2,z.2)

def designTwinHintAt (z : RawUpccCase × (ℕ × ℕ)) : ℕ :=
  if z.2.1 = z.2.2 then 0
  else if splitLabTest (designTwins z.1,
    (designBlockIndex (z.1,z.2.1),designBlockIndex (z.1,z.2.2))) then 1 else 2

def designTwinHintRow (z : RawUpccCase × List ℕ) : List ℕ × ℕ :=
  (z.2,designTwinHintAt (z.1,(rawGet (z.2,0),rawGet (z.2,1))))

def designTwinHint (r : RawUpccCase) : RawConfig :=
  (r.2.2,(tuplesOf r.2.2 2).map (fun t => designTwinHintRow (r,t)))

theorem polyFun_designBlockIndex : PolyFun designBlockIndex :=
  ((((polyFun_fst.comp polyFun_snd).comp polyFun_snd).pair polyFun_snd)).comp polyFun_rawLetterIndex

theorem polyFun_designTwinHintAt : PolyFun designTwinHintAt := by
  have hi : PolyFun (fun z : RawUpccCase × (ℕ × ℕ) => designBlockIndex (z.1,z.2.1)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_designBlockIndex
  have hj : PolyFun (fun z : RawUpccCase × (ℕ × ℕ) => designBlockIndex (z.1,z.2.2)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp polyFun_designBlockIndex
  simpa only [designTwinHintAt, decide_eq_true_eq] using
    PolyFun.ite ((polyFun_snd.comp polyFun_fst).natEq (polyFun_snd.comp polyFun_snd))
    (polyFun_const 0) (PolyFun.ite
      (((polyFun_fst.comp polyFun_designTwins).pair (hi.pair hj)).comp polyFun_splitLabTest)
      (polyFun_const 1) (polyFun_const 2))

theorem polyFun_designTwinHintRow : PolyFun designTwinHintRow :=
  polyFun_snd.pair ((polyFun_fst.pair
    (((polyFun_snd.pair (polyFun_const 0)).comp polyFun_rawGet).pair
      ((polyFun_snd.pair (polyFun_const 1)).comp polyFun_rawGet))).comp polyFun_designTwinHintAt)

theorem polyFun_designTwinHint : PolyFun designTwinHint :=
  (polyFun_snd.comp polyFun_snd).pair
    ((polyFun_id.pair ((polyFun_snd.comp polyFun_snd).comp
      ((polyFun_tuplesOf 2).comp polyFun_snd))).comp (PolyFun.mapParam polyFun_designTwinHintRow))

theorem designTwinHint_get (r : RawUpccCase) {u v : ℕ} (hu : u ∈ r.2.2) (hv : v ∈ r.2.2) :
    binColor (designTwinHint r,(u,v)) = designTwinHintAt (r,(u,v)) := by
  have ht : [u,v] ∈ tuplesOf r.2.2 2 :=
    (mem_tuplesOf _ _ _).2 ⟨rfl,by simpa using And.intro hu hv⟩
  have hh := congrArg (fun o => o.getD 0) (sbipLookup
    (fun t => designTwinHintAt (r,(rawGet (t,0),rawGet (t,1)))) _ ht)
  simpa [designTwinHint,designTwinHintRow,rawGet,binColor,tblGet] using hh

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
include h he₂

theorem designBlockIndex_spec (hnd : r.2.2.Nodup) (B : ↥X.blocks) :
    designBlockIndex (r,name₂ B) = (e₂ B).val := by
  have hh := rawLetterIndex_spec ((h.right _).2 ⟨B,rfl⟩)
  apply (List.Nodup.getElem_inj_iff hnd).1
  rw [he₂]
  exact (List.getD_eq_getElem _ _ hh.1).symm.trans hh.2

include he₁

theorem designTwinHint_spec (hnd : r.2.2.Nodup) (B C : ↥X.blocks) :
    binColor (designTwinHint r,(name₂ B,name₂ C)) = X.twinHint B.val C.val := by
  classical
  rw [designTwinHint_get _ ((h.right _).2 ⟨B,rfl⟩) ((h.right _).2 ⟨C,rfl⟩)]
  have heq : name₂ B = name₂ C ↔ B.val = C.val :=
    ⟨fun hh => congrArg Subtype.val (h.inj₂ hh),fun hh => congrArg name₂ (Subtype.ext hh)⟩
  have ht : splitLabTest (designTwins r,((e₂ B).val,(e₂ C).val)) = true ↔ X.IsHTwin B.val C.val := by
    rw [splitLabTest,decide_eq_true_eq]
    exact designTwins_spec h e₁ he₁ e₂ he₂ B C
  simp only [designTwinHintAt,designBlockIndex_spec h e₂ he₂ hnd,heq,ht,BlkCaseObj.twinHint]

open scoped Classical in
theorem designTie_hint_good (hlt : X.n₂ < X.n₁) (h1 : ¬ X.IsCase1)
    (ht : designTie r = true) :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    (X.linkGraph.restrictBlkHint X.blocks X.twinHint).HasHint := by
  classical
  letI : Fintype ↥s := Fintype.ofFinite _
  letI : DecidableEq ↥s := Classical.decEq _
  exact X.hasHint_twinHint hlt h1 ((designTie_spec h e₁ he₁ e₂ he₂).1 ht)

end
end Algo
