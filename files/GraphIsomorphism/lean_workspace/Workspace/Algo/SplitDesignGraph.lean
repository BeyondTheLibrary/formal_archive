import Workspace.Algo.SplitDesignTie
import Workspace.Algo.SplitBipStep5

/-! # Section 9.7: the graph passed to the next turn

A restriction keeps the selected block names, the original link color,
and the supplied hint. The next initial coloring records both edge directions
and both hint directions, just as Section 9.4 does.
-/
namespace Algo
open Babai RAM

/-- The old case, selected block names, and the new hint table. -/
abbrev RawDesignGraph := (RawUpccCase × List ℕ) × RawConfig

def designGraphParts (z : RawDesignGraph) : List ℕ × List ℕ := (z.1.1.2.1,z.1.2)

def designGraphEdgeTest (z : RawDesignGraph × (ℕ × ℕ)) : Bool :=
  decide (z.2.1 ∈ z.1.1.1.2.1) && decide (z.2.2 ∈ z.1.1.2) &&
    decide (binColor (z.1.1.1.1,z.2) = sbipFirstInvolved z.1.1.1)

def designGraphEdge (z : RawDesignGraph × (ℕ × ℕ)) : ℕ :=
  if designGraphEdgeTest z then 1 else 0

def designGraphVertex (z : RawDesignGraph × ℕ) : ℕ :=
  if decide (z.2 ∈ z.1.1.1.2.1) then Nat.pair 1 (binColor (z.1.1.1.1,(z.2,z.2)))
  else if decide (z.2 ∈ z.1.1.2) then Nat.pair 2 (binColor (z.1.1.1.1,(z.2,z.2))) else 0

def designGraphPair (z : RawDesignGraph × (ℕ × ℕ)) : ℕ :=
  if decide (z.2.1 = z.2.2) then Nat.pair 0 (designGraphVertex (z.1,z.2.1))
  else Nat.pair 1 (Nat.pair
    (Nat.pair (designGraphEdge z) (designGraphEdge (z.1,(z.2.2,z.2.1))))
    (Nat.pair (binColor (z.1.2,z.2)) (binColor (z.1.2,(z.2.2,z.2.1)))))

def designGraphRow (z : RawDesignGraph × List ℕ) : List ℕ × ℕ :=
  (z.2,designGraphPair (z.1,(rawGet (z.2,0),rawGet (z.2,1))))

def designGraphInitial (z : RawDesignGraph) : RawConfig :=
  let l := z.1.1.2.1 ++ z.1.2
  (l,(tuplesOf l 2).map (fun t => designGraphRow (z,t)))

def designGraphRefine (z : RawDesignGraph) : RawConfig :=
  sbipStep3 (sbipIndexed (designGraphInitial z,z.1.1.2.1 ++ z.1.2))

theorem polyFun_designGraphParts : PolyFun designGraphParts :=
  (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst).pair
    (polyFun_fst.comp polyFun_snd)

theorem polyFun_designGraphEdgeTest : PolyFun designGraphEdgeTest := by
  have hr : PolyFun (fun z : RawDesignGraph × (ℕ × ℕ) => z.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have hg : PolyFun (fun z : RawDesignGraph × (ℕ × ℕ) => z.1.1.2) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_snd
  have hl := ((polyFun_snd.comp polyFun_fst).pair
    ((hr.comp polyFun_snd).comp polyFun_fst)).comp polyFun_natListMem
  have hb := ((polyFun_snd.comp polyFun_snd).pair hg).comp polyFun_natListMem
  have hc := (((hr.comp polyFun_fst).pair polyFun_snd).comp polyFun_binColor).natEq
    (hr.comp sbipPoly_firstInvolved)
  exact polyFun_rawJAnd (polyFun_rawJAnd hl hb) hc

theorem polyFun_designGraphEdge : PolyFun designGraphEdge :=
  PolyFun.ite polyFun_designGraphEdgeTest (polyFun_const 1) (polyFun_const 0)

theorem polyFun_designGraphVertex : PolyFun designGraphVertex := by
  have hr : PolyFun (fun z : RawDesignGraph × ℕ => z.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have hg : PolyFun (fun z : RawDesignGraph × ℕ => z.1.1.2) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_snd
  have hl := (polyFun_snd.pair ((hr.comp polyFun_snd).comp polyFun_fst)).comp polyFun_natListMem
  have hb := (polyFun_snd.pair hg).comp polyFun_natListMem
  have hd := ((hr.comp polyFun_fst).pair (polyFun_snd.pair polyFun_snd)).comp polyFun_binColor
  exact PolyFun.ite hl (((polyFun_const 1).pair hd).comp polyFun_upccNatPair)
    (PolyFun.ite hb (((polyFun_const 2).pair hd).comp polyFun_upccNatPair) (polyFun_const 0))

theorem polyFun_designGraphPair : PolyFun designGraphPair := by
  have hu : PolyFun (fun z : RawDesignGraph × (ℕ × ℕ) => z.2.1) := polyFun_snd.comp polyFun_fst
  have hv : PolyFun (fun z : RawDesignGraph × (ℕ × ℕ) => z.2.2) := polyFun_snd.comp polyFun_snd
  have hh : PolyFun (fun z : RawDesignGraph × (ℕ × ℕ) => z.1.2) := polyFun_fst.comp polyFun_snd
  have hf := (polyFun_fst.pair hu).comp polyFun_designGraphVertex
  have he := (polyFun_designGraphEdge.pair
    ((polyFun_fst.pair (hv.pair hu)).comp polyFun_designGraphEdge)).comp polyFun_upccNatPair
  have hhi := (((hh.pair polyFun_snd).comp polyFun_binColor).pair
    ((hh.pair (hv.pair hu)).comp polyFun_binColor)).comp polyFun_upccNatPair
  exact PolyFun.ite (hu.natEq hv) (((polyFun_const 0).pair hf).comp polyFun_upccNatPair)
    (((polyFun_const 1).pair ((he.pair hhi).comp polyFun_upccNatPair)).comp polyFun_upccNatPair)

theorem polyFun_designGraphRow : PolyFun designGraphRow :=
  polyFun_snd.pair ((polyFun_fst.pair
    (((polyFun_snd.pair (polyFun_const 0)).comp polyFun_rawGet).pair
      ((polyFun_snd.pair (polyFun_const 1)).comp polyFun_rawGet))).comp polyFun_designGraphPair)

theorem polyFun_designGraphInitial : PolyFun designGraphInitial := by
  have hl := polyFun_designGraphParts.comp polyFun_append
  exact hl.pair ((polyFun_id.pair (hl.comp ((polyFun_tuplesOf 2).comp polyFun_snd))).comp
    (PolyFun.mapParam polyFun_designGraphRow))

theorem polyFun_designGraphRefine : PolyFun designGraphRefine :=
  ((polyFun_designGraphInitial.pair (polyFun_designGraphParts.comp polyFun_append)).comp
    sbipPoly_indexed).comp sbipPoly_step3

theorem designGraphInitial_get (r : RawDesignGraph) {u v : ℕ}
    (hu : u ∈ r.1.1.2.1 ++ r.1.2) (hv : v ∈ r.1.1.2.1 ++ r.1.2) :
    binColor (designGraphInitial r,(u,v)) = designGraphPair (r,(u,v)) := by
  have ht : [u,v] ∈ tuplesOf (r.1.1.2.1 ++ r.1.2) 2 :=
    (mem_tuplesOf _ _ _).2 ⟨rfl,by simpa using And.intro hu hv⟩
  have hh := congrArg (fun o => o.getD 0) (sbipLookup
    (fun t => designGraphPair (r,(rawGet (t,0),rawGet (t,1)))) _ ht)
  simpa [designGraphInitial,designGraphRow,rawGet,binColor,tblGet] using hh

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
include h

open scoped Classical in
theorem designGraphEdge_spec (g : List ℕ) (hint : RawConfig)
    {S : Set (Set ↥s)}
    (hg : ∀ B : ↥X.blocks, name₂ B ∈ g ↔ B.val ∈ S)
    (x : ↥X.Pt₁) (B : ↥X.blocks) :
    designGraphEdge (((r,g),hint),(name₁ x,name₂ B)) =
      if (x.val,B.val) ∈ (X.linkGraph.restrictBlk S).E then 1 else 0 := by
  have hx : name₁ x ∈ r.2.1 := (h.left _).2 ⟨x,rfl⟩
  simp only [designGraphEdge,designGraphEdgeTest,hx,hg,h.link,designFirst_spec h,
    decide_true,Bool.true_and,Bool.and_eq_true,decide_eq_true_eq]
  have he : B.val ∈ S ∧ X.c {x.val} B.val = X.linkColor ↔
      (x.val,B.val) ∈ (X.linkGraph.restrictBlk S).E := by
    change _ ↔ (X.part₁ x.val ∧ B.val ∈ X.blocks ∧ _) ∧ B.val ∈ S
    exact ⟨fun hh => ⟨⟨x.property,B.property,hh.2⟩,hh.1⟩,fun hh => ⟨hh.2,hh.1.2.2⟩⟩
  simp only [he]

end
end Algo
