import Workspace.Algo.SplitBipDisconnect
import Workspace.Machine.GIRaw

/-!
# Section 9.4: ordered recoding and position tables

Restrictions keep the old names. The mathematical restricted configuration
closes gaps in those names. The first routine does the same finite rank scan.
The second changes vertex names to list positions for the component routine.
Neither scan runs to a number stored in binary.
-/

namespace Algo
open Babai RAM

/-- Looking up a table built from a list of keys. -/
theorem sbipLookup {β : Type*} (f : List ℕ → β) (l : List (List ℕ)) {t : List ℕ}
    (ht : t ∈ l) : (l.map (fun s => (s,f s))).lookup t = some (f t) := by
  have hh := lookup_map_key f (l.map (fun t => (t,0))) t
  simpa [List.map_map,ht] using hh

/-- All realized color names, encoded as singleton strings for `rankIn`. -/
def sbipCodes (p : RawConfig) : List (List ℕ) :=
  dedupG ([],(p.1.product p.1).map (fun q => [binColor (p,q)]))

theorem sbipPoly_codes : PolyFun sbipCodes := by
  have hf : PolyFun (fun z : RawConfig × (ℕ × ℕ) => [binColor z]) :=
    (polyFun_binColor.pair (polyFun_const [])).comp polyFun_cons
  have hm := (polyFun_id.pair
    ((polyFun_fst.pair polyFun_fst).comp GIReduction.polyFun_product)).comp (PolyFun.mapParam hf)
  exact ((polyFun_const []).pair hm).comp (polyFun_dedupG polyFun_listNatEq)

/-- The new name of a table key, using the order of its old integer name. -/
def sbipRecodeRow (z : RawConfig × List ℕ) : List ℕ × ℕ :=
  (z.2,rankIn (sbipCodes z.1,[tblGet (z.1.2,z.2)]))

theorem sbipPoly_recodeRow : PolyFun sbipRecodeRow := by
  have hs : PolyFun (fun z : RawConfig × List ℕ => [tblGet (z.1.2,z.2)] ) :=
    ((((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp polyFun_tblGet).pair
    (polyFun_const [])).comp polyFun_cons
  exact polyFun_snd.pair (((polyFun_fst.comp sbipPoly_codes).pair hs).comp polyFun_rankIn)

/-- Sections 9.4, steps 5–7: close gaps in names, keeping the original order. -/
def sbipRecode (p : RawConfig) : RawConfig :=
  (p.1,(tuplesOf p.1 2).map (fun t => sbipRecodeRow (p,t)))

theorem sbipPoly_recode : PolyFun sbipRecode :=
  polyFun_fst.pair ((polyFun_id.pair
    (polyFun_fst.comp ((polyFun_tuplesOf 2).comp polyFun_snd))).comp
      (PolyFun.mapParam sbipPoly_recodeRow))

theorem sbipRecode_get (p : RawConfig) {u v : ℕ} (hu : u ∈ p.1) (hv : v ∈ p.1) :
    binColor (sbipRecode p,(u,v)) = rankIn (sbipCodes p,[binColor (p,(u,v))]) := by
  have ht : [u,v] ∈ tuplesOf p.1 2 := (mem_tuplesOf _ _ _).2 ⟨rfl,by simpa using And.intro hu hv⟩
  exact congrArg (fun o => o.getD 0) (sbipLookup
    (fun t => rankIn (sbipCodes p,[tblGet (p.2,t)])) _ ht)

/-- The recoding computes `ofNamedColoring` exactly, on any listed carrier. -/
theorem sbipRecode_spec {V : Type*} [Finite V] (p : RawConfig) (name : V → ℕ)
    (hd : ∀ a, a ∈ p.1 ↔ ∃ u, name u = a) (u v : V) :
    binColor (sbipRecode p,(name u,name v)) =
      (PartitionStructure.ofNamedColoring (fun a b => binColor (p,(name a,name b)))).natColor u v := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hs : (sbipCodes p).toFinset = WL.namedCodes (fun a b => binColor (p,(name a,name b))) := by
    ext t
    simp only [List.mem_toFinset,sbipCodes,mem_dedupG_nil,List.mem_map,List.mem_product,
      WL.namedCodes,Finset.mem_image,Finset.mem_univ,true_and,Prod.exists]
    constructor
    · rintro ⟨a,b,hab,ht⟩
      obtain ⟨ha,hb⟩ := List.mem_product.mp hab
      obtain ⟨a',rfl⟩ := (hd a).1 ha
      obtain ⟨b',rfl⟩ := (hd b).1 hb
      exact ⟨a',b',ht⟩
    · rintro ⟨a,b,ht⟩
      exact ⟨name a,name b,List.mem_product.mpr ⟨(hd _).2 ⟨a,rfl⟩,(hd _).2 ⟨b,rfl⟩⟩,ht⟩
  have hnd : (sbipCodes p).Nodup := nodup_dedupG _
  rw [sbipRecode_get p ((hd _).2 ⟨u,rfl⟩) ((hd _).2 ⟨v,rfl⟩),
    namedRank_raw hnd,hs]
  rfl

/-- Pull one tuple back from positions to the supplied vertex names. -/
def sbipIndexRow (z : (RawConfig × List ℕ) × List ℕ) : List ℕ × ℕ :=
  (z.2,tblGet (z.1.1.2,z.2.map (fun i => rawGet (z.1.2,i))))

theorem sbipPoly_indexRow : PolyFun sbipIndexRow := by
  have hm : PolyFun (fun z : (RawConfig × List ℕ) × List ℕ =>
      z.2.map (fun i => rawGet (z.1.2,i))) :=
    ((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp (PolyFun.mapParam polyFun_rawGet)
  exact polyFun_snd.pair ((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).pair hm).comp
    polyFun_tblGet)

/-- A restricted table on positions, with its old vertex names supplied separately. -/
def sbipIndexed (z : RawConfig × List ℕ) : RawConfig :=
  (List.range z.2.length,(tuplesOf (List.range z.2.length) 2).map (fun t => sbipIndexRow (z,t)))

theorem sbipPoly_indexed : PolyFun sbipIndexed := by
  have hd : PolyFun (fun z : RawConfig × List ℕ => List.range z.2.length) :=
    polyFun_snd.comp polyFun_rangeLength
  exact hd.pair ((polyFun_id.pair (hd.comp ((polyFun_tuplesOf 2).comp polyFun_snd))).comp
    (PolyFun.mapParam sbipPoly_indexRow))

@[simp] theorem sbipIndexed_length (p : RawConfig) (l : List ℕ) :
    (sbipIndexed (p,l)).1.length = l.length := List.length_range

theorem sbipIndexed_get (p : RawConfig) (l : List ℕ) (u v : Fin l.length) :
    binColor (sbipIndexed (p,l),(u,v)) = binColor (p,(l[u.val],l[v.val])) := by
  have ht : [u.val,v.val] ∈ tuplesOf (List.range l.length) 2 :=
    (mem_tuplesOf _ _ _).2 ⟨rfl,by simp [u.isLt,v.isLt]⟩
  have hh := congrArg (fun o => o.getD 0) (sbipLookup
    (fun t => tblGet (p.2,t.map (fun i => rawGet (l,i)))) _ ht)
  simpa [sbipIndexed,sbipIndexRow,binColor,tblGet,rawGet,u.isLt,v.isLt] using hh

/-- The position table is structurally valid even if the source table is junk. -/
theorem sbipIndexed_wf (p : RawConfig) (l : List ℕ) : NamedBinaryWF l.length (sbipIndexed (p,l)) := by
  have hk : (sbipIndexed (p,l)).2.map Prod.fst = tuplesOf (List.range l.length) 2 := by
    simp [sbipIndexed,sbipIndexRow,List.map_map,Function.comp_def]
  refine ⟨List.nodup_range,?_,?_,?_⟩
  · intro a; exact List.mem_range
  · rw [hk]; exact nodup_tuplesOf List.nodup_range 2
  · intro t; rw [hk,mem_tuplesOf]; simp only [List.mem_range]

/-- Section 9.4, step 6: first recode the whole restricted configuration,
then read its first part. -/
def sbipStep6Table (z : RawConfig × List ℕ) : RawConfig := sbipIndexed (sbipRecode z.1,z.2)

theorem sbipPoly_step6Table : PolyFun sbipStep6Table :=
  ((polyFun_fst.comp sbipPoly_recode).pair polyFun_snd).comp sbipPoly_indexed

/-- The table prepared for step 6 has exactly the restricted configuration's names.
The map `at` identifies list positions with the dominant points. -/
theorem sbipStep6Table_spec {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) (p : RawConfig) (name : ↥(step5Vtx X) → ℕ)
    (hd : ∀ a, a ∈ p.1 ↔ ∃ A, name A = a)
    (hc : PartitionStructure.ofNamedColoring (fun A B => binColor (p,(name A,name B))) = step5Config X)
    (l : List ℕ) (enum : Fin l.length ≃ ↥(dominantClass X))
    (hl : ∀ i, l[i.val] = name (step5Pt X (enum i))) (u v : Fin l.length) :
    binColor (sbipStep6Table (p,l),(u,v)) = step6Color X (enum u) (enum v) := by
  rw [sbipStep6Table,sbipIndexed_get,hl,hl,sbipRecode_spec p name hd,hc]
  rfl

end Algo
