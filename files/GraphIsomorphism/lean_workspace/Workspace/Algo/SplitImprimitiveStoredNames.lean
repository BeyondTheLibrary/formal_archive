import Workspace.Algo.SplitImprimitiveStoredRaw
import Workspace.Algo.SplitBipVertexDictionary

/-! The incoming finite dictionary is specified by its actual member rows.
The adapter then restores every point and contracted block through that
dictionary. Its claims apply to each actual selected graph, so column range
conditions are proved from the branch enumeration itself.
-/
namespace Algo
open Babai RAM
open scoped Classical

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (X : BlkImprimitiveObj s) (name₁ : ↥X.Pt₁ → ℕ) (name₂ : ↥X.blocks → ℕ)
    (point : ↥s → ℕ) (d : List (List ℕ))

/-- The stored meaning of each incoming compact point and block name. -/
structure ImpStoredNames : Prop where
  points : ∀ x, sbipDictGet (d,name₁ x) = [point x.val]
  blocks : ∀ B a, a ∈ sbipDictGet (d,name₂ B) ↔ ∃ x ∈ B.val, point x = a

/-- The common numbered dictionary supplies the incoming semantic rows. -/
theorem impStoredNames_of_dictionary (e : ↥X.vtxSet ≃ Fin d.length)
    (hd : SbipVertexDictionary X.vtxSet point d e) (hp : Function.Injective point) :
    ImpStoredNames X (fun x => (e (X.vtxOfPt x)).val)
      (fun B => (e (X.vtxOfBlk B)).val) point d := by
  constructor
  · intro x
    rw [sbipDictGet_get]
    exact (sbipVertexDictionary_singleton hd hp (X.vtxOfPt x) x.val).2 rfl
  · intro B a
    rw [sbipDictGet_get]
    exact hd.row_mem (X.vtxOfBlk B) a

variable {X name₁ name₂ point d} {r : RawUpccCase}
    (hn : ImpNames X name₁ name₂ r) (hd : ImpStoredNames X name₁ name₂ point d)

include hd in
theorem impStored_point (x : ↥X.Pt₁) : sbipDictPoint (d,name₁ x) = point x.val :=
  sbipDictPoint_singleton (hd.points x)

include hn hd
/-- A component union is exactly the original-point image of the paper's column. -/
theorem impStored_column {g : List ℕ} (hg : ∀ a ∈ g,a ∈ r.2.2) (u : ℕ) :
    u ∈ sbipDictUnion (d,g) ↔ ∃ x ∈ impColumnSet X name₂ g, point x = u := by
  rw [sbipDictUnion_mem]
  constructor
  · rintro ⟨a,ha,hu⟩
    obtain ⟨B,rfl⟩ := (hn.right a).mp (hg a ha)
    obtain ⟨x,hx,hname⟩ := (hd.blocks B u).mp hu
    exact ⟨x,⟨B,ha,hx⟩,hname⟩
  · rintro ⟨x,⟨B,hB,hx⟩,rfl⟩
    exact ⟨name₂ B,hB,(hd.blocks B (point x)).mpr ⟨x,hx,rfl⟩⟩

/-- Every actual stored column retains its full underlying point set. -/
theorem impStoredGraph_column {q : RawImpGraph} (hq : q ∈ impStep2Graphs r)
    (dom : List ℕ) (i : Fin q.2.1.length) (u : ℕ) :
    u ∈ sbipDictGet ((impStoredGraph ((dom,d),q)).2,dom.length+i) ↔
      ∃ x ∈ impColumnSet X name₂ q.2.1[i.val], point x = u := by
  rw [impStoredGraph_dict]
  exact impStored_column hn hd (fun a ha =>
    impStep2Graphs_column_names hq (List.getElem_mem i.isLt) ha) u

/-- Restoring first-part names keeps exactly the original first-part points. -/
theorem impStoredGraph_points {q : RawImpGraph} (hq : q ∈ impStep2Graphs r)
    (dom : List ℕ) (u : ℕ) :
    u ∈ (impStoredGraph ((dom,d),q)).1.1.1 ↔ ∃ x : ↥X.Pt₁, point x.val = u := by
  rw [impStoredGraph_left,impStep2Graphs_left hq]
  change u ∈ r.2.1.map (fun a => sbipDictPoint (d,a)) ↔ _
  constructor
  · rintro hu
    obtain ⟨a,ha,he⟩ := List.mem_map.mp hu
    obtain ⟨x,rfl⟩ := (hn.left a).mp ha
    exact ⟨x,(impStored_point hd x).symm.trans he⟩
  · rintro ⟨x,rfl⟩
    exact List.mem_map.mpr ⟨name₁ x,(hn.left _).mpr ⟨x,rfl⟩,impStored_point hd x⟩

/-- Distinct first-part positions remain distinct after restoring old names. -/
theorem impStoredGraph_left_nodup {q : RawImpGraph} (hq : q ∈ impStep2Graphs r)
    (dom : List ℕ) (hleft : r.2.1.Nodup) (hp : Function.Injective point) :
    (impStoredGraph ((dom,d),q)).1.1.1.Nodup := by
  rw [impStoredGraph_left,impStep2Graphs_left hq]
  apply hleft.map_on
  intro a ha b hb he
  obtain ⟨x,rfl⟩ := (hn.left a).mp ha
  obtain ⟨y,rfl⟩ := (hn.left b).mp hb
  have hh : point x.val = point y.val := by
    rw [← impStored_point hd x,← impStored_point hd y]
    exact he
  exact congrArg name₁ (Subtype.ext (hp hh))

end
end Algo
