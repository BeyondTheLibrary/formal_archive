import Workspace.Algo.DesignReadPartition
import Workspace.Algo.SplitDesignRun

/-! # Full stored outcomes at the Design Lemma's returning tuples

A disconnected constituent returns the component partition. Otherwise a
non-clique binary configuration returns its dominant UPCC. The remaining
exit retains the vertex-color partition. The full returning family uses
these same computations for each tuple.
-/
namespace Algo
open Babai RAM

/-- A partition of the whole domain, or a configuration with its old vertex names. -/
abbrev RawDesignReadOut := Option RawColPart × (List ℕ × Option RawConfig)

def designReadHasSkeleton (z : DIn) : Bool := decide (z.1.1.2.length + 2 ≤ z.1.1.1.length)

def designReadHasComponents (z : DIn) : Bool :=
  designReadHasSkeleton z && sbipImprimitive (designDomPairs z)

def designReadHasUpcc (z : DIn) : Bool :=
  designReadHasSkeleton z && decide (2 < cliqueRank z)

def designReadPartitionExit (p : RawColPart) : RawDesignReadOut := (some p,[],none)

def designReadUpccTable (z : DIn) : RawConfig := sbipRecode (designDomPairs z)

def designReadUpccExit (z : DIn) : RawDesignReadOut := (none,dominantList z,some (designReadUpccTable z))

def designReadExit (z : DIn) : RawDesignReadOut :=
  if designReadHasComponents z then designReadPartitionExit (designReadPart z)
  else if designReadHasUpcc z then designReadUpccExit z
  else designReadPartitionExit (designReadPlain z)

theorem polyFun_designReadHasSkeleton : PolyFun designReadHasSkeleton :=
  (((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_length).add (polyFun_const 2)).le
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_length))

theorem polyFun_designReadHasComponents : PolyFun designReadHasComponents :=
  polyFun_rawJAnd polyFun_designReadHasSkeleton (polyFun_designDomPairs.comp sbipPoly_imprimitive)

theorem polyFun_designReadHasUpcc : PolyFun designReadHasUpcc :=
  polyFun_rawJAnd polyFun_designReadHasSkeleton ((polyFun_const 3).le polyFun_cliqueRank)

theorem polyFun_designReadPartitionExit : PolyFun designReadPartitionExit :=
  polyFun_some.pair ((polyFun_const []).pair (polyFun_const none))

theorem polyFun_designReadUpccTable : PolyFun designReadUpccTable :=
  polyFun_designDomPairs.comp sbipPoly_recode

theorem polyFun_designReadUpccExit : PolyFun designReadUpccExit :=
  (polyFun_const none).pair (polyFun_dominantList.pair (polyFun_designReadUpccTable.comp polyFun_some))

theorem polyFun_designReadExit : PolyFun designReadExit :=
  PolyFun.ite polyFun_designReadHasComponents
    (polyFun_designReadPart.comp polyFun_designReadPartitionExit)
    (PolyFun.ite polyFun_designReadHasUpcc polyFun_designReadUpccExit
      (polyFun_designReadPlain.comp polyFun_designReadPartitionExit))

/-- Every returned partition has a label for each vertex. -/
theorem designReadExit_partition_wf {z : DIn} {P : RawColPart}
    (hp : (designReadExit z).1 = some P) : P.WF z.1.2.1.length := by
  unfold designReadExit at hp
  split at hp
  · have he : designReadPart z = P := Option.some.inj hp
    rw [← he]
    exact designReadPart_wf z
  · split at hp
    · simp [designReadUpccExit] at hp
    · have he : designReadPlain z = P := Option.some.inj hp
      rw [← he]
      exact designReadPlain_wf z

theorem designReadExit_partition_eq {z : DIn} {P : RawColPart}
    (hp : (designReadExit z).1 = some P) :
    designReadExit z = designReadPartitionExit P := by
  unfold designReadExit at hp ⊢
  split at hp
  · rename_i hc
    rw [if_pos hc,Option.some.inj hp]
  · rename_i hc
    rw [if_neg hc]
    split at hp
    · simp [designReadUpccExit] at hp
    · rename_i hu
      rw [if_neg hu,Option.some.inj hp]

theorem designReadExit_of_none {z : DIn} (hp : (designReadExit z).1 = none) :
    ∃ l q, designReadExit z = (none,l,some q) := by
  unfold designReadExit at hp ⊢
  split at hp
  · simp [designReadPartitionExit] at hp
  · rename_i hc
    rw [if_neg hc]
    split at hp
    · rename_i hu
      exact ⟨_,_,if_pos hu⟩
    · simp [designReadPartitionExit] at hp

/-- The configuration exit retains exactly the computed dominant names and pair table. -/
theorem designReadExit_upcc {z : DIn} {p : RawConfig}
    (hp : (designReadExit z).2.2 = some p) :
    designReadHasComponents z = false ∧ designReadHasUpcc z = true ∧
      (designReadExit z).2.1 = dominantList z ∧ p = designReadUpccTable z := by
  unfold designReadExit at hp ⊢
  split at hp
  · simp [designReadPartitionExit] at hp
  · rename_i hn
    split at hp
    · rename_i hu
      refine ⟨Bool.eq_false_iff.2 hn,hu,?_,(Option.some.inj hp).symm⟩
      simp only [if_neg hn,if_pos hu,designReadUpccExit]
    · simp [designReadPartitionExit] at hp

/-- Preserve the returning tuple alongside its fully computed output. -/
def ambientDesignReadFamily (c : ℕ) (g : AmbientGIn) : List (List ℕ × RawDesignReadOut) :=
  (ambientDesignVersions c g).map (fun xs => (xs,designReadExit
    (withStr (ambientDesignAt c g [],xs))))

def designCallReadFamily (r : RawUpccCase) : List (List ℕ × RawDesignReadOut) :=
  ambientDesignReadFamily 3 (designCallGIn r)

theorem quasiFun_ambientDesignReadFamily (c : ℕ) : QuasiFun (ambientDesignReadFamily c) := by
  have hm : PolyFun (fun z : DIn × List ℕ => (z.2,designReadExit (withStr z))) :=
    polyFun_snd.pair (polyFun_withStr.comp polyFun_designReadExit)
  exact ((quasiFun_ambientDesignAt c).pair (quasiFun_ambientDesignVersions c)).comp_poly
    (PolyFun.mapParam hm)

theorem quasiFun_designCallReadFamily : QuasiFun designCallReadFamily :=
  quasiFun_designCallGIn.comp (quasiFun_ambientDesignReadFamily 3)

theorem designReadAt (c : ℕ) (g : AmbientGIn) (xs : List ℕ) :
    withStr (ambientDesignAt c g [],xs) = ambientDesignAt c g xs := rfl

theorem designCallReadFamily_length (r : RawUpccCase) :
    (designCallReadFamily r).length = (designCallVersions r).length := by simp [designCallReadFamily,ambientDesignReadFamily,designCallVersions]

theorem designCallReadFamily_mem (r : RawUpccCase) (xs : List ℕ) (o : RawDesignReadOut) :
    (xs,o) ∈ designCallReadFamily r ↔ xs ∈ designCallVersions r ∧
      o = designReadExit (ambientDesignAt 3 (designCallGIn r) xs) := by
  simp only [designCallReadFamily,ambientDesignReadFamily,designReadAt,List.mem_map,Prod.mk.injEq]
  change (∃ ys ∈ designCallVersions r, ys = xs ∧ _ = o) ↔ _
  constructor
  · rintro ⟨ys,hy,he,ho⟩; subst ys; exact ⟨hy,ho.symm⟩
  · rintro ⟨hx,rfl⟩; exact ⟨xs,hx,rfl,rfl⟩

end Algo
