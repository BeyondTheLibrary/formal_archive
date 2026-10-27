/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the Extended Design Lemma (Theorem 9.2.3) for every arity, on a padded
input.
-/
import Workspace.Algo.DesignPadded
import Workspace.Algo.SplitOrJohnsonRAM

/-!
# Theorem 9.2.3 for every arity: the padded family

`Algo.extendedSplitFamily a c t d` (`Workspace/Algo/SplitExtendedRun.lean`) runs the Design
Lemma family of §8 with the arity guard `k ≤ (log₂ n + 1)^a`, and then Theorem 9.2.1 on each
dominant UPCC.  Here the guard is replaced, as in `Workspace/Algo/DesignPadded.lean`, by `n^k`
zeros written next to the input: on the padded input the whole Design Lemma family (every
returning string of the least returning length, with its outcome) is a `RAM.PolyFun`
(`Algo.polyFun_padReadFamily`).  When `k ≤ n` it is the guarded family at the exponent
`a = k` (`Algo.padReadFamily_eq`), so the specification of the guarded family applies
unchanged.

`Algo.extendedSplitAll c t d` is the routine of Theorem 9.2.3 for every arity; it agrees with
`Algo.extendedSplitFamily k c t d` on the same input with the guard witness set to the domain
(`Algo.extendedSplitAll_eq`).  Its running time is proved in
`Workspace/Algo/ExtendedDesignAllRAM.lean`.

No axiom and no `sorry`.
-/

namespace Algo
open Babai RAM RAM.Targets

/-! ## The padded Design Lemma family -/

/-- The input of the procedure of §8 carried by an Extended Design Lemma input: the arity
string, the domain, the relations and the threshold.  The guard witness is dropped. -/
def ambToG (g : AmbientGIn) : GIn := (((g.1.1.1, g.1.1.2.2), g.1.2), g.2)

/-- `n^k` zeros, for `n` the size of the domain and `k` the arity. -/
def ambPad (g : AmbientGIn) : List ℕ := List.replicate (g.1.1.2.2.length ^ g.1.1.1.length) 0

/-- The same input with the guard witness set to the domain. -/
def ambSetBase (g : AmbientGIn) : AmbientGIn := (((g.1.1.1, g.1.1.2.2, g.1.1.2.2), g.1.2), g.2)

/-- The strings of the length of `xs`, from the padded table builder. -/
def padVersionRows (z : (GIn × List ℕ) × List ℕ) : List (List ℕ) :=
  (padTable ((z.1.1.1.1.1.take z.2.length, z.1.1.1.1.2), z.1.2)).2.map Prod.fst

/-- All returning strings of the least returning length, on the padded input. -/
def padVersions (w : GIn × List ℕ) : List (List ℕ) :=
  (padDesignProcedure w).elim [] (fun xs =>
    (padVersionRows (w, xs)).filter (fun ys => returnsB (padDesignAt w ys)))

/-- **The Design Lemma family on the padded input**: each returning string with its outcome
(`Algo.designReadExit`). -/
def padReadFamily (w : GIn × List ℕ) : List (List ℕ × RawDesignReadOut) :=
  (padVersions w).map (fun xs => (xs, designReadExit (padDesignAt w xs)))

theorem polyFun_padVersionRows : PolyFun padVersionRows := by
  have hks : PolyFun (fun z : (GIn × List ℕ) × List ℕ => z.1.1.1.1.1) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst).comp polyFun_fst
  have hdom : PolyFun (fun z : (GIn × List ℕ) × List ℕ => z.1.1.1.1.2) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst).comp polyFun_snd
  have hpad : PolyFun (fun z : (GIn × List ℕ) × List ℕ => z.1.2) := polyFun_fst.comp polyFun_snd
  have htake := (hks.pair (polyFun_snd.comp polyFun_length)).comp polyFun_take
  exact (((htake.pair hdom).pair hpad).comp polyFun_padTable).comp
    (polyFun_snd.comp (PolyFun.map polyFun_fst))

theorem padDesignAt_withStr (w : GIn × List ℕ) (ys : List ℕ) :
    withStr (padDesignAt w [], ys) = padDesignAt w ys := rfl

theorem polyFun_padVersions : PolyFun padVersions := by
  have hVA : PolyFun (fun z : (GIn × List ℕ) × List ℕ =>
      (padVersionRows z).filter (fun ys => returnsB (padDesignAt z.1 ys))) :=
    (((polyFun_fst.comp polyFun_padDesignAt0).pair polyFun_padVersionRows).comp
      (PolyFun.filterParam (polyFun_withStr.comp polyFun_returnsB))).of_eq (fun _ => rfl)
  have hh : PolyFun (fun z : List ℕ × (GIn × List ℕ) =>
      (padVersionRows (z.2, z.1)).filter (fun ys => returnsB (padDesignAt z.2 ys))) :=
    (polyFun_snd.pair polyFun_fst).comp hVA
  refine ((polyFun_padDesignProcedure.pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const []) hh)).of_eq (fun w => ?_)
  unfold padVersions
  cases padDesignProcedure w <;> rfl

theorem polyFun_padReadFamily : PolyFun padReadFamily := by
  have hm : PolyFun (fun z : DIn × List ℕ => (z.2, designReadExit (withStr z))) :=
    polyFun_snd.pair (polyFun_withStr.comp polyFun_designReadExit)
  exact ((polyFun_padDesignAt0.pair polyFun_padVersions).comp (PolyFun.mapParam hm)).of_eq
    (fun _ => rfl)

/-! ## Agreement with the guarded family at the exponent `k` -/

section Agree

variable {g : AmbientGIn}

theorem pow_le_pow_of_le_of_le {n j k : ℕ} (hj : j ≤ k) (hk : k ≤ n) : n ^ j ≤ n ^ k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : k = 0 := by omega
    subst this
    have : j = 0 := by omega
    subst this
    rfl
  · exact Nat.pow_le_pow_right hn hj

theorem ambPad_padOk (hkn : g.1.1.1.length ≤ g.1.1.2.2.length) :
    PadOk g.1.1.1.length g.1.1.2.2.length (ambPad g).length :=
  ⟨hkn, by simp [ambPad]⟩

theorem padPipeline_ambToG (hkn : g.1.1.1.length ≤ g.1.1.2.2.length) :
    padPipeline321 ((ambToG g).1, ambPad g) = ambientPipeline321 g.1.1.1.length (ambSetBase g).1 := by
  have hp := ambPad_padOk hkn
  have e : ambientPipeline321 g.1.1.1.length (ambSetBase g).1 =
      rawPipeline g.1.1.1.length (tupleTable g.1.1.2.2 g.1.1.1.length, g.1.2) :=
    ambientPipeline321_of_guard (c := g.1.1.1.length) (a := (ambSetBase g).1)
      (le_guardBound_self hkn)
  rw [e, padPipeline321, rawPipeline, idxOf, pairIdxOf_eq,
    padMon_of_guard (a := ((ambToG g).1, ambPad g)) hp,
    padTable_of_guard (a := ((ambToG g).1.1, ambPad g)) hp]
  rfl

theorem padDesignAt_ambToG (hkn : g.1.1.1.length ≤ g.1.1.2.2.length) (xs : List ℕ) :
    padDesignAt (ambToG g, ambPad g) xs = ambientDesignAt g.1.1.1.length (ambSetBase g) xs := by
  simp only [padDesignAt, ambientDesignAt]
  rw [padPipeline_ambToG hkn]
  rfl

theorem padDesignProcedure_ambToG (hkn : g.1.1.1.length ≤ g.1.1.2.2.length) :
    padDesignProcedure (ambToG g, ambPad g) =
      ambientDesignProcedure g.1.1.1.length (ambSetBase g) := by
  have hp := ambPad_padOk hkn
  have hr : padScanRounds (padDesignAt (ambToG g, ambPad g) [], ambPad g) = g.1.1.1.length := by
    unfold padScanRounds
    have hd : (padDesignAt (ambToG g, ambPad g) []).1.2.1.length = g.1.1.2.2.length := by
      show (padPipeline321 ((ambToG g).1, ambPad g)).1.length = _
      rw [fst_padPipeline321]; rfl
    rw [hd]
    exact if_pos hp
  have e : ambientDesignProcedure g.1.1.1.length (ambSetBase g) =
      ansUpTo (ambientDesignAt g.1.1.1.length (ambSetBase g) []) g.1.1.1.length :=
    ambientDesignScan_of_guard (c := g.1.1.1.length)
      (a := (g.1.1.2.2, ambientDesignAt g.1.1.1.length (ambSetBase g) []))
      (le_guardBound_self hkn)
  rw [e, padDesignProcedure, padScan_eq, hr, ← padDesignAt_ambToG hkn]

theorem padVersionRows_ambToG (hkn : g.1.1.1.length ≤ g.1.1.2.2.length) (xs : List ℕ) :
    padVersionRows ((ambToG g, ambPad g), xs) =
      ambientDesignVersionRows g.1.1.1.length (ambSetBase g, xs) := by
  have hj : (g.1.1.1.take xs.length).length ≤ g.1.1.1.length := by
    rw [List.length_take]; exact min_le_right _ _
  have hp : PadOk (g.1.1.1.take xs.length).length g.1.1.2.2.length (ambPad g).length :=
    ⟨hj.trans hkn, by simpa [ambPad] using pow_le_pow_of_le_of_le hj hkn⟩
  show (padTable ((g.1.1.1.take xs.length, g.1.1.2.2), ambPad g)).2.map Prod.fst =
    (aggTable g.1.1.1.length (g.1.1.1.take xs.length, g.1.1.2.2, g.1.1.2.2)).2.map Prod.fst
  rw [padTable_of_guard (a := ((g.1.1.1.take xs.length, g.1.1.2.2), ambPad g)) hp,
    aggTable_of_guard (a := (g.1.1.1.take xs.length, g.1.1.2.2, g.1.1.2.2))
      (hj.trans (le_guardBound_self hkn))]

theorem padVersions_ambToG (hkn : g.1.1.1.length ≤ g.1.1.2.2.length) :
    padVersions (ambToG g, ambPad g) = ambientDesignVersions g.1.1.1.length (ambSetBase g) := by
  rw [padVersions, ambientDesignVersions, padDesignProcedure_ambToG hkn]
  generalize ambientDesignProcedure g.1.1.1.length (ambSetBase g) = o
  cases o with
  | none => simp only [Option.elim_none]
  | some xs =>
      simp only [Option.elim_some]
      show (padVersionRows ((ambToG g, ambPad g), xs)).filter
          (fun ys => returnsB (padDesignAt (ambToG g, ambPad g) ys)) =
        (ambientDesignVersionRows g.1.1.1.length (ambSetBase g, xs)).filter
          (fun ys => returnsB (ambientDesignAt g.1.1.1.length (ambSetBase g) ys))
      rw [padVersionRows_ambToG hkn]
      exact List.filter_congr (fun ys _ => by rw [padDesignAt_ambToG hkn])

/-- **On the padded input the family is the guarded family at the exponent `k`**, for `k ≤ n`. -/
theorem padReadFamily_eq (hkn : g.1.1.1.length ≤ g.1.1.2.2.length) :
    padReadFamily (ambToG g, ambPad g) = ambientDesignReadFamily g.1.1.1.length (ambSetBase g) := by
  unfold padReadFamily ambientDesignReadFamily
  rw [padVersions_ambToG hkn]
  refine List.map_congr_left (fun xs _ => ?_)
  rw [designReadAt, padDesignAt_ambToG hkn]

end Agree

/-! ## The routine of Theorem 9.2.3 for every arity -/

/-- **The Extended Design Lemma family for every arity**: the Design Lemma family on the padded
input, then the branch of `Algo.extendedSplitBranch` at each of its outcomes. -/
def extendedSplitAll (c t d : ℕ) (g : AmbientGIn) : List RawAlignOutcome :=
  (padReadFamily (ambToG g, ambPad g)).flatMap (fun o => extendedSplitBranch c t d (g, o.2))

/-- The branch reads only the threshold and the domain of the input. -/
theorem extendedSplitBranch_ambSetBase (c t d : ℕ) (g : AmbientGIn) (o : RawDesignReadOut) :
    extendedSplitBranch c t d (ambSetBase g, o) = extendedSplitBranch c t d (g, o) := rfl

theorem extendedSplitAll_eq {c t d : ℕ} {g : AmbientGIn}
    (hkn : g.1.1.1.length ≤ g.1.1.2.2.length) :
    extendedSplitAll c t d g = extendedSplitFamily g.1.1.1.length c t d (ambSetBase g) := by
  unfold extendedSplitAll extendedSplitFamily
  rw [padReadFamily_eq hkn]
  rfl

/-- **The hypotheses of Theorem 9.2.3** on an input: the domain is `[n]` without repetition,
`3/4 ≤ α < 1` with a positive denominator, `2 ≤ k ≤ n/4`, and the relative strong symmetry defect
exceeds `1 − α`.  This is `Algo.ExtendedInputRep` without the arity guard. -/
structure ExtendedInput (n : ℕ) (g : AmbientGIn) : Prop where
  nodup : g.1.1.2.2.Nodup
  domain : ∀ i, i ∈ g.1.1.2.2 ↔ i < n
  denominator : 0 < g.2.2
  lower : (3 : ℝ) / 4 ≤ sbipAlphaValue g.2
  upper : sbipAlphaValue g.2 < 1
  two : 2 ≤ g.1.1.1.length
  arity : 4 * g.1.1.1.length ≤ n
  defect : 1 - sbipAlphaValue g.2 < (defect (decRel n g.1.1.1.length g.1.2).Aut : ℝ)

namespace ExtendedInput

variable {n : ℕ} {g : AmbientGIn}

theorem length_dom (h : ExtendedInput n g) : g.1.1.2.2.length = n :=
  length_eq_of_nodup_mem h.nodup h.domain

theorem arity_le (h : ExtendedInput n g) : g.1.1.1.length ≤ g.1.1.2.2.length := by
  have h1 := h.arity; rw [h.length_dom]; omega

/-- With the guard witness set to the domain, the input satisfies the guarded hypotheses at the
exponent `k`. -/
theorem toRep (h : ExtendedInput n g) : ExtendedInputRep g.1.1.1.length n (ambSetBase g) where
  nodup := h.nodup
  domain := h.domain
  guard := le_guardBound_self h.arity_le
  denominator := h.denominator
  lower := h.lower
  upper := h.upper
  two := h.two
  arity := h.arity
  defect := h.defect

end ExtendedInput

/-- **Theorem 9.2.3, validity and canonicity, for every arity.**  For one choice of bounds, on
every input satisfying the hypotheses of the theorem the family is nonempty and each member is an
outcome (a) or (b); and an isomorphism of two such inputs with the same arity string, domain and
threshold carries every member of the first family to a member of the second. -/
theorem exists_extendedSplitAll_valid_canonical (c : ℕ) :
    ∃ t d, BipInputRunCanonical c t d ∧
      (∀ n g, ExtendedInput n g →
        (∃ p, p ∈ extendedSplitAll c t d g) ∧
        ∀ p ∈ extendedSplitAll c t d g, ∃ Z, decAlignOutcome n p = some Z ∧
          IsSplitOutcome (sbipAlphaValue g.2) Set.univ Z) ∧
      (∀ n (g g' : AmbientGIn), ExtendedInput n g → ExtendedInput n g' →
        g.1.1.1 = g'.1.1.1 → g.1.1.2.2 = g'.1.1.2.2 → g.2 = g'.2 →
        ∀ f : Equiv.Perm (Fin n),
        f ∈ KAryRelStruct.Iso (decRel n g.1.1.1.length g.1.2) (decRel n g.1.1.1.length g'.1.2) →
        ∀ p ∈ extendedSplitAll c t d g, ∃ p' ∈ extendedSplitAll c t d g',
          RawSplitOutcomeIso n f p p') := by
  obtain ⟨t, d, hcan, hall⟩ := exists_extendedSplitFamily_valid_canonical c
  refine ⟨t, d, hcan, fun n g h => ?_, fun n g g' h h' hk hd hα f hf p hp => ?_⟩
  · rw [extendedSplitAll_eq h.arity_le]
    exact (hall g.1.1.1.length).2.1 n _ h.toRep
  · rw [extendedSplitAll_eq h.arity_le] at hp
    have hkk : g.1.1.1.length = g'.1.1.1.length := by rw [hk]
    have h1 : (ambSetBase g).1.1 = (ambSetBase g').1.1 := by
      simp only [ambSetBase, hk, hd]
    have hrep' : ExtendedInputRep g.1.1.1.length n (ambSetBase g') := by
      have := h'.toRep; rwa [← hkk] at this
    obtain ⟨p', hp', hiso⟩ := (hall g.1.1.1.length).2.2 n _ _ h.toRep hrep' h1 hα f hf p hp
    refine ⟨p', ?_, hiso⟩
    rw [extendedSplitAll_eq h'.arity_le, ← hkk]
    exact hp'

end Algo
