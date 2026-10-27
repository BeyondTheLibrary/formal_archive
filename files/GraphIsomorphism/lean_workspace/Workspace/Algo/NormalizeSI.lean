import Workspace.Algo.Luks

/-!
# Normalizing the input of String Isomorphism

The domain size does not bound an arbitrary input encoding: generators can repeat and
letters can be large. We shorten the generators and name each letter by its first position
in the concatenation of the two strings. Both strings use the same names.

`RawSI` has no separate domain field. Its domain witness is the length of its first string,
and the routine keeps both string lengths. On junk, `tidyGens` first sanitizes permutations
without changing their decoding, then shortens the list. The routine still renames both
strings, even when their lengths differ. Its polynomial time bound holds on all inputs.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

/-- The first position of a letter in a list, with default zero when it does not occur. -/
def rawLetterIndex (p : RawStr × ℕ) : ℕ := rawInvLookup (p.1.zipIdx, p.2)

theorem polyFun_rawLetterIndex : PolyFun rawLetterIndex :=
  (((polyFun_fst.comp polyFun_zipIdx).pair polyFun_snd).comp
    polyFun_rawInvLookup).of_eq (fun _ => rfl)

private theorem lookup_zipIdx_of_mem {a : ℕ} {l : List ℕ} (ha : a ∈ l) (k : ℕ) :
    ∃ i, ∃ hi : i < l.length, l[i] = a ∧ (l.zipIdx k).lookup a = some (i + k) := by
  induction l generalizing k with
  | nil => simp at ha
  | cons b l ih =>
      by_cases hab : a = b
      · subst a
        exact ⟨0, by simp, by simp, by simp⟩
      · have hal : a ∈ l := (List.mem_cons.1 ha).resolve_left hab
        obtain ⟨i, hi, hval, hlook⟩ := ih hal (k + 1)
        refine ⟨i + 1, by simpa using hi, by simpa using hval, ?_⟩
        have hbeq : (a == b) = false := beq_eq_false_iff_ne.2 hab
        simpa [List.zipIdx_cons, List.lookup, hbeq, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hlook

/-- A letter that occurs gets an index in the list, and that index reads back the letter. -/
theorem rawLetterIndex_spec {l : RawStr} {a : ℕ} (ha : a ∈ l) :
    rawLetterIndex (l, a) < l.length ∧ l.getD (rawLetterIndex (l, a)) 0 = a := by
  obtain ⟨i, hi, hval, hlook⟩ := lookup_zipIdx_of_mem ha 0
  have heq : rawLetterIndex (l, a) = i := by
    simp [rawLetterIndex, rawInvLookup, hlook]
  rw [heq]
  exact ⟨hi, (List.getD_eq_getElem _ _ hi).trans hval⟩

/-- The naming map is injective on the letters that occur. -/
theorem rawLetterIndex_eq_iff {l : RawStr} {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) :
    rawLetterIndex (l, a) = rawLetterIndex (l, b) ↔ a = b := by
  constructor
  · intro h
    exact (rawLetterIndex_spec ha).2.symm.trans
      ((congrArg (fun i => l.getD i 0) h).trans (rawLetterIndex_spec hb).2)
  · rintro rfl
    rfl

/-- Rename a string using a shared list of letters. -/
def rawRenameStr (p : RawStr × RawStr) : RawStr :=
  p.2.map (fun a => rawLetterIndex (p.1, a))

theorem polyFun_rawRenameStr : PolyFun rawRenameStr :=
  (PolyFun.mapParam polyFun_rawLetterIndex).of_eq (fun _ => rfl)

/-- Shorten the generators and rename the two strings together. -/
def rawNormSI (I : RawSI) : RawSI :=
  (tidyGens (I.2.1, I.1), rawRenameStr (I.2.1 ++ I.2.2, I.2.1),
    rawRenameStr (I.2.1 ++ I.2.2, I.2.2))

/-- The normalization is polynomial on all inputs, including junk. -/
theorem polyFun_rawNormSI : PolyFun rawNormSI := by
  have hx : PolyFun (fun I : RawSI => I.2.1) := polyFun_snd.comp polyFun_fst
  have hy : PolyFun (fun I : RawSI => I.2.2) := polyFun_snd.comp polyFun_snd
  have hl : PolyFun (fun I : RawSI => I.2.1 ++ I.2.2) :=
    (hx.pair hy).comp polyFun_append
  exact (((hx.pair polyFun_fst).comp polyFun_tidyGens).pair
    (((hl.pair hx).comp polyFun_rawRenameStr).pair
      ((hl.pair hy).comp polyFun_rawRenameStr))).of_eq (fun _ => rfl)

@[simp] theorem rawNormSI_length_left (I : RawSI) :
    (rawNormSI I).2.1.length = I.2.1.length := by simp [rawNormSI, rawRenameStr]

@[simp] theorem rawNormSI_length_right (I : RawSI) :
    (rawNormSI I).2.2.length = I.2.2.length := by simp [rawNormSI, rawRenameStr]

/-- The decoded group is preserved even on junk. -/
theorem decGroup_rawNormSI {n : ℕ} (I : RawSI) (hn : I.2.1.length = n) :
    decGroup n (rawNormSI I).1 = decGroup n I.1 := decGroup_tidyGens hn I.1

/-- A bounded presentation on a domain of size `n`, using the well-formedness predicates
of `Encodings.lean`. This is an input invariant, not yet a Master-round invariant. -/
def NormSIWF (n : ℕ) (I : RawSI) : Prop :=
  RawGens.WF n I.1 ∧ I.1.length ≤ n * n ∧
    RawStr.WF n (2 * n) I.2.1 ∧ RawStr.WF n (2 * n) I.2.2

/-!
For A15, the size invariant for a Master round on `RawSI` with
`ground I = I.2.1.length` is `WF I := NormSIWF I.2.1.length I`. A15 may conjoin its
concrete branch conditions. `NormSIWF.size_le` supplies the instance-size bound.
Every recursive `RawSI` child
must satisfy this same predicate, for example by applying `rawNormSI` when it is built and
proving that the child still describes the required problem. Root normalization alone does
not prove `child_wf`. Window instances also need their window and representative conditions.
Nodes with action data, phase data, or retained parent data need fixed polynomial bounds on
those fields in the same nonincreasing ground parameter.

The current child constructors already shorten generators in these places:
`winChild` uses `tidyGens`; `descChild` uses `descKer` and `rawKerGens`;
`impChild` uses `impKer`; `lcChild` uses `lcKer`; `top1Child` uses `topLiftChild` and
`topLiftPrepare`; `top2Child` uses `top2Leaf`. The last four paths use `tidyGens`.
`topKernel`, `topStab`, `topAltPreimage`, and `topWinStart` also use `tidyGens`.
The answer routines `rawCosetJoin`, `rawBrute`, and `rawRightTranslate` shorten as well.

The following helpers do not shorten their returned list: `rawRestrictGens`,
`rawBlockImgs`, `rawExtGens`, `rawProjGens`, `rawLiftGens`, `actLiftGens`,
`actKerGens`, `blockKerGens`, `rawTopStabGens`, `rawCertK`, and `rawCertM`. Some read a short
table or shorten on the extended domain internally. These routines do not in general give
the bound `n * n` for their final domain. `rawCertK` reads a point-stabilizer table on the
same domain, so a length proof can suffice there. `rawCertM`, `top1Request`, `liftWin`, and
`liftLC` copy data and need bounds inherited from their inputs. A15 must use the shortening
wrappers or prove a bound for each use.
Generator-image lists for a homomorphism must be changed together when shortening.
None of these existing child constructors renames letters jointly as `rawNormSI` does.
Copying or permuting normalized strings preserves the old label bound, but restricting to
a smaller domain does not establish the new bound `2 * n`.

The local rounds `chainRound`, `descentRound`, `impRound`, and `lcRound` use the
encoded string-pair size as ground; the top rounds use the encoded parent size. Their local
cost proofs therefore still need a bound in the Master ground size when A15 composes them.
The detailed hand-over is in the DESIGN note "A6 repair: input normalization".
-/

/-- Equal-length strings normalize to a bounded presentation. -/
theorem rawNormSI_wf {n : ℕ} (I : RawSI) (hx : I.2.1.length = n)
    (hy : I.2.2.length = n) : NormSIWF n (rawNormSI I) := by
  refine ⟨wf_tidyGens hx _, length_tidyGens hx _, ⟨by simpa using hx, ?_⟩,
    ⟨by simpa using hy, ?_⟩⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    have h := (rawLetterIndex_spec (List.mem_append_left I.2.2 hb)).1
    simpa [List.length_append, hx, hy, two_mul] using h
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    have h := (rawLetterIndex_spec (List.mem_append_right I.2.1 hb)).1
    simpa [List.length_append, hx, hy, two_mul] using h

theorem rawNormSI_rawOfSI_wf {n s : ℕ} (a : SIInput n s) :
    NormSIWF n (rawNormSI (rawOfSI a)) :=
  rawNormSI_wf _ (length_encStr _) (length_encStr _)

theorem decGroup_rawNormSI_rawOfSI {n s : ℕ} (a : SIInput n s) :
    decGroup n (rawNormSI (rawOfSI a)).1 = genGroup a.1 := by
  rw [decGroup_rawNormSI _ (length_encStr _)]
  exact decGroup_map_encPerm n a.1

/-- Decoding a renamed string applies the same naming map at each point. -/
theorem decStrN_rawRenameStr {n : ℕ} (l x : RawStr) (hx : x.length = n) :
    decStrN n (rawRenameStr (l, x)) =
      fun i => rawLetterIndex (l, decStrN n x i) := by
  funext i
  have hi : (i : ℕ) < x.length := by rw [hx]; exact i.isLt
  simp only [decStrN, rawRenameStr]
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    List.getD_eq_getElem _ _ hi]

private theorem decStrN_mem {n : ℕ} {x : RawStr} (hx : x.length = n) (i : Fin n) :
    decStrN n x i ∈ x := by
  rw [decStrN, List.getD_eq_getElem _ _ (by rw [hx]; exact i.isLt)]
  exact List.getElem_mem _

/-- A shared naming map preserves string isomorphisms. Injectivity is needed only on
the letters that occur in the two strings. -/
theorem strIso_rawRenameStr {n : ℕ} (K : Set (Perm (Fin n))) (l x y : RawStr)
    (hx : x.length = n) (hy : y.length = n)
    (hxl : ∀ a ∈ x, a ∈ l) (hyl : ∀ a ∈ y, a ∈ l) :
    Babai.strIso K (decStrN n (rawRenameStr (l, x)))
      (decStrN n (rawRenameStr (l, y))) = Babai.strIso K (decStrN n x) (decStrN n y) := by
  rw [decStrN_rawRenameStr l x hx, decStrN_rawRenameStr l y hy]
  simp only [Babai.strIso_eq_sep]
  ext σ
  simp only [Set.mem_setOf_eq]
  exact and_congr_right (fun _ => forall_congr' (fun i =>
    rawLetterIndex_eq_iff (hxl _ (decStrN_mem hx i)) (hyl _ (decStrN_mem hy (σ i)))))

@[simp] theorem decStrN_encStr {n s : ℕ} (x : Fin n → Fin s) :
    decStrN n (encStr x) = fun i => (x i : ℕ) := decStrN_encStrN _

private theorem strIso_fin_val {n s : ℕ} (K : Set (Perm (Fin n))) (x y : Fin n → Fin s) :
    Babai.strIso K (fun i => (x i : ℕ)) (fun i => (y i : ℕ)) = Babai.strIso K x y := by
  simp only [Babai.strIso_eq_sep]
  ext σ
  simp only [Set.mem_setOf_eq, Fin.val_inj]

/-- Normalization preserves the set of isomorphisms of the original typed input. -/
theorem strIso_rawNormSI_rawOfSI {n s : ℕ} (a : SIInput n s) :
    Babai.strIso (decGroup n (rawNormSI (rawOfSI a)).1 : Set (Perm (Fin n)))
      (decStrN n (rawNormSI (rawOfSI a)).2.1) (decStrN n (rawNormSI (rawOfSI a)).2.2)
      = Babai.strIso (genGroup a.1 : Set (Perm (Fin n))) a.2.1 a.2.2 := by
  rw [decGroup_rawNormSI_rawOfSI]
  change Babai.strIso _ (decStrN n (rawRenameStr _)) (decStrN n (rawRenameStr _)) = _
  dsimp only [rawOfSI]
  rw [strIso_rawRenameStr _ (encStr a.2.1 ++ encStr a.2.2) (encStr a.2.1) (encStr a.2.2)
    (length_encStr _) (length_encStr _)
    (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_right _ h)]
  rw [decStrN_encStr, decStrN_encStr, strIso_fin_val]

/-- The same shared naming map preserves the automorphism group of the first string. -/
theorem strAut_rawNormSI_rawOfSI {n s : ℕ} (a : SIInput n s) :
    Babai.strAut (decGroup n (rawNormSI (rawOfSI a)).1 : Set (Perm (Fin n)))
      (decStrN n (rawNormSI (rawOfSI a)).2.1)
      = Babai.strAut (genGroup a.1 : Set (Perm (Fin n))) a.2.1 := by
  rw [Babai.strAut, Babai.strAut, decGroup_rawNormSI_rawOfSI]
  change Babai.strIso _ (decStrN n (rawRenameStr _)) (decStrN n (rawRenameStr _)) = _
  dsimp only [rawOfSI]
  rw [strIso_rawRenameStr _ (encStr a.2.1 ++ encStr a.2.2) (encStr a.2.1) (encStr a.2.1)
    (length_encStr _) (length_encStr _)
    (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_left _ h)]
  rw [decStrN_encStr, strIso_fin_val]

/-- A raw answer can be read as a typed answer with the same encoding when every stored
permutation is well formed. -/
def RawCoset.WF (n : ℕ) : RawCoset → Prop
  | none => True
  | some (gs, σ) => RawGens.WF n gs ∧ RawPerm.WF n σ

/-- The raw output specification: a well-formed answer whose decoded coset is the set of
string isomorphisms. This includes the empty-answer case. -/
def RawSIRel (n : ℕ) (I : RawSI) (b : RawCoset) : Prop :=
  RawCoset.WF n b ∧ decCoset n b =
    Babai.strIso (decGroup n I.1 : Set (Perm (Fin n))) (decStrN n I.2.1) (decStrN n I.2.2)

/-- The raw coset specification gives the output representation of Definition 11.1.2,
Section 11.1: generators of the automorphism group and one isomorphism. -/
theorem exists_SIRel_of_decCoset {n s : ℕ} (a : SIInput n s) (b : RawCoset)
    (hwf : RawCoset.WF n b) (hans : decCoset n b = IsoSet a.1 a.2.1 a.2.2) :
    ∃ b' : Option (List (Perm (Fin n)) × Perm (Fin n)),
      Enc.encode b' = Enc.encode b ∧ SIRel n s a b' := by
  classical
  cases b with
  | none => exact ⟨none, rfl, hans.symm⟩
  | some q =>
      obtain ⟨gs, σ⟩ := q
      obtain ⟨hg, hσ⟩ := hwf
      refine ⟨some (gs.map (decPerm n), decPerm n σ), ?_, ?_⟩
      · have heG : Enc.encode (gs.map (decPerm n)) = Enc.encode gs := by
          rw [encode_gens_eq, map_encPerm_decPerm hg]
        have heσ : Enc.encode (decPerm n σ) = Enc.encode σ := by
          rw [encode_perm_eq, encPerm_decPerm hσ]
        change 1 :: (frame (Enc.encode (gs.map (decPerm n))) ++
          frame (Enc.encode (decPerm n σ))) =
            1 :: (frame (Enc.encode gs) ++ frame (Enc.encode σ))
        rw [heG, heσ]
      · have hrep : decPerm n σ ∈ IsoSet a.1 a.2.1 a.2.2 := by
          rw [← hans]
          exact ⟨1, (decGroup n gs).one_mem, (mul_one _).symm⟩
        refine ⟨hrep, ?_⟩
        ext g
        change g ∈ decGroup n gs ↔ g ∈ AutSet a.1 a.2.1
        constructor
        · intro hg'
          have hsg : decPerm n σ * g ∈ IsoSet a.1 a.2.1 a.2.2 := by
            rw [← hans]
            exact ⟨g, hg', rfl⟩
          refine ⟨?_, fun u => (hsg.2 u).trans (hrep.2 (g u)).symm⟩
          have hm := (genGroup a.1).mul_mem ((genGroup a.1).inv_mem hrep.1) hsg.1
          simpa only [inv_mul_cancel_left] using hm
        · intro hg'
          have hsg : decPerm n σ * g ∈ IsoSet a.1 a.2.1 a.2.2 :=
            ⟨(genGroup a.1).mul_mem hrep.1 hg'.1,
              fun u => (hg'.2 u).trans (hrep.2 (g u))⟩
          rw [← hans] at hsg
          obtain ⟨g', hg', he⟩ := hsg
          exact mul_left_cancel he ▸ hg'

/-- The final assembly uses this lemma to discharge `hdec` of
`siWorkspaceRoutine_of_norm_run`. A raw answer for the normalized input is an answer for
the original input, and the typed answer has exactly the raw answer's encoding. -/
theorem rawNormSI_answer {n s : ℕ} (a : SIInput n s) (b : RawCoset)
    (h : RawSIRel n (rawNormSI (rawOfSI a)) b) :
    ∃ b' : Option (List (Perm (Fin n)) × Perm (Fin n)),
      Enc.encode b' = Enc.encode b ∧ SIRel n s a b' := by
  apply exists_SIRel_of_decCoset a b h.1
  rw [h.2, strIso_rawNormSI_rawOfSI, Babai.strIso_eq_sep]
  rfl

/-- One fixed polynomial bounds every normalized input, independently of its old alphabet
and of the length of its old generating list. -/
def normSIBound (n : ℕ) : ℕ := 64 * (n + 1) ^ 4

theorem polyBound_normSIBound : PolyBound normSIBound := polyBound_witness 64 4

/-- A bounded presentation has size polynomial in its domain size. -/
theorem NormSIWF.size_le {n : ℕ} {I : RawSI} (h : NormSIWF n I) :
    Enc.size I ≤ normSIBound n := by
  obtain ⟨hg, hlen, hx, hy⟩ := h
  have hp : ∀ g ∈ I.1, Enc.size g ≤ strBound n := by
    intro g hmem
    exact size_natList_le (le_of_eq (hg g hmem).length) (hg g hmem).2.1
  have hgs := size_list_le_of_entries I.1 (strBound n) hp
  have hmul := Nat.mul_le_mul_right (2 * strBound n + 1) hlen
  have hxs := size_natList_le (le_of_eq hx.1) hx.2
  have hys := size_natList_le (le_of_eq hy.1) hy.2
  have hpair := Combine.size_pair_le I.2.1 I.2.2
  have hwhole := Combine.size_pair_le I.1 I.2
  dsimp [strBound, normSIBound] at *
  nlinarith

theorem size_rawNormSI_rawOfSI {n s : ℕ} (a : SIInput n s) :
    Enc.size (rawNormSI (rawOfSI a)) ≤ normSIBound n := (rawNormSI_rawOfSI_wf a).size_le

/-- Repeated identity generators no longer obstruct a domain-size bound. The bound is
independent of `k`, including when `k` is larger than the evaluator's bound at domain one. -/
theorem size_rawNormSI_repeatedIdentity (k : ℕ) :
    Enc.size (rawNormSI (rawOfSI
      ((List.replicate k (1 : Perm (Fin 1)), fun _ => 0, fun _ => 0) : SIInput 1 1)))
      ≤ normSIBound 1 := size_rawNormSI_rawOfSI _

end Algo

#print axioms Algo.polyFun_rawNormSI
#print axioms Algo.rawNormSI_rawOfSI_wf
#print axioms Algo.decGroup_rawNormSI_rawOfSI
#print axioms Algo.strIso_rawNormSI_rawOfSI
#print axioms Algo.strAut_rawNormSI_rawOfSI
#print axioms Algo.rawNormSI_answer
#print axioms Algo.size_rawNormSI_rawOfSI
#print axioms Algo.size_rawNormSI_repeatedIdentity
