/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the permutation routines on raw data.
-/
import Workspace.Algo.Encodings
import Workspace.Machine.ListOps2
import Workspace.Luks.Defs

/-!
# Permutation routines on raw data

Every routine of the paper's algorithms works on permutations of `[0, n)`.  This file writes
them on the raw type `Algo.RawPerm = List ℕ`, where the degree `n` is never a type index: it
is read off as the length of the list, or it arrives inside the input.  That is what
`Workspace/Machine/DESIGN.md` demands of anything that has to be uniform in `n`, because
`RAM.PolyFun` is a statement about **one** function between two fixed encodable types.

Each routine comes in three parts.

1. The definition, a plain computable function on raw data.  Every routine is **total**: on a
   list that is not a permutation it answers junk, and no specification lemma claims anything
   about that answer.
2. The specification, against `Algo.decPerm`, under the well-formedness hypothesis
   `Algo.RawPerm.WF`.
3. The `RAM.PolyFun` statement, built from the combinators of `Workspace/Machine/`.

## The convention on products

The paper acts on the right: its product `στ` means "first `σ`, then `τ`".  Lean acts on the
left, so the paper's `στ` is Lean's `τ * σ` (see the header of `Workspace/Luks/Defs.lean`).
Everything below is stated for Lean's `*`; `Algo.rawMul_encPerm` reads
`rawMul (encPerm n σ, encPerm n τ) = encPerm n (σ * τ)`, which is the paper's product `τσ`.

## Main definitions

`Algo.rawApply`, `Algo.rawMul`, `Algo.rawOne`, `Algo.rawInv`, `Algo.rawIsPerm`,
`Algo.rawPermEq`, `Algo.rawPermMem`, `Algo.rawStrAct`, `Algo.rawGensMul`, `Algo.rawGensInv`,
`Algo.rawImages`.

No axiom, no `sorry`, no running-time claim outside `RAM.PolyFun`.
-/

namespace Algo

open RAM

/-! ## Reading one entry

Two readers, with different defaults.  A point outside the domain is its own image, which
keeps `Algo.rawApply` the identity off the domain; a letter outside the domain is `0`. -/

/-- **Apply a raw permutation to a point.**  Outside the domain the point is fixed. -/
def rawApply (p : RawPerm × ℕ) : ℕ := p.1.getD p.2 p.2

/-- **Read one letter of a raw string.**  Outside the domain the letter is `0`. -/
def rawGet (p : RawStr × ℕ) : ℕ := p.1.getD p.2 0

/-- Off the domain `rawApply` is the identity.  This is the junk clause; no specification
lemma below depends on it. -/
theorem rawApply_of_length_le {l : RawPerm} {i : ℕ} (h : l.length ≤ i) :
    rawApply (l, i) = i :=
  List.getD_eq_default _ _ h

/-- **The specification of `rawApply`**: on a well-formed raw permutation it is the decoded
permutation. -/
theorem rawApply_of_wf {n : ℕ} {l : RawPerm} (h : RawPerm.WF n l) {i : ℕ} (hi : i < n) :
    rawApply (l, i) = (decPerm n l ⟨i, hi⟩ : ℕ) := by
  have hlen : i < l.length := by rw [h.length]; exact hi
  rw [rawApply, List.getD_eq_getElem _ _ hlen, decPerm_val_of_wf h ⟨i, hi⟩]

/-- `rawApply` on an encoded permutation. -/
theorem rawApply_encPerm (n : ℕ) (σ : Equiv.Perm (Fin n)) {i : ℕ} (hi : i < n) :
    rawApply (encPerm n σ, i) = (σ ⟨i, hi⟩ : ℕ) := by
  rw [rawApply_of_wf (wf_encPerm n σ) hi, decPerm_encPerm]

/-- `rawGet` on an encoded string. -/
theorem rawGet_encStr {n s : ℕ} (x : Fin n → Fin s) {i : ℕ} (hi : i < n) :
    rawGet (encStr x, i) = (x ⟨i, hi⟩ : ℕ) := by
  have hlen : i < (encStr x).length := by rw [length_encStr]; exact hi
  rw [rawGet, List.getD_eq_getElem _ _ hlen]
  simp [encStr]

theorem polyFun_rawApply : PolyFun rawApply :=
  (polyFun_id.pair polyFun_snd).comp polyFun_getD

theorem polyFun_rawGet : PolyFun rawGet :=
  ((polyFun_id.pair (polyFun_const 0)).comp polyFun_getD).of_eq (fun _ => rfl)

/-! ## The product

`(σ * τ) i = σ (τ i)`, so the array of `σ * τ` is the array of `τ` with every entry sent
through `σ`.  That is a map with a parameter, `RAM.PolyFun.mapParam`. -/

/-- **The product of two raw permutations.**  In Lean's convention: `rawMul (a, b)` decodes to
`decPerm a * decPerm b`.  In the paper's convention this is the product `ba`. -/
def rawMul (p : RawPerm × RawPerm) : RawPerm := p.2.map (fun j => rawApply (p.1, j))

@[simp] theorem length_rawMul (a b : RawPerm) : (rawMul (a, b)).length = b.length := by
  simp [rawMul]

/-- **The specification of `rawMul`** on encoded permutations.  The left factor is Lean's, so
the paper's product spelled here is `τσ`. -/
theorem rawMul_encPerm (n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    rawMul (encPerm n σ, encPerm n τ) = encPerm n (σ * τ) := by
  apply List.ext_getElem
  · simp [rawMul]
  · intro i hi hi2
    have hin : i < n := by simpa using hi2
    rw [getElem_encPerm n (σ * τ) i hin]
    show ((encPerm n τ).map (fun j => rawApply (encPerm n σ, j)))[i]'hi = _
    rw [List.getElem_map, getElem_encPerm n τ i hin, rawApply_encPerm n σ (τ ⟨i, hin⟩).isLt]
    simp

/-- **The specification of `rawMul`** on well-formed raw data. -/
theorem rawMul_of_wf {n : ℕ} {a b : RawPerm} (ha : RawPerm.WF n a) (hb : RawPerm.WF n b) :
    rawMul (a, b) = encPerm n (decPerm n a * decPerm n b) := by
  have h := rawMul_encPerm n (decPerm n a) (decPerm n b)
  rwa [encPerm_decPerm ha, encPerm_decPerm hb] at h

theorem wf_rawMul {n : ℕ} {a b : RawPerm} (ha : RawPerm.WF n a) (hb : RawPerm.WF n b) :
    RawPerm.WF n (rawMul (a, b)) := by
  rw [rawMul_of_wf ha hb]; exact wf_encPerm _ _

theorem polyFun_rawMul : PolyFun rawMul :=
  (PolyFun.mapParam polyFun_rawApply).of_eq (fun _ => rfl)

/-! ## The identity

`List.range n` for a machine natural `n` is not a `RAM.PolyFun` (see the header of
`Workspace/Machine/ListOps2.lean`), so the degree has to arrive as a list of that length: a
string, or one of the generators, or any other array over the domain. -/

/-- **The identity permutation of the domain of `l`.** -/
def rawOne (l : List ℕ) : RawPerm := List.range l.length

theorem encPerm_one (n : ℕ) : encPerm n (1 : Equiv.Perm (Fin n)) = List.range n := by
  apply List.ext_getElem <;> simp [encPerm]

/-- **The specification of `rawOne`.** -/
theorem rawOne_eq (l : List ℕ) : rawOne l = encPerm l.length 1 := (encPerm_one _).symm

theorem wf_rawOne (l : List ℕ) : RawPerm.WF l.length (rawOne l) := by
  rw [rawOne_eq]; exact wf_encPerm _ _

theorem polyFun_rawOne : PolyFun rawOne := polyFun_rangeLength

/-! ## The inverse

There is no writing at a computed position, so the inverse is found by search: for every point
`j` of the domain, look for the index `i` with `l[i] = j`.  The table of the search is
`l.zipIdx`, whose entries are the pairs `(l[i], i)`; the search itself is
`RAM.polyFun_listLookup`, and the loop over `j` is again a map with a parameter.  The cost is
quadratic, which is all that is needed. -/

/-- One lookup in the table of a raw permutation. -/
def rawInvLookup (p : List (ℕ × ℕ) × ℕ) : ℕ := (p.1.lookup p.2).getD 0

/-- **The inverse of a raw permutation.** -/
def rawInv (l : RawPerm) : RawPerm :=
  (List.range l.length).map (fun j => rawInvLookup (l.zipIdx, j))

@[simp] theorem length_rawInv (l : RawPerm) : (rawInv l).length = l.length := by
  simp [rawInv]

/-- In the table of a list with no repeated entry, the entry `l[i]` is found at the index
`i`. -/
theorem lookup_zipIdx_getElem : ∀ (l : List ℕ), l.Nodup →
    ∀ (k i j : ℕ) (hi : i < l.length), l[i]'hi = j → List.lookup j (l.zipIdx k) = some (i + k) := by
  intro l
  induction l with
  | nil => intro _ k i j hi _; simp at hi
  | cons a t ih =>
      intro hnd k i j hi hij
      rw [List.zipIdx_cons]
      match i with
      | 0 =>
          have hja : a = j := by simpa using hij
          subst hja
          simp [List.lookup]
      | (i + 1) =>
          have hi' : i < t.length := by simpa using hi
          have hij' : t[i]'hi' = j := by simpa using hij
          have hmem : j ∈ t := hij' ▸ List.getElem_mem hi'
          have hne : ¬ (j = a) := fun h => (List.nodup_cons.1 hnd).1 (h ▸ hmem)
          have hbeq : (j == a) = false := by simpa using hne
          have hstep : List.lookup j ((a, k) :: t.zipIdx (k + 1))
              = List.lookup j (t.zipIdx (k + 1)) := by
            simp [List.lookup, hbeq]
          rw [hstep, ih (List.nodup_cons.1 hnd).2 (k + 1) i j hi' hij']
          congr 1
          omega

/-- **The specification of `rawInv`.** -/
theorem rawInv_of_wf {n : ℕ} {l : RawPerm} (h : RawPerm.WF n l) :
    rawInv l = encPerm n (decPerm n l)⁻¹ := by
  apply List.ext_getElem
  · rw [length_rawInv, length_encPerm, h.length]
  · intro j hj _
    have hjn : j < n := by rw [← h.length]; simpa using hj
    set i : ℕ := ((decPerm n l)⁻¹ ⟨j, hjn⟩).val with hi
    have hin : i < n := ((decPerm n l)⁻¹ ⟨j, hjn⟩).isLt
    have hil : i < l.length := by rw [h.length]; exact hin
    have hfin : (⟨i, hin⟩ : Fin n) = (decPerm n l)⁻¹ ⟨j, hjn⟩ := Fin.ext rfl
    have hli : l[i]'hil = j := by
      have h1 := decPerm_val_of_wf h ⟨i, hin⟩
      have h2 : (decPerm n l) ((decPerm n l)⁻¹ ⟨j, hjn⟩) = ⟨j, hjn⟩ := by simp
      rw [hfin, h2] at h1
      exact h1.symm
    have hlook : List.lookup j (l.zipIdx 0) = some i := by
      have := lookup_zipIdx_getElem l h.nodup 0 i j hil hli
      rwa [Nat.add_zero] at this
    have hread : (rawInv l)[j]'hj = rawInvLookup (l.zipIdx, j) := by
      simp only [rawInv, List.getElem_map, List.getElem_range]
    have hval : rawInvLookup (l.zipIdx, j) = i := by
      simp [rawInvLookup, hlook]
    rw [getElem_encPerm n _ j hjn, hread, hval, hi]

/-- `rawInv` on an encoded permutation. -/
theorem rawInv_encPerm (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    rawInv (encPerm n σ) = encPerm n σ⁻¹ := by
  rw [rawInv_of_wf (wf_encPerm n σ), decPerm_encPerm]

theorem wf_rawInv {n : ℕ} {l : RawPerm} (h : RawPerm.WF n l) : RawPerm.WF n (rawInv l) := by
  rw [rawInv_of_wf h]; exact wf_encPerm _ _

theorem polyFun_rawInvLookup : PolyFun rawInvLookup :=
  (((polyFun_listLookup (β := ℕ) polyFun_natEq).pair (polyFun_const 0)).comp
    polyFun_optionGetD).of_eq (fun _ => rfl)

theorem polyFun_rawInv : PolyFun rawInv :=
  ((polyFun_zipIdx.pair polyFun_rangeLength).comp
    (PolyFun.mapParam polyFun_rawInvLookup)).of_eq (fun _ => rfl)

/-! ## The well-formedness test

A list of length `n` is the array of a permutation of `[0, n)` exactly when every point of
`[0, n)` occurs in it.  One inclusion is pigeonhole, the other is counting; neither direction
needs the entries to be tested separately. -/

/-- Well-formedness in one clause. -/
theorem wf_iff_forall_mem (l : RawPerm) :
    RawPerm.WF l.length l ↔ ∀ j < l.length, j ∈ l := by
  constructor
  · intro h j hj
    have hsub : l.toFinset ⊆ Finset.range l.length := by
      intro a ha
      simp only [List.mem_toFinset] at ha
      simpa using h.lt ha
    have hcard : (Finset.range l.length).card ≤ l.toFinset.card := by
      rw [List.toFinset_card_of_nodup h.nodup]
      simp
    have heq : l.toFinset = Finset.range l.length := Finset.eq_of_subset_of_card_le hsub hcard
    have : j ∈ l.toFinset := by rw [heq]; simpa using hj
    simpa using this
  · intro h
    have hsub : Finset.range l.length ⊆ l.toFinset := by
      intro a ha
      simp only [Finset.mem_range] at ha
      simpa using h a ha
    have h2 : l.toFinset.card ≤ l.length := List.toFinset_card_le l
    have heq : Finset.range l.length = l.toFinset :=
      Finset.eq_of_subset_of_card_le hsub (by simpa using h2)
    have hcard : l.toFinset.card = l.length := by rw [← heq]; simp
    have hnd : l.Nodup := by
      have hlen : l.dedup.length = l.length := by rw [← List.card_toFinset]; exact hcard
      exact List.dedup_eq_self.1 (List.Sublist.eq_of_length (List.dedup_sublist l) hlen)
    refine ⟨rfl, ?_, hnd⟩
    intro a ha
    have : a ∈ l.toFinset := by simpa using ha
    rw [← heq] at this
    simpa using this

/-- **The well-formedness test.**  The degree is the length of the list. -/
def rawIsPerm (l : RawPerm) : Bool :=
  ((List.range l.length).filter (fun j => !decide (j ∈ l))).isEmpty

/-- **The specification of `rawIsPerm`.** -/
theorem rawIsPerm_eq_true_iff (l : RawPerm) : rawIsPerm l = true ↔ RawPerm.WF l.length l := by
  rw [wf_iff_forall_mem, rawIsPerm]
  simp [List.isEmpty_iff, List.filter_eq_nil_iff]

theorem rawIsPerm_encPerm (n : ℕ) (σ : Equiv.Perm (Fin n)) : rawIsPerm (encPerm n σ) = true := by
  rw [rawIsPerm_eq_true_iff, length_encPerm]
  exact wf_encPerm n σ

theorem polyFun_rawIsPerm : PolyFun rawIsPerm := by
  have hmem : PolyFun (fun p : RawPerm × ℕ => (!decide (p.2 ∈ p.1) : Bool)) := by
    refine (PolyFun.ite ((polyFun_snd.pair polyFun_fst).comp polyFun_natListMem)
      (polyFun_const false) (polyFun_const true)).of_eq (fun p => ?_)
    by_cases h : p.2 ∈ p.1 <;> simp [h]
  refine (((polyFun_id.pair polyFun_rangeLength).comp
    (PolyFun.filterParam hmem)).comp polyFun_isEmpty).of_eq (fun l => ?_)
  rfl

/-! ## Equality and membership -/

/-- **Equality of two raw permutations.** -/
def rawPermEq (p : RawPerm × RawPerm) : Bool := decide (p.1 = p.2)

/-- **Membership of a raw permutation in a list of raw permutations.** -/
def rawPermMem (p : RawPerm × RawGens) : Bool := decide (p.1 ∈ p.2)

theorem encPerm_injective (n : ℕ) : Function.Injective (encPerm n) := by
  intro σ τ h
  have := congrArg (decPerm n) h
  simpa using this

/-- **The specification of `rawPermEq`.** -/
theorem rawPermEq_encPerm (n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    rawPermEq (encPerm n σ, encPerm n τ) = decide (σ = τ) := by
  rw [rawPermEq]
  by_cases h : σ = τ
  · simp [h]
  · have hne : ¬ (encPerm n σ = encPerm n τ) := fun hh => h (encPerm_injective n hh)
    simp [h, hne]

/-- **The specification of `rawPermMem`.** -/
theorem rawPermMem_encPerm (n : ℕ) (σ : Equiv.Perm (Fin n))
    (gens : List (Equiv.Perm (Fin n))) :
    rawPermMem (encPerm n σ, gens.map (encPerm n)) = decide (σ ∈ gens) := by
  simp only [rawPermMem]
  exact decide_eq_decide.2 (List.mem_map_of_injective (encPerm_injective n))

theorem polyFun_rawPermEq : PolyFun rawPermEq := polyFun_listNatEq

theorem polyFun_rawPermMem : PolyFun rawPermMem :=
  (polyFun_listMem polyFun_listNatEq).of_eq
    (fun _ => by rw [rawPermMem]; exact decide_eq_decide.2 Iff.rfl)

/-! ## The action on strings

Eq. (55): `x^τ(u) = x(u^{τ⁻¹})`, which is `Babai.strAct x τ u = x (τ⁻¹ u)`.  The new letter at
the point `u` is therefore the old letter at `τ⁻¹ u`, so the routine reads the string along the
inverse array. -/

/-- **The action of a raw permutation on a raw string**, Eq. (55). -/
def rawStrAct (p : RawPerm × RawStr) : RawStr :=
  (rawInv p.1).map (fun i => rawGet (p.2, i))

/-- **The specification of `rawStrAct`**, against `Babai.strAct`. -/
theorem rawStrAct_encStr {n s : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n → Fin s) :
    rawStrAct (encPerm n σ, encStr x) = encStr (Babai.strAct x σ) := by
  show (rawInv (encPerm n σ)).map (fun i => rawGet (encStr x, i)) = _
  rw [rawInv_encPerm, encPerm, List.map_ofFn, encStr]
  refine congrArg List.ofFn (funext fun u => ?_)
  show rawGet (encStr x, ((σ⁻¹ u : Fin n) : ℕ)) = ((Babai.strAct x σ u : Fin s) : ℕ)
  rw [rawGet_encStr x (σ⁻¹ u).isLt]
  simp [Babai.strAct]

theorem polyFun_rawStrAct : PolyFun rawStrAct :=
  ((polyFun_snd.pair (polyFun_fst.comp polyFun_rawInv)).comp
    (PolyFun.mapParam polyFun_rawGet)).of_eq (fun _ => rfl)

/-! ## Lists of generators

The three routines a generator list needs: multiply every generator by a fixed permutation,
invert every generator, and send one point through every generator.  All three are maps, the
first and the third with a parameter. -/

/-- **Multiply every generator on the left.**  In the paper's convention `rawGensMul (a, gs)`
is the list of products `ga` with `g` running over `gs`. -/
def rawGensMul (p : RawPerm × RawGens) : RawGens := p.2.map (fun g => rawMul (p.1, g))

/-- **Invert every generator.** -/
def rawGensInv (gs : RawGens) : RawGens := gs.map rawInv

/-- **The image of one point under every generator.** -/
def rawImages (p : ℕ × RawGens) : List ℕ := p.2.map (fun g => rawApply (g, p.1))

/-- **The specification of `rawGensMul`.** -/
theorem rawGensMul_encPerm (n : ℕ) (σ : Equiv.Perm (Fin n))
    (gens : List (Equiv.Perm (Fin n))) :
    rawGensMul (encPerm n σ, gens.map (encPerm n)) = gens.map (fun τ => encPerm n (σ * τ)) := by
  show (gens.map (encPerm n)).map (fun g => rawMul (encPerm n σ, g)) = _
  rw [List.map_map]
  exact List.map_congr_left (fun τ _ => rawMul_encPerm n σ τ)

theorem wf_rawGensMul {n : ℕ} {a : RawPerm} {gs : RawGens} (ha : RawPerm.WF n a)
    (hgs : RawGens.WF n gs) : RawGens.WF n (rawGensMul (a, gs)) := by
  intro g hg
  rw [rawGensMul, List.mem_map] at hg
  obtain ⟨b, hb, rfl⟩ := hg
  exact wf_rawMul ha (hgs b hb)

/-- **The specification of `rawGensInv`.** -/
theorem rawGensInv_encPerm (n : ℕ) (gens : List (Equiv.Perm (Fin n))) :
    rawGensInv (gens.map (encPerm n)) = gens.map (fun τ => encPerm n τ⁻¹) := by
  rw [rawGensInv, List.map_map]
  exact List.map_congr_left (fun τ _ => rawInv_encPerm n τ)

theorem wf_rawGensInv {n : ℕ} {gs : RawGens} (hgs : RawGens.WF n gs) :
    RawGens.WF n (rawGensInv gs) := by
  intro g hg
  rw [rawGensInv, List.mem_map] at hg
  obtain ⟨b, hb, rfl⟩ := hg
  exact wf_rawInv (hgs b hb)

/-- **The specification of `rawImages`.** -/
theorem rawImages_encPerm (n : ℕ) (gens : List (Equiv.Perm (Fin n))) {i : ℕ} (hi : i < n) :
    rawImages (i, gens.map (encPerm n)) = gens.map (fun τ => ((τ ⟨i, hi⟩ : Fin n) : ℕ)) := by
  show (gens.map (encPerm n)).map (fun g => rawApply (g, i)) = _
  rw [List.map_map]
  exact List.map_congr_left (fun τ _ => rawApply_encPerm n τ hi)

theorem polyFun_rawGensMul : PolyFun rawGensMul :=
  (PolyFun.mapParam polyFun_rawMul).of_eq (fun _ => rfl)

theorem polyFun_rawGensInv : PolyFun rawGensInv := PolyFun.map polyFun_rawInv

theorem polyFun_rawImages : PolyFun rawImages :=
  (PolyFun.mapParam (polyFun_snd.pair polyFun_fst |>.comp polyFun_rawApply)).of_eq (fun _ => rfl)

end Algo
