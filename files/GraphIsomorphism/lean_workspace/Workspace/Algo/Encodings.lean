/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the raw encodings that every RAM routine works on.
-/
import Workspace.Machine.Targets
import Mathlib.Data.Fintype.EquivFin

/-!
# Raw encodings for the algorithmic layer

`RAM.PolyFun` is a statement about one function between two fixed encodable types, so it
cannot say "uniformly in `n`".  The final theorem
(`RAM.Targets.Theorem_1_1_1_statement`) asks for **one** program serving every domain size
`n` and every alphabet size `s`.  The way out is fixed by `Workspace/Machine/DESIGN.md`: a
routine that must be uniform in `n` works on *raw* types, where `n` is implicit in the
length of a list, and is transported to `SIInput n s` at the very end.

This file provides the raw types, the maps both ways, and the fact that makes the transport
free: as **lists of naturals**, the encoding of a permutation of `Fin n` is literally the
encoding of the list of its images, and likewise for strings and for a whole instance of
String Isomorphism.  See `Workspace/Algo/DESIGN.md`, item 3.

## Main definitions

* `Algo.RawPerm`, `Algo.RawGens`, `Algo.RawStr`, `Algo.RawSI`, `Algo.RawCoset` — the raw types;
* `Algo.encPerm`, `Algo.encStr`, `Algo.rawOfSI` — from the typed objects to the raw ones;
* `Algo.decPerm`, `Algo.decGroup`, `Algo.decCoset` — back.

## Main results

* `Algo.encode_perm_eq`, `Algo.encode_pi_eq`, `Algo.encode_gens_eq`, `Algo.encode_si_eq` —
  the encodings agree;
* `Algo.decPerm_encPerm` — the round trip on permutations;
* `Algo.decGroup_map_encPerm` — the round trip on a group given by generators.

Nothing here is a running-time statement.  No axiom, no `sorry`.
-/

namespace Algo

open RAM RAM.Targets

/-! ## The raw types -/

/-- A permutation of `[0, n)`, as the list of the images of `0, 1, …, n-1`. -/
abbrev RawPerm := List ℕ

/-- A permutation group, as a list of generators. -/
abbrev RawGens := List RawPerm

/-- A string, one letter per point of the domain.  Its length is the domain size `n`. -/
abbrev RawStr := List ℕ

/-- An answer to String Isomorphism (Def. 11.1.2): either the empty set, or a list of
generators of `Aut_G(x)` together with one coset representative. -/
abbrev RawCoset := Option (RawGens × RawPerm)

/-- An instance of String Isomorphism (Def. 11.1.2): generators of `G`, and two strings.
The domain size `n` is the length of the first string. -/
abbrev RawSI := RawGens × RawStr × RawStr

/-! ## From the typed objects to the raw ones -/

/-- The raw form of a permutation: the array of its images. -/
def encPerm (n : ℕ) (σ : Equiv.Perm (Fin n)) : RawPerm :=
  List.ofFn (fun i : Fin n => (σ i : ℕ))

/-- The raw form of a string: the array of its letters. -/
def encStr {n s : ℕ} (x : Fin n → Fin s) : RawStr :=
  List.ofFn (fun i : Fin n => (x i : ℕ))

/-- The raw form of an instance of String Isomorphism. -/
def rawOfSI {n s : ℕ} (a : SIInput n s) : RawSI :=
  (a.1.map (encPerm n), encStr a.2.1, encStr a.2.2)

@[simp] theorem length_encPerm (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (encPerm n σ).length = n := by
  simp [encPerm]

@[simp] theorem length_encStr {n s : ℕ} (x : Fin n → Fin s) : (encStr x).length = n := by
  simp [encStr]

@[simp] theorem getElem_encPerm (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : ℕ) (h : i < n) :
    (encPerm n σ)[i]'(by simpa using h) = (σ ⟨i, h⟩ : ℕ) := by
  simp [encPerm]

/-! ## The encodings agree

`Enc (Fin n)` encodes `i` as `[i.val]`, exactly as `Enc ℕ` encodes `i.val`
(`Workspace/Machine/Encoding.lean`).  So the whole picture in memory is the same at the two
types, and the transport between them does no work at all. -/

/-- The encoding of a list is read through a map by composing with it. -/
theorem encList_map {α β : Type*} (f : β → List ℕ) (h : α → β) (l : List α) :
    encList f (l.map h) = encList (fun a => f (h a)) l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, encList, ih]

/-- A function on `Fin n` and the list of its values have the same encoding. -/
theorem encode_pi_eq {n s : ℕ} (x : Fin n → Fin s) :
    Enc.encode x = Enc.encode (encStr x) := by
  show encList Enc.encode (List.ofFn x) = encList Enc.encode (encStr x)
  rw [encStr, show (List.ofFn fun i : Fin n => (x i : ℕ))
      = (List.ofFn x).map (fun j : Fin s => (j : ℕ)) by
        simp only [List.map_ofFn]; rfl,
    encList_map]
  rfl

/-- A permutation of `Fin n` and the list of its images have the same encoding. -/
theorem encode_perm_eq (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Enc.encode σ = Enc.encode (encPerm n σ) := by
  show Enc.encode (fun i => σ i : Fin n → Fin n) = _
  rw [encode_pi_eq (s := n) (fun i => σ i)]
  rfl

/-- A list of permutations and the list of their raw forms have the same encoding. -/
theorem encode_gens_eq (n : ℕ) (gens : List (Equiv.Perm (Fin n))) :
    Enc.encode gens = Enc.encode (gens.map (encPerm n)) := by
  show encList Enc.encode gens = encList Enc.encode (gens.map (encPerm n))
  rw [encList_map]
  exact congrArg (fun f => encList f gens) (funext fun σ => encode_perm_eq n σ)

/-- **The transport is free.**  An instance of String Isomorphism and its raw form have the
same encoding, so one RAM routine on `Algo.RawSI` serves every `n` and every `s`. -/
theorem encode_si_eq {n s : ℕ} (a : SIInput n s) :
    Enc.encode a = Enc.encode (rawOfSI a) := by
  obtain ⟨gens, x, y⟩ := a
  show frame (Enc.encode gens) ++ frame (Enc.encode (x, y))
      = frame (Enc.encode (gens.map (encPerm n))) ++ frame (Enc.encode (encStr x, encStr y))
  rw [encode_gens_eq n gens]
  congr 2
  show frame (Enc.encode x) ++ frame (Enc.encode y)
      = frame (Enc.encode (encStr x)) ++ frame (Enc.encode (encStr y))
  rw [encode_pi_eq x, encode_pi_eq y]

/-! ## Back from the raw form

The decoding maps are total: a raw list that is not a permutation decodes to the identity.
They are specification maps only — the RAM never runs them — so they may use classical
choice. -/

/-- The function on `Fin n` that a raw list describes: entry `i`, capped so that it lies in
the domain. -/
def rawFun (n : ℕ) (l : RawPerm) (i : Fin n) : Fin n :=
  ⟨min (l.getD i 0) (n - 1), lt_of_le_of_lt (min_le_right _ _) (by have := i.isLt; omega)⟩

open Classical in
/-- The permutation a raw list describes, or the identity when the list is not a
permutation. -/
noncomputable def decPerm (n : ℕ) (l : RawPerm) : Equiv.Perm (Fin n) :=
  if h : Function.Bijective (rawFun n l) then Equiv.ofBijective _ h else 1

theorem rawFun_encPerm (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    rawFun n (encPerm n σ) = σ := by
  funext i
  have hi : (i : ℕ) < (encPerm n σ).length := by simp
  have h1 : (encPerm n σ).getD (i : ℕ) 0 = (σ i : ℕ) := by
    rw [List.getD_eq_getElem _ _ hi]
    simp
  have h2 : (σ i : ℕ) ≤ n - 1 := by have := (σ i).isLt; omega
  apply Fin.ext
  simp only [rawFun, h1]
  omega

/-- The round trip on permutations. -/
@[simp] theorem decPerm_encPerm (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    decPerm n (encPerm n σ) = σ := by
  classical
  have hb : Function.Bijective (rawFun n (encPerm n σ)) := by
    rw [rawFun_encPerm]; exact σ.bijective
  rw [decPerm, dif_pos hb]
  apply Equiv.ext
  intro i
  show rawFun n (encPerm n σ) i = σ i
  rw [rawFun_encPerm]

/-- The group a list of raw generators describes.  This is `RAM.Targets.genGroup` of the
decoded list. -/
noncomputable def decGroup (n : ℕ) (gs : RawGens) : Subgroup (Equiv.Perm (Fin n)) :=
  genGroup (gs.map (decPerm n))

/-- The answer a raw coset describes: `∅` for `none`, and the paper's right coset `Aut·σ`
otherwise.

**The side.**  The paper's right coset `Hσ = {hσ | h ∈ H}` is Lean's `σ • H`, because the
paper composes permutations left to right and Lean composes them right to left
(`Workspace/Algo/DESIGN.md`, the convention).  So `Aut·σ` is written `decPerm n σ * g` here,
and it is the form the mathematical layer uses: `Babai.wIso_eq_smul_wAut_one` (Obs. 11.1.11)
and `Babai.Proposition_11_1_7_chainRule` both state the answer as `σ • Aut`. -/
noncomputable def decCoset (n : ℕ) (c : RawCoset) : Set (Equiv.Perm (Fin n)) :=
  match c with
  | none => ∅
  | some (a, σ) => {τ | ∃ g ∈ decGroup n a, τ = decPerm n σ * g}

/-- The round trip on a group given by generators. -/
@[simp] theorem decGroup_map_encPerm (n : ℕ) (gens : List (Equiv.Perm (Fin n))) :
    decGroup n (gens.map (encPerm n)) = genGroup gens := by
  rw [decGroup, List.map_map]
  congr 1
  induction gens with
  | nil => rfl
  | cons σ l ih => simp only [List.map_cons, Function.comp_apply, decPerm_encPerm, ih]

/-! ## Well-formed raw data

Every routine of the algorithmic layer is **total**: it answers something on every input, and
what it answers on junk is junk.  The specification lemmas therefore all carry a
well-formedness hypothesis, and this is what it says.  All three predicates are decidable and
computable, so a routine may test them; `Workspace/Algo/Perm.lean` turns the test for a raw
permutation into a `RAM.PolyFun`. -/

/-- A raw permutation is **well formed** for the degree `n` when it lists `n` entries, all of
them below `n`, with no repetition.  This says exactly that the list is the array of images of
a permutation of `[0, n)`. -/
def RawPerm.WF (n : ℕ) (l : RawPerm) : Prop :=
  l.length = n ∧ (∀ a ∈ l, a < n) ∧ l.Nodup

instance RawPerm.decidableWF (n : ℕ) (l : RawPerm) : Decidable (RawPerm.WF n l) :=
  inferInstanceAs (Decidable (l.length = n ∧ (∀ a ∈ l, a < n) ∧ l.Nodup))

theorem RawPerm.WF.length {n : ℕ} {l : RawPerm} (h : RawPerm.WF n l) : l.length = n := h.1

theorem RawPerm.WF.lt {n : ℕ} {l : RawPerm} (h : RawPerm.WF n l) {a : ℕ} (ha : a ∈ l) :
    a < n := h.2.1 a ha

theorem RawPerm.WF.nodup {n : ℕ} {l : RawPerm} (h : RawPerm.WF n l) : l.Nodup := h.2.2

/-- An entry of a well-formed raw permutation, read at an index of the domain. -/
theorem RawPerm.WF.getElem_lt {n : ℕ} {l : RawPerm} (h : RawPerm.WF n l) {i : ℕ}
    (hi : i < l.length) : l[i] < n :=
  h.lt (List.getElem_mem hi)

/-- A list of raw generators is well formed when each of its entries is. -/
def RawGens.WF (n : ℕ) (gs : RawGens) : Prop := ∀ g ∈ gs, RawPerm.WF n g

instance RawGens.decidableWF (n : ℕ) (gs : RawGens) : Decidable (RawGens.WF n gs) :=
  inferInstanceAs (Decidable (∀ g ∈ gs, RawPerm.WF n g))

/-- A raw string is well formed for the domain size `n` and the alphabet size `s` when it
lists `n` letters, all of them below `s`. -/
def RawStr.WF (n s : ℕ) (x : RawStr) : Prop := x.length = n ∧ ∀ a ∈ x, a < s

instance RawStr.decidableWF (n s : ℕ) (x : RawStr) : Decidable (RawStr.WF n s x) :=
  inferInstanceAs (Decidable (x.length = n ∧ ∀ a ∈ x, a < s))

/-- The raw form of a permutation is well formed. -/
theorem wf_encPerm (n : ℕ) (σ : Equiv.Perm (Fin n)) : RawPerm.WF n (encPerm n σ) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro a ha
    rw [encPerm, List.mem_ofFn'] at ha
    obtain ⟨i, rfl⟩ := ha
    exact (σ i).isLt
  · rw [encPerm, List.nodup_ofFn]
    intro i j hij
    exact σ.injective (Fin.ext hij)

/-- The raw form of a list of generators is well formed. -/
theorem wf_map_encPerm (n : ℕ) (gens : List (Equiv.Perm (Fin n))) :
    RawGens.WF n (gens.map (encPerm n)) := by
  intro g hg
  rw [List.mem_map] at hg
  obtain ⟨σ, _, rfl⟩ := hg
  exact wf_encPerm n σ

/-- The raw form of a string is well formed. -/
theorem wf_encStr {n s : ℕ} (x : Fin n → Fin s) : RawStr.WF n s (encStr x) := by
  refine ⟨by simp, ?_⟩
  intro a ha
  rw [encStr, List.mem_ofFn'] at ha
  obtain ⟨i, rfl⟩ := ha
  exact (x i).isLt

/-! ## Decoding a well-formed raw permutation

On well-formed data the capping in `Algo.rawFun` does nothing, the function is a bijection,
and `Algo.decPerm` reads off the entries of the list. -/

theorem rawFun_val_of_wf {n : ℕ} {l : RawPerm} (h : RawPerm.WF n l) (i : Fin n) :
    (rawFun n l i : ℕ) = l[(i : ℕ)]'(by rw [h.length]; exact i.isLt) := by
  have hi : (i : ℕ) < l.length := by rw [h.length]; exact i.isLt
  have h1 : l.getD (i : ℕ) 0 = l[(i : ℕ)] := List.getD_eq_getElem _ _ hi
  have h2 : l[(i : ℕ)] < n := h.getElem_lt hi
  simp only [rawFun, h1]
  omega

theorem rawFun_injective_of_wf {n : ℕ} {l : RawPerm} (h : RawPerm.WF n l) :
    Function.Injective (rawFun n l) := by
  intro i j hij
  have hi : (i : ℕ) < l.length := by rw [h.length]; exact i.isLt
  have hj : (j : ℕ) < l.length := by rw [h.length]; exact j.isLt
  have := congrArg (Fin.val) hij
  rw [rawFun_val_of_wf h i, rawFun_val_of_wf h j] at this
  exact Fin.ext (List.Nodup.getElem_inj_iff h.nodup |>.1 this)

theorem rawFun_bijective_of_wf {n : ℕ} {l : RawPerm} (h : RawPerm.WF n l) :
    Function.Bijective (rawFun n l) := by
  haveI : Finite (Fin n) := Finite.of_fintype _
  exact (Finite.injective_iff_bijective).1 (rawFun_injective_of_wf h)

/-- **The decoding reads off the list.**  On a well-formed raw permutation, `decPerm` sends
the point `i` to the entry `l[i]`. -/
theorem decPerm_val_of_wf {n : ℕ} {l : RawPerm} (h : RawPerm.WF n l) (i : Fin n) :
    (decPerm n l i : ℕ) = l[(i : ℕ)]'(by rw [h.length]; exact i.isLt) := by
  classical
  rw [decPerm, dif_pos (rawFun_bijective_of_wf h)]
  exact rawFun_val_of_wf h i

/-- **The round trip the other way round.**  A well-formed raw permutation, decoded and
encoded again, is itself. -/
theorem encPerm_decPerm {n : ℕ} {l : RawPerm} (h : RawPerm.WF n l) :
    encPerm n (decPerm n l) = l := by
  apply List.ext_getElem
  · simp [h.length]
  · intro i hi hi'
    have hin : i < n := by simpa using hi
    rw [getElem_encPerm n _ i hin, decPerm_val_of_wf h ⟨i, hin⟩]

end Algo
