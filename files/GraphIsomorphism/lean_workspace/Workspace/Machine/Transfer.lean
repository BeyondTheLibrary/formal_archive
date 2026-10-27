import Workspace.Machine.ListOps

/-!
# Transfer along equal encodings

A clean routine of the workspace convention is specified by the *memory* it starts in and the
memory it halts in, and both are read off the encoding
(`RAM.CleanComputeAt`, `RAM.CleanSolveAt`, `Workspace/Machine/Offset.lean`).  So a program does
not know at which type its input is read: if two types encode their elements as the same list of
registers, one program serves both.

This is what the algorithmic layer needs.  `RAM.PolyFun` speaks about one function between two
fixed encodable types, so it cannot say "uniformly in `n`".  Every routine there is therefore
written on raw types (`ℕ`, `List ℕ`, `List (List ℕ)`), where `n` is the length of a list, and is
carried over to the family `SIInput n s` at the very end.  The carrying over is free, because
`Enc (Fin n)` encodes `i` as `[i.val]`, exactly as `Enc ℕ` encodes `i.val`
(`Workspace/Machine/Encoding.lean`), so a permutation of `Fin n` and the list of its images have
the *same* encoding.  See Sec. 3.3 of `Workspace/Algo/DESIGN.md`.

The lemmas below take an interpretation map `e : α → α'` from the type one wants to the type one
has, with `Enc.encode (e a) = Enc.encode a`.  Nothing else about `e` is assumed: it need not be
injective, and no map back is needed.

## Main results

* `RAM.CleanComputeAt.transfer`, `RAM.CleanSolveAt.transfer`;
* `RAM.PolyTimeCleanAt.transfer`, `RAM.QuasiPolyTimeCleanAt.transfer`;
* `RAM.PolyFun.transfer`, `RAM.QuasiPolyFun.transfer`;
* `RAM.SizeBound.transfer`;
* the sanity example `RAM.Transfer.polyFun_boxedLength`.
-/

namespace RAM

variable {α β α' β' : Type*}

/-! ## Equal encodings give equal sizes -/

/-- Two objects with the same encoding have the same size: `Enc.size` is `listSize` of the
encoding and nothing else. -/
theorem size_eq_of_encode_eq [Enc α] [Enc β] {a : α} {b : β} (h : Enc.encode a = Enc.encode b) :
    Enc.size a = Enc.size b := by
  show listSize (Enc.encode a) = listSize (Enc.encode b)
  rw [h]

/-! ## Transfer of the clean classes -/

/-- **Transfer of a clean routine along equal encodings.**  If `e` does not change the encoding
of the input and `f` does not change the encoding of the output, then a program that computes
`f'` at the workspace convention computes `f` as well: it is the same run on the same memory. -/
theorem CleanComputeAt.transfer {K : ℕ} [Enc α] [Enc β] [Enc α'] [Enc β'] {P : Program}
    {T : ℕ → ℕ} {f : α → β} {f' : α' → β'} {e : α → α'}
    (he : ∀ a, Enc.encode (e a) = Enc.encode a)
    (hf : ∀ a, Enc.encode (f a) = Enc.encode (f' (e a)))
    (h : CleanComputeAt K P f' T) : CleanComputeAt K P f T := by
  intro a
  have hsize : Enc.size (e a) = Enc.size a := size_eq_of_encode_eq (he a)
  have hrun := h (e a)
  rw [he a, hsize] at hrun
  rw [hf a]
  exact hrun

/-- **Transfer of a clean search routine along equal encodings.**  The hypothesis `hR` says that
every answer the program may return at the type `β'` is the encoding of an answer admissible at
the type `β`.  This is the lemma Sec. 3.3 of `Workspace/Algo/DESIGN.md` asks for. -/
theorem CleanSolveAt.transfer {K : ℕ} [Enc α] [Enc β] [Enc α'] [Enc β'] {P : Program}
    {T : ℕ → ℕ} {R : α → β → Prop} {R' : α' → β' → Prop} {e : α → α'}
    (he : ∀ a, Enc.encode (e a) = Enc.encode a)
    (hR : ∀ (a : α) (b' : β'), R' (e a) b' → ∃ b : β, Enc.encode b = Enc.encode b' ∧ R a b)
    (h : CleanSolveAt K P R' T) : CleanSolveAt K P R T := by
  intro a
  obtain ⟨b', hb', hrun⟩ := h (e a)
  obtain ⟨b, hb, hRab⟩ := hR a b' hb'
  have hsize : Enc.size (e a) = Enc.size a := size_eq_of_encode_eq (he a)
  rw [he a, hsize] at hrun
  refine ⟨b, hRab, ?_⟩
  rw [hb]
  exact hrun

theorem PolyTimeCleanAt.transfer {K : ℕ} [Enc α] [Enc β] [Enc α'] [Enc β'] {f : α → β}
    {f' : α' → β'} {e : α → α'} (he : ∀ a, Enc.encode (e a) = Enc.encode a)
    (hf : ∀ a, Enc.encode (f a) = Enc.encode (f' (e a)))
    (h : PolyTimeCleanAt K f') : PolyTimeCleanAt K f := by
  obtain ⟨P, T, hT, hP⟩ := h
  exact ⟨P, T, hT, hP.transfer he hf⟩

theorem QuasiPolyTimeCleanAt.transfer {K : ℕ} [Enc α] [Enc β] [Enc α'] [Enc β'] {f : α → β}
    {f' : α' → β'} {e : α → α'} (he : ∀ a, Enc.encode (e a) = Enc.encode a)
    (hf : ∀ a, Enc.encode (f a) = Enc.encode (f' (e a)))
    (h : QuasiPolyTimeCleanAt K f') : QuasiPolyTimeCleanAt K f := by
  obtain ⟨P, T, hT, hP⟩ := h
  exact ⟨P, T, hT, hP.transfer he hf⟩

theorem PolyTimeCleanRelAt.transfer {K : ℕ} [Enc α] [Enc β] [Enc α'] [Enc β']
    {R : α → β → Prop} {R' : α' → β' → Prop} {e : α → α'}
    (he : ∀ a, Enc.encode (e a) = Enc.encode a)
    (hR : ∀ (a : α) (b' : β'), R' (e a) b' → ∃ b : β, Enc.encode b = Enc.encode b' ∧ R a b)
    (h : PolyTimeCleanRelAt K R') : PolyTimeCleanRelAt K R := by
  obtain ⟨P, T, hT, hP⟩ := h
  exact ⟨P, T, hT, hP.transfer he hR⟩

theorem QuasiPolyTimeCleanRelAt.transfer {K : ℕ} [Enc α] [Enc β] [Enc α'] [Enc β']
    {R : α → β → Prop} {R' : α' → β' → Prop} {e : α → α'}
    (he : ∀ a, Enc.encode (e a) = Enc.encode a)
    (hR : ∀ (a : α) (b' : β'), R' (e a) b' → ∃ b : β, Enc.encode b = Enc.encode b' ∧ R a b)
    (h : QuasiPolyTimeCleanRelAt K R') : QuasiPolyTimeCleanRelAt K R := by
  obtain ⟨P, T, hT, hP⟩ := h
  exact ⟨P, T, hT, hP.transfer he hR⟩

/-! ## Transfer of the size bound -/

theorem SizeBound.transfer [Enc α] [Enc β] [Enc α'] [Enc β'] {f : α → β} {f' : α' → β'}
    {e : α → α'} (he : ∀ a, Enc.encode (e a) = Enc.encode a)
    (hf : ∀ a, Enc.encode (f a) = Enc.encode (f' (e a))) (h : SizeBound f') : SizeBound f := by
  obtain ⟨c, d, hc⟩ := h
  refine ⟨c, d, fun a => ?_⟩
  have h1 : Enc.size (f a) = Enc.size (f' (e a)) := size_eq_of_encode_eq (hf a)
  have h2 : Enc.size (e a) = Enc.size a := size_eq_of_encode_eq (he a)
  have h3 := hc (e a)
  rw [h2] at h3
  omega

/-! ## Transfer of `PolyFun` -/

/-- **Transfer of `PolyFun` along equal encodings.** -/
theorem PolyFun.transfer [Enc α] [Enc β] [Enc α'] [Enc β'] {f : α → β} {f' : α' → β'}
    {e : α → α'} (he : ∀ a, Enc.encode (e a) = Enc.encode a)
    (hf : ∀ a, Enc.encode (f a) = Enc.encode (f' (e a))) (h : PolyFun f') : PolyFun f :=
  ⟨h.time.transfer he hf, h.size.transfer he hf⟩

/-- **Transfer of `QuasiPolyFun` along equal encodings.** -/
theorem QuasiPolyFun.transfer [Enc α] [Enc β] [Enc α'] [Enc β'] {f : α → β} {f' : α' → β'}
    {e : α → α'} (he : ∀ a, Enc.encode (e a) = Enc.encode a)
    (hf : ∀ a, Enc.encode (f a) = Enc.encode (f' (e a))) (h : QuasiPolyFun f') :
    QuasiPolyFun f :=
  ⟨h.time.transfer he hf, h.size.transfer he hf⟩

/-! ## A sanity example

The statements above are not vacuous: here is a type whose encoding is literally the encoding of
a list of naturals, and the transfer of `RAM.polyFun_length` to it.  The same three lines carry
every routine of the algorithmic layer from a raw type to the family `SIInput n s`. -/

namespace Transfer

/-- A list of naturals under another name. -/
structure Boxed where
  /-- The underlying list. -/
  val : List ℕ

instance : Enc Boxed where
  encode b := Enc.encode b.val
  encode_injective := by
    intro b b' h
    have : b.val = b'.val := Enc.encode_injective (α := List ℕ) h
    cases b; cases b'; simpa using this

/-- Unboxing does not change the encoding. -/
theorem encode_val (b : Boxed) : Enc.encode b.val = Enc.encode b := rfl

/-- **The sanity check.**  The length of a `Boxed` is a `PolyFun`, by transfer of
`RAM.polyFun_length` along `Boxed.val`.  No new machine code is involved. -/
theorem polyFun_boxedLength : PolyFun (fun b : Boxed => b.val.length) :=
  PolyFun.transfer (e := Boxed.val) (f' := fun l : List ℕ => l.length)
    (fun b => encode_val b) (fun _ => rfl) polyFun_length

end Transfer

end RAM
