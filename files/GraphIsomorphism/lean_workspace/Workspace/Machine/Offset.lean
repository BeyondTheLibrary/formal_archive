import Workspace.Machine.Compose

/-!
# The workspace convention

The top-level convention of `Workspace/Machine/Encoding.lean` puts the length of the input in
register `0` and the entries in registers `1, ..., n`.  For an input longer than every constant
occurring in a program, *no register with a fixed index is free*: a routine cannot even set a
loop counter without destroying a register that still holds live data.  This is the obstacle
recorded in the "Doubts" section of `Workspace/Machine/DESIGN.md`.

The way out, decided for this layer, is to keep the top-level convention exactly as it is and to
do all the assembly work in a **workspace convention** with `K` free registers at the bottom:

`initMemAt K l`: registers `0, ..., K - 1` hold `0` (they are the workspace), register `K` holds
`l.length`, registers `K + 1, ..., K + n` hold the entries, and every other register holds `0`.

`initMemAt 0 = initMem`, so the workspace convention is a generalization of the top-level one.
The clean classes are repeated at the workspace convention (`CleanComputeAt`, `PolyTimeCleanAt`,
`QuasiPolyTimeCleanAt`), with the same proofs of the same closure facts; the link between the two
conventions is `Workspace/Machine/Reloc.lean` (upwards, by relocation) and — still missing — the
bootstrap described in `DESIGN.md` (downwards).

## Main definitions and results

* `RAM.initMemAt`, `RAM.initMemAt_zero`, `RAM.eq_initMemAt` (the shape in which a routine proves
  that it has produced a workspace memory);
* `RAM.CleanComputeAt`, `RAM.CleanSolveAt`, `RAM.PolyTimeCleanAt`, `RAM.QuasiPolyTimeCleanAt`;
* `RAM.cleanComputeAt_zero`: at `K = 0` these are the classes of `Compose.lean`;
* `RAM.CleanComputeAt.comp`, `RAM.PolyTimeCleanAt.comp`, `RAM.QuasiPolyTimeCleanAt.comp` and the
  relational forms: the closure of the workspace classes under composition.
-/

namespace RAM

variable {α β γ : Type*}

/-! ## The memory convention -/

/-- The initial memory of the workspace convention: `K` zeroed work registers, then the input in
the ordinary convention starting at register `K`. -/
def initMemAt (K : ℕ) (l : List ℕ) : Mem := fun a => if a < K then 0 else initMem l (a - K)

@[simp] theorem initMemAt_zero (l : List ℕ) : initMemAt 0 l = initMem l := by
  funext a; simp [initMemAt]

theorem initMemAt_of_lt {K : ℕ} (l : List ℕ) {a : ℕ} (h : a < K) : initMemAt K l a = 0 := by
  simp [initMemAt, h]

@[simp] theorem initMemAt_add (K : ℕ) (l : List ℕ) (x : ℕ) :
    initMemAt K l (K + x) = initMem l x := by
  simp only [initMemAt, if_neg (by omega : ¬ K + x < K)]
  congr 1
  omega

/-- The criterion a routine uses to prove that it has produced a workspace memory: the work
registers are zero, and the rest of the memory is the ordinary initial memory shifted by `K`. -/
theorem eq_initMemAt {m : Mem} {K : ℕ} {l : List ℕ} (hlow : ∀ z, z < K → m z = 0)
    (hhigh : ∀ x, m (K + x) = initMem l x) : m = initMemAt K l := by
  funext z
  rcases Nat.lt_or_ge z K with h | h
  · rw [hlow z h, initMemAt_of_lt l h]
  · have hz : z = K + (z - K) := by omega
    rw [hz, hhigh, initMemAt_add]

/-! ## The clean classes at the workspace convention -/

/-- `CleanComputeAt K P f T`: started in `initMemAt K (encode a)`, the program halts within
`T (Enc.size a)` steps in exactly `initMemAt K (encode (f a))`.  The work registers are zero
before and after, so these programs compose by concatenation exactly as the clean programs of
`Workspace/Machine/Compose.lean` do. -/
def CleanComputeAt (K : ℕ) [Enc α] [Enc β] (P : Program) (f : α → β) (T : ℕ → ℕ) : Prop :=
  ∀ a : α, RunsTo P (fun m => m = initMemAt K (Enc.encode a))
    (fun m' => m' = initMemAt K (Enc.encode (f a))) (T (Enc.size a))

/-- The relational form: the program halts cleanly holding *some* admissible answer. -/
def CleanSolveAt (K : ℕ) [Enc α] [Enc β] (P : Program) (R : α → β → Prop) (T : ℕ → ℕ) : Prop :=
  ∀ a : α, ∃ b : β, R a b ∧ RunsTo P (fun m => m = initMemAt K (Enc.encode a))
    (fun m' => m' = initMemAt K (Enc.encode b)) (T (Enc.size a))

/-- At `K = 0` the workspace convention is the top-level convention. -/
theorem cleanComputeAt_zero [Enc α] [Enc β] {P : Program} {f : α → β} {T : ℕ → ℕ} :
    CleanComputeAt 0 P f T ↔ CleanCompute P f T := by
  simp only [CleanComputeAt, CleanCompute, initMemAt_zero]

theorem cleanSolveAt_zero [Enc α] [Enc β] {P : Program} {R : α → β → Prop} {T : ℕ → ℕ} :
    CleanSolveAt 0 P R T ↔ CleanSolve P R T := by
  simp only [CleanSolveAt, CleanSolve, initMemAt_zero]

theorem CleanComputeAt.mono {K : ℕ} [Enc α] [Enc β] {P : Program} {f : α → β} {T T' : ℕ → ℕ}
    (h : CleanComputeAt K P f T) (hT : ∀ n, T n ≤ T' n) : CleanComputeAt K P f T' :=
  fun a => (h a).mono (hT _)

theorem CleanSolveAt.mono {K : ℕ} [Enc α] [Enc β] {P : Program} {R : α → β → Prop} {T T' : ℕ → ℕ}
    (h : CleanSolveAt K P R T) (hT : ∀ n, T n ≤ T' n) : CleanSolveAt K P R T' := by
  intro a
  obtain ⟨b, hb, hrun⟩ := h a
  exact ⟨b, hb, hrun.mono (hT _)⟩

theorem CleanComputeAt.cleanSolveAt {K : ℕ} [Enc α] [Enc β] {P : Program} {f : α → β}
    {T : ℕ → ℕ} (h : CleanComputeAt K P f T) :
    CleanSolveAt K P (fun a b => b = f a) T := fun a => ⟨f a, rfl, h a⟩

/-! ## Composition

Word for word the composition of `Compose.lean`: the intermediate result is delivered in exactly
the memory the second routine expects, so the programs are concatenated and the times add. -/

theorem CleanComputeAt.comp {K : ℕ} [Enc α] [Enc β] [Enc γ] {P Q : Program} {f : α → β}
    {g : β → γ} {T₁ T₂ S : ℕ → ℕ} (hP : CleanComputeAt K P f T₁) (hQ : CleanComputeAt K Q g T₂)
    (hT₂ : ∀ n n', n ≤ n' → T₂ n ≤ T₂ n') (hS : ∀ a, Enc.size (f a) ≤ S (Enc.size a)) :
    CleanComputeAt K (seq P Q) (fun a => g (f a)) (fun n => T₁ n + T₂ (S n)) := by
  intro a
  exact ((hP a).seq (hQ (f a))).mono (Nat.add_le_add_left (hT₂ _ _ (hS a)) _)

theorem CleanSolveAt.comp {K : ℕ} [Enc α] [Enc β] [Enc γ] {P Q : Program} {R : α → β → Prop}
    {R' : β → γ → Prop} {T₁ T₂ S : ℕ → ℕ} (hP : CleanSolveAt K P R T₁)
    (hQ : CleanSolveAt K Q R' T₂) (hT₂ : ∀ n n', n ≤ n' → T₂ n ≤ T₂ n')
    (hS : ∀ a b, R a b → Enc.size b ≤ S (Enc.size a)) :
    CleanSolveAt K (seq P Q) (fun a c => ∃ b, R a b ∧ R' b c) (fun n => T₁ n + T₂ (S n)) := by
  intro a
  obtain ⟨b, hb, hrun⟩ := hP a
  obtain ⟨c, hc, hrun'⟩ := hQ b
  exact ⟨c, ⟨b, hb, hc⟩,
    (hrun.seq hrun').mono (Nat.add_le_add_left (hT₂ _ _ (hS a b hb)) _)⟩

/-! ## The time classes at the workspace convention -/

/-- A function computed in polynomial time by a clean program of the workspace convention. -/
def PolyTimeCleanAt (K : ℕ) [Enc α] [Enc β] (f : α → β) : Prop :=
  ∃ (P : Program) (T : ℕ → ℕ), PolyBound T ∧ CleanComputeAt K P f T

/-- A function computed in quasipolynomial time by a clean program of the workspace
convention. -/
def QuasiPolyTimeCleanAt (K : ℕ) [Enc α] [Enc β] (f : α → β) : Prop :=
  ∃ (P : Program) (T : ℕ → ℕ), QuasiPolyBound T ∧ CleanComputeAt K P f T

/-- A search problem solved in polynomial time at the workspace convention. -/
def PolyTimeCleanRelAt (K : ℕ) [Enc α] [Enc β] (R : α → β → Prop) : Prop :=
  ∃ (P : Program) (T : ℕ → ℕ), PolyBound T ∧ CleanSolveAt K P R T

/-- A search problem solved in quasipolynomial time at the workspace convention. -/
def QuasiPolyTimeCleanRelAt (K : ℕ) [Enc α] [Enc β] (R : α → β → Prop) : Prop :=
  ∃ (P : Program) (T : ℕ → ℕ), QuasiPolyBound T ∧ CleanSolveAt K P R T

theorem polyTimeCleanAt_zero [Enc α] [Enc β] {f : α → β} :
    PolyTimeCleanAt 0 f ↔ PolyTimeClean f := by
  simp only [PolyTimeCleanAt, PolyTimeClean, cleanComputeAt_zero]

theorem quasiPolyTimeCleanAt_zero [Enc α] [Enc β] {f : α → β} :
    QuasiPolyTimeCleanAt 0 f ↔ QuasiPolyTimeClean f := by
  simp only [QuasiPolyTimeCleanAt, QuasiPolyTimeClean, cleanComputeAt_zero]

theorem PolyTimeCleanAt.quasiPolyTimeCleanAt {K : ℕ} [Enc α] [Enc β] {f : α → β}
    (h : PolyTimeCleanAt K f) : QuasiPolyTimeCleanAt K f := by
  obtain ⟨P, T, hT, hP⟩ := h
  exact ⟨P, T, hT.quasiPoly, hP⟩

/-- **Composition in polynomial time**, at the workspace convention. -/
theorem PolyTimeCleanAt.comp {K : ℕ} [Enc α] [Enc β] [Enc γ] {f : α → β} {g : β → γ} {S : ℕ → ℕ}
    (hf : PolyTimeCleanAt K f) (hg : PolyTimeCleanAt K g) (hSpoly : PolyBound S)
    (hS : ∀ a, Enc.size (f a) ≤ S (Enc.size a)) : PolyTimeCleanAt K (fun a => g (f a)) := by
  obtain ⟨P, T₁, hT₁, hP⟩ := hf
  obtain ⟨Q, T₂, ⟨c, d, hc⟩, hQ⟩ := hg
  refine ⟨seq P Q, fun n => T₁ n + c * (S n + 1) ^ d,
    hT₁.add ((polyBound_witness c d).comp hSpoly), ?_⟩
  exact hP.comp (T₂ := fun n => c * (n + 1) ^ d) (hQ.mono hc)
    (fun _ _ h => polyBound_witness_mono c d h) hS

/-- **Composition in quasipolynomial time**, at the workspace convention. -/
theorem QuasiPolyTimeCleanAt.comp {K : ℕ} [Enc α] [Enc β] [Enc γ] {f : α → β} {g : β → γ}
    {S : ℕ → ℕ} (hf : QuasiPolyTimeCleanAt K f) (hg : QuasiPolyTimeCleanAt K g)
    (hSpoly : PolyBound S) (hS : ∀ a, Enc.size (f a) ≤ S (Enc.size a)) :
    QuasiPolyTimeCleanAt K (fun a => g (f a)) := by
  obtain ⟨P, T₁, hT₁, hP⟩ := hf
  obtain ⟨Q, T₂, ⟨c, hc⟩, hQ⟩ := hg
  refine ⟨seq P Q, fun n => T₁ n + 2 ^ ((Nat.log 2 (S n) + 2) ^ c),
    hT₁.add ((quasiPolyBound_witness c).comp_poly hSpoly), ?_⟩
  exact hP.comp (T₂ := fun n => 2 ^ ((Nat.log 2 n + 2) ^ c)) (hQ.mono hc)
    (fun _ _ h => quasiPolyBound_witness_mono c h) hS

/-- **Composition in quasipolynomial time with a quasipolynomially large intermediate result.**
This is the sharper form made possible by `RAM.QuasiPolyBound.comp`
(`Workspace/Machine/TimeClasses.lean`): the bound on the size of the intermediate result need
only be quasipolynomial, since a quasipolynomial cost evaluated at a quasipolynomially bounded
size is again quasipolynomial. -/
theorem QuasiPolyTimeCleanAt.comp_quasiSize {K : ℕ} [Enc α] [Enc β] [Enc γ] {f : α → β}
    {g : β → γ} {S : ℕ → ℕ} (hf : QuasiPolyTimeCleanAt K f) (hg : QuasiPolyTimeCleanAt K g)
    (hSq : QuasiPolyBound S) (hS : ∀ a, Enc.size (f a) ≤ S (Enc.size a)) :
    QuasiPolyTimeCleanAt K (fun a => g (f a)) := by
  obtain ⟨P, T₁, hT₁, hP⟩ := hf
  obtain ⟨Q, T₂, ⟨c, hc⟩, hQ⟩ := hg
  refine ⟨seq P Q, fun n => T₁ n + 2 ^ ((Nat.log 2 (S n) + 2) ^ c),
    hT₁.add ((quasiPolyBound_witness c).comp hSq), ?_⟩
  exact hP.comp (T₂ := fun n => 2 ^ ((Nat.log 2 n + 2) ^ c)) (hQ.mono hc)
    (fun _ _ h => quasiPolyBound_witness_mono c h) hS

/-- The relational form of `RAM.QuasiPolyTimeCleanAt.comp_quasiSize`. -/
theorem QuasiPolyTimeCleanRelAt.comp_quasiSize {K : ℕ} [Enc α] [Enc β] [Enc γ]
    {R : α → β → Prop} {R' : β → γ → Prop} {S : ℕ → ℕ} (hR : QuasiPolyTimeCleanRelAt K R)
    (hR' : QuasiPolyTimeCleanRelAt K R') (hSq : QuasiPolyBound S)
    (hS : ∀ a b, R a b → Enc.size b ≤ S (Enc.size a)) :
    QuasiPolyTimeCleanRelAt K (fun a c => ∃ b, R a b ∧ R' b c) := by
  obtain ⟨P, T₁, hT₁, hP⟩ := hR
  obtain ⟨Q, T₂, ⟨c, hc⟩, hQ⟩ := hR'
  refine ⟨seq P Q, fun n => T₁ n + 2 ^ ((Nat.log 2 (S n) + 2) ^ c),
    hT₁.add ((quasiPolyBound_witness c).comp hSq), ?_⟩
  exact hP.comp (T₂ := fun n => 2 ^ ((Nat.log 2 n + 2) ^ c)) (hQ.mono hc)
    (fun _ _ h => quasiPolyBound_witness_mono c h) hS

theorem QuasiPolyTimeCleanAt.comp_poly {K : ℕ} [Enc α] [Enc β] [Enc γ] {f : α → β} {g : β → γ}
    {S : ℕ → ℕ} (hf : QuasiPolyTimeCleanAt K f) (hg : PolyTimeCleanAt K g) (hSpoly : PolyBound S)
    (hS : ∀ a, Enc.size (f a) ≤ S (Enc.size a)) : QuasiPolyTimeCleanAt K (fun a => g (f a)) :=
  hf.comp hg.quasiPolyTimeCleanAt hSpoly hS

theorem PolyTimeCleanAt.comp_quasi {K : ℕ} [Enc α] [Enc β] [Enc γ] {f : α → β} {g : β → γ}
    {S : ℕ → ℕ} (hf : PolyTimeCleanAt K f) (hg : QuasiPolyTimeCleanAt K g) (hSpoly : PolyBound S)
    (hS : ∀ a, Enc.size (f a) ≤ S (Enc.size a)) : QuasiPolyTimeCleanAt K (fun a => g (f a)) :=
  hf.quasiPolyTimeCleanAt.comp hg hSpoly hS

/-- The relational form of closure under composition in polynomial time. -/
theorem PolyTimeCleanRelAt.comp {K : ℕ} [Enc α] [Enc β] [Enc γ] {R : α → β → Prop}
    {R' : β → γ → Prop} {S : ℕ → ℕ} (hR : PolyTimeCleanRelAt K R)
    (hR' : PolyTimeCleanRelAt K R') (hSpoly : PolyBound S)
    (hS : ∀ a b, R a b → Enc.size b ≤ S (Enc.size a)) :
    PolyTimeCleanRelAt K (fun a c => ∃ b, R a b ∧ R' b c) := by
  obtain ⟨P, T₁, hT₁, hP⟩ := hR
  obtain ⟨Q, T₂, ⟨c, d, hc⟩, hQ⟩ := hR'
  refine ⟨seq P Q, fun n => T₁ n + c * (S n + 1) ^ d,
    hT₁.add ((polyBound_witness c d).comp hSpoly), ?_⟩
  exact hP.comp (T₂ := fun n => c * (n + 1) ^ d) (hQ.mono hc)
    (fun _ _ h => polyBound_witness_mono c d h) hS

/-- The relational form of closure under composition in quasipolynomial time. -/
theorem QuasiPolyTimeCleanRelAt.comp {K : ℕ} [Enc α] [Enc β] [Enc γ] {R : α → β → Prop}
    {R' : β → γ → Prop} {S : ℕ → ℕ} (hR : QuasiPolyTimeCleanRelAt K R)
    (hR' : QuasiPolyTimeCleanRelAt K R') (hSpoly : PolyBound S)
    (hS : ∀ a b, R a b → Enc.size b ≤ S (Enc.size a)) :
    QuasiPolyTimeCleanRelAt K (fun a c => ∃ b, R a b ∧ R' b c) := by
  obtain ⟨P, T₁, hT₁, hP⟩ := hR
  obtain ⟨Q, T₂, ⟨c, hc⟩, hQ⟩ := hR'
  refine ⟨seq P Q, fun n => T₁ n + 2 ^ ((Nat.log 2 (S n) + 2) ^ c),
    hT₁.add ((quasiPolyBound_witness c).comp_poly hSpoly), ?_⟩
  exact hP.comp (T₂ := fun n => 2 ^ ((Nat.log 2 n + 2) ^ c)) (hQ.mono hc)
    (fun _ _ h => quasiPolyBound_witness_mono c h) hS

/-- The identity is computed by the empty program at every workspace convention. -/
theorem cleanComputeAt_id (K : ℕ) [Enc α] : CleanComputeAt K [] (id : α → α) (fun _ => 0) :=
  fun _ => runsTo_nil (fun _ hm => hm)

theorem polyTimeCleanAt_id (K : ℕ) [Enc α] : PolyTimeCleanAt K (id : α → α) :=
  ⟨[], fun _ => 0, polyBound_const 0, cleanComputeAt_id K⟩

end RAM
