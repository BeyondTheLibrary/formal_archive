import Workspace.Machine.Targets
import Workspace.Machine.ListOps2
import Workspace.Luks.GraphToString

/-!
# The Graph Isomorphism target

The input is two simple graphs on `Fin n`. Each graph is encoded by its full
adjacency matrix: `n` lists of `n` natural numbers, each equal to zero or one.
This retains the vertex count even for graphs with no edges. There are `2n²`
bits before list framing, whose overhead is also polynomial in `n`.
-/

namespace RAM.Targets

open Classical

/-- The full adjacency matrix, with zero on the diagonal. -/
noncomputable def graphMatrix {n : ℕ} (X : SimpleGraph (Fin n)) : List (List ℕ) :=
  List.ofFn fun u => List.ofFn fun v => if X.Adj u v then 1 else 0

@[simp] theorem graphMatrix_length {n : ℕ} (X : SimpleGraph (Fin n)) :
    (graphMatrix X).length = n := by simp [graphMatrix]

theorem graphMatrix_injective {n : ℕ} :
    Function.Injective (graphMatrix : SimpleGraph (Fin n) → List (List ℕ)) := by
  intro X Y h
  have hrow := List.ofFn_injective h
  apply SimpleGraph.ext
  funext u v
  apply propext
  have hbit := congrFun (List.ofFn_injective (congrFun hrow u)) v
  change (if X.Adj u v then 1 else 0 : ℕ) = (if Y.Adj u v then 1 else 0) at hbit
  by_cases hx : X.Adj u v <;> by_cases hy : Y.Adj u v <;> simp_all

/-- An input of Graph Isomorphism, with an adjacency-matrix encoding. -/
structure GIInput (n : ℕ) where
  X : SimpleGraph (Fin n)
  Y : SimpleGraph (Fin n)

/-- The two adjacency matrices seen by the machine. -/
noncomputable def GIInput.raw {n : ℕ} (a : GIInput n) : List (List ℕ) × List (List ℕ) :=
  (graphMatrix a.X, graphMatrix a.Y)

noncomputable instance {n : ℕ} : Enc (GIInput n) where
  encode a := Enc.encode a.raw
  encode_injective := by
    intro a b h
    have h' : a.raw = b.raw := Enc.encode_injective h
    have hX := graphMatrix_injective (congrArg Prod.fst h')
    have hY := graphMatrix_injective (congrArg Prod.snd h')
    cases a; cases b
    simp_all [GIInput.raw]

@[simp] theorem GIInput.encode_raw {n : ℕ} (a : GIInput n) :
    Enc.encode a.raw = Enc.encode a := rfl

/-- The framing of rows and bits adds only a quadratic amount of data. -/
theorem graphMatrix_size {n : ℕ} (X : SimpleGraph (Fin n)) :
    Enc.size (graphMatrix X) ≤ 1 + n * (2 * (1 + 7 * n) + 1) := by
  have hrow : ∀ row ∈ graphMatrix X, Enc.size row ≤ 1 + 7 * n := by
    intro row hr
    rw [graphMatrix, List.mem_ofFn'] at hr
    obtain ⟨u, rfl⟩ := hr
    have hbit : ∀ b ∈ (List.ofFn fun v : Fin n => if X.Adj u v then 1 else 0 : List ℕ),
        Enc.size b ≤ 3 := by
      intro b hb
      rw [List.mem_ofFn'] at hb
      obtain ⟨v, rfl⟩ := hb
      dsimp only
      split <;> decide
    simpa [Nat.mul_comm] using size_list_le_of_entries _ 3 hbit
  simpa using size_list_le_of_entries _ (1 + 7 * n) hrow

/-- Input size and the vertex count are polynomially related. -/
theorem GIInput.size_bounds {n : ℕ} (a : GIInput n) :
    n ≤ Enc.size a ∧ Enc.size a ≤ 4 * (1 + n * (2 * (1 + 7 * n) + 1)) := by
  have h₁ := graphMatrix_size a.X
  have h₂ := graphMatrix_size a.Y
  have h₃ := size_pair_le' a.raw
  have h₄ := (length_le_size (graphMatrix a.X)).trans (size_fst_le' a.raw)
  change n ≤ Enc.size a.raw ∧ Enc.size a.raw ≤ _
  dsimp only [GIInput.raw] at h₃ h₄ ⊢
  rw [graphMatrix_length] at h₄
  exact ⟨h₄, by omega⟩

/-- **Corollary 1.1.2, Sec. 1.1, GI part.** One RAM program decides graph
isomorphism within one quasipolynomial bound, uniformly in the vertex count. -/
def Corollary_1_1_2_GI_statement : Prop :=
  ∃ (P : Program) (T : ℕ → ℕ), QuasiPolyBound T ∧ ∀ n : ℕ,
    ∃ f : GIInput n → Bool,
      (∀ a, f a = true ↔ (Babai.GraphToString.Iso a.X a.Y).Nonempty) ∧
        ComputesInTime P f T

end RAM.Targets
