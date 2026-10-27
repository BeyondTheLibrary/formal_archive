/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): folds and maps of routines
bounded at an external degree. Not part of the faithful formalization.
-/
import Workspace.Explicit.NodeBounded
import Workspace.Algo.AggNodeCheckedTraverse

/-!
# Folds and maps at an external degree

`Explicit.TN.foldl`, `Explicit.TN.map`, `Explicit.TN.mapParam`: the proofs of
`Algo.aggnQuasiFun_foldl` and `Algo.aggnQuasiFun_map` in the class `Explicit.TN`. The routine
mapped over a list needs its precondition only on the entries of the list.
-/

namespace Explicit

open RAM Algo

variable {α β γ σ : Type*}

namespace TN

variable [Enc α] [Enc β] [Enc γ] [Enc σ]

/-- **A list fold** with a bound on every intermediate accumulator. -/
theorem foldl {f : σ × α → σ} {PreF : ℕ → σ × α → Prop} {Pre : ℕ → σ × List α → Prop}
    {k : ℕ} (hf : TN f PreF k)
    (hacc : ∃ A b, ∀ n s, Pre n s → ∀ j,
      Enc.size ((s.2.take j).foldl (fun y a => f (y, a)) s.1) ≤ tsB A k b n (Enc.size s))
    (hP : ∀ n s, Pre n s → ∀ j (a : α), s.2[j]? = some a →
      PreF n ((s.2.take j).foldl (fun y a => f (y, a)) s.1, a)) :
    TN (fun s : σ × List α => s.2.foldl (fun y a => f (y, a)) s.1) Pre k := by
  -- one step of the fold, through a case analysis on the list
  have hg : TN (fun x : σ => (x, ([] : List α))) (fun _ _ => True) k :=
    ofPoly (polyFun_id.pair polyFun_nil) _ _
  have hh : TN (fun q : (α × List α) × σ => (f (q.2, q.1.1), q.1.2))
      (fun n q => PreF n (q.2, q.1.1)) k :=
    (poly_comp (polyFun_snd.pair (polyFun_fst.comp polyFun_fst)) hf).pair
      (ofPoly (polyFun_fst.comp polyFun_snd) _ _)
  have hcases := listCases (Pre := fun n (p : List α × σ) => ∀ a l, p.1 = a :: l → PreF n (p.2, a))
    hg hh (fun _ _ _ => trivial) (fun n x l s h => h x l rfl)
  have hstep : TN (foldlStep f) (fun n s => ∀ a l, s.2 = a :: l → PreF n (s.1, a)) k :=
    (poly_comp polyFun_swap hcases).of_eq (fun ⟨x, r⟩ => by cases r <;> rfl)
  have hstep' : TN (fun x : ℕ × (σ × List α) => (x.1 - 1, foldlStep f x.2))
      (fun n x => ∀ a l, x.2.2 = a :: l → PreF n (x.2.1, a)) k :=
    (ofPoly (polyFun_fst.sub (polyFun_const 1)) _ _).pair (poly_comp polyFun_snd hstep)
  obtain ⟨A, b, hacc⟩ := hacc
  have hB : Bounded (fun n (s : σ × List α) => 2 * (Enc.size s + 2) +
      2 * (2 * tsB A k b n (Enc.size s) + 2 * Enc.size s)) Pre k :=
    ((Bounded.const 2).mul (Bounded.size.add (Bounded.const 2))).add ((Bounded.const 2).mul
      (((Bounded.const 2).mul ⟨A, b, fun _ _ _ => le_rfl⟩).add
        ((Bounded.const 2).mul Bounded.size)))
  obtain ⟨A', b', hB⟩ := hB
  refine (iterateSetup (setUp := fun s : σ × List α => (s.2.length, s))
    (readOff := fun s : σ × List α => s.1) (Prer := fun _ _ => True)
    (ofPoly ((polyFun_snd.comp polyFun_length).pair polyFun_id) _ _) hstep'
    (ofPoly (polyFun_snd.comp polyFun_fst) _ _)
    (Bounded.size.mono fun n s _ => (length_le_size s.2).trans (size_snd_le' s))
    ⟨A', b', fun n s hs j hj => ?_⟩ (fun n s hs j hj => ?_) (fun _ _ _ => trivial)).of_eq
    (fun ⟨x, r⟩ => by simp only [foldlStep_iterate, List.take_length])
  · obtain ⟨x, r⟩ := s
    refine le_trans ?_ (hB n _ hs)
    dsimp only
    rw [foldlStep_iterate]
    have h1 := Combine.size_pair_le (r.length - j)
      (List.foldl (fun y a => f (y, a)) x (r.take j), r.drop j)
    have h2 := Combine.size_pair_le (List.foldl (fun y a => f (y, a)) x (r.take j)) (r.drop j)
    have h3 := hacc n (x, r) hs j
    have h4 := (size_drop_le j r).trans (size_snd_le' (x, r))
    have h5 : Enc.size (r.length - j) ≤ Enc.size (x, r) + 2 := by
      rw [Small.size_nat]
      have := size_le_self (r.length - j)
      have := (length_le_size r).trans (size_snd_le' (x, r))
      omega
    dsimp only at h3
    omega
  · obtain ⟨x, r⟩ := s
    intro a l he
    dsimp only at he hj ⊢
    rw [foldlStep_iterate] at he ⊢
    dsimp only at he ⊢
    apply hP n (x, r) hs j a
    rw [List.drop_eq_getElem_cons hj] at he
    rw [List.getElem?_eq_getElem hj]
    exact congrArg some (List.cons.inj he).1

/-- **Mapping a routine over a list**: the routine meets its precondition on every entry. -/
theorem map {g : α → β} {PreG : ℕ → α → Prop} {k : ℕ} (hg : TN g PreG k) :
    TN (fun l : List α => l.map g) (fun n l => ∀ a ∈ l, PreG n a) k := by
  obtain ⟨Ag, bg, hgB⟩ := hg
  have hs := hgB.size
  have hcons : TN (fun z : List β × α => g z.2 :: z.1) (fun n z => PreG n z.2) k :=
    ((poly_comp polyFun_snd ⟨Ag, bg, hgB⟩).pair (ofPoly polyFun_fst _ _)).comp_poly polyFun_cons
  have hfold := foldl (Pre := fun n (s : List β × List α) => ∀ a ∈ s.2, PreG n a) hcons
    ⟨Ag + 5, bg + 1, fun n s hs' j => ?_⟩ (fun n s hs' j a ha => hs' a (List.mem_of_getElem? ha))
  · refine ((ofPoly (polyFun_nil.pair polyFun_id) _ _).comp hfold (fun n l h => h)).comp_poly
      polyFun_reverse |>.of_eq (fun l => by rw [foldl_map_cons_eq]; simp)
  · obtain ⟨x, r⟩ := s
    dsimp only
    have h1 := size_foldl_map_cons_le g (r.take j) x
    have hS : ∀ c ∈ (r.take j).map g, Enc.size c ≤ tsB Ag k bg n (Enc.size (x, r)) := by
      intro c hc
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
      have hmem := List.mem_of_mem_take ha
      exact (hs n a (hs' a hmem)).trans (tsB_mono le_rfl le_rfl le_rfl le_rfl
        ((size_mem_le hmem).trans (size_snd_le' (x, r))))
    have h2 := size_list_le_of_entries _ _ hS
    rw [List.length_map] at h2
    have h3 : (r.take j).length ≤ Enc.size (x, r) :=
      (List.length_take_le' _ _).trans ((length_le_size r).trans (size_snd_le' (x, r)))
    have h4 : Enc.size x ≤ Enc.size (x, r) := size_fst_le' (x, r)
    generalize Enc.size (x, r) = S at *
    generalize hT : tsB Ag k bg n S = T at *
    have h5 := Nat.mul_le_mul h3 (le_refl (2 * T + 1))
    have h6 : S ≤ tsB 0 k 1 n S := self_le_tsB k n _
    have h7 := tsB_mul 0 Ag k 1 bg n S
    rw [Nat.zero_add, Nat.add_comm 1 bg, hT] at h7
    have h8 := mul_tsB_le 5 Ag k (bg + 1) n S
    have hT1 : 1 ≤ T := hT ▸ one_le_tsB Ag k bg n S
    have hST : S * T ≤ tsB Ag k (bg + 1) n S := (Nat.mul_le_mul_right T h6).trans h7.le
    have hSU : S ≤ tsB Ag k (bg + 1) n S := (Nat.le_mul_of_pos_right S hT1).trans hST
    have h1U := one_le_tsB Ag k (bg + 1) n S
    have he : S * (2 * T + 1) = 2 * (S * T) + S := by ring
    omega

/-- **Mapping a routine with a fixed parameter.** -/
theorem mapParam {f : γ × α → β} {PreF : ℕ → γ × α → Prop} {k : ℕ} (hf : TN f PreF k) :
    TN (fun p : γ × List α => p.2.map (fun a => f (p.1, a)))
      (fun n p => ∀ a ∈ p.2, PreF n (p.1, a)) k :=
  ((ofPoly (PolyFun.mapParam (polyFun_id (α := γ × α))) _ _).comp (map hf) (fun n p h q hq => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hq
    exact h a ha)).of_eq (fun p => by simp only [List.map_map]; rfl)

/-- **A flat map with a fixed parameter.** -/
theorem flatMapParam {f : γ × α → List β} {PreF : ℕ → γ × α → Prop} {k : ℕ}
    (hf : TN f PreF k) :
    TN (fun p : γ × List α => p.2.flatMap (fun a => f (p.1, a)))
      (fun n p => ∀ a ∈ p.2, PreF n (p.1, a)) k :=
  ((mapParam hf).comp_poly polyFun_flatten).of_eq (fun p => by simp [List.flatMap])

end TN

end Explicit
