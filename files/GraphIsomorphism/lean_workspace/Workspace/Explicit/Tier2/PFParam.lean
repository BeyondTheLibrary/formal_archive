/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), tier 2: traversals with a
parameter, with explicit constants. Not part of the faithful formalization.
-/
import Workspace.Explicit.Tier2.PFSize

/-!
# Traversals with a parameter, with explicit constants

The `Explicit.PF` forms of `RAM.polyFun_rangeLength`, `RAM.PolyFun.mapParam`,
`RAM.PolyFun.filterParam` and `RAM.PolyFun.foldlParam`, proved as the machine lemmas.

The combinators with a hypothesis are stated through `Explicit.PFB`, a routine together with
its four constants: the constants are the closed expressions produced by the rules of
`Explicit.PF`, read off the proof. At a fixed routine they evaluate to numerals, which the
concrete lemmas state.
-/

namespace Explicit

open RAM

variable {α β γ σ : Type*} [Enc α] [Enc β] [Enc γ] [Enc σ]

/-- **A routine with its four constants.** -/
structure PFB (f : α → β) where
  k : ℕ
  d : ℕ
  s : ℕ
  e : ℕ
  pf : PF f k d s e

/-- The constants of `PFB.of h` are those of the type of `h`. -/
def PFB.of {f : α → β} {k d s e : ℕ} (h : PF f k d s e) : PFB f := ⟨k, d, s, e, h⟩

/-- `(4 N + 1)^e ≤ 2^{2e} (N + 1)^e`. -/
theorem four_mul_pow_le (N e : ℕ) : (4 * N + 1) ^ e ≤ 2 ^ (2 * e) * (N + 1) ^ e := by
  calc (4 * N + 1) ^ e ≤ (4 * (N + 1)) ^ e := Nat.pow_le_pow_left (by omega) e
    _ = 2 ^ (2 * e) * (N + 1) ^ e := by rw [mul_pow, pow_mul]; norm_num

/-- `RAM.polyFun_rangeLength`. -/
theorem pf_rangeLength : PF (fun l : List α => List.range l.length) 465 5 28 2 := by
  have hstep := ((PF.fst (α := List ℕ) (β := α)).comp pf_length).pair
    (PF.fst (α := List ℕ) (β := α)) |>.comp (pf_cons (β := ℕ))
  have hfold := PF.foldl (ka := 4) (da := 2) (f := rangeStep) hstep (fun x r j => by
    have h := rangeStep_size_bound x r j
    set N := Enc.size ((x, r) : List ℕ × List α)
    have e1 : 2 ^ 4 * (N + 1) ^ 2 = 16 * (N * N) + 32 * N + 16 := by ring
    have e2 : N * (4 * N + 5) = 4 * (N * N) + 5 * N := by ring
    rw [e1]
    omega)
  have h := (((PF.const (α := List α) ([] : List ℕ)).pair PF.id).comp hfold).comp pf_reverse
  exact h.of_eq (fun l => by
    show (List.foldl (fun y a => rangeStep (y, a)) ([] : List ℕ) l).reverse = _
    rw [rangeStep_result]
    simp [List.range_eq_range'])

/-- `RAM.PolyFun.mapParam`. -/
def PF.mapParamB {f : γ × α → β} {k d s e : ℕ} (hf : PF f k d s e) :
    PFB (fun p : γ × List α => p.2.map (fun a => f (p.1, a))) := PFB.of <| by
  have hstep := ((PF.fst (α := γ × List β) (β := α)).comp PF.fst).pair
    ((((((PF.fst (α := γ × List β) (β := α)).comp PF.fst).pair PF.snd).comp hf).pair
      ((PF.fst (α := γ × List β) (β := α)).comp PF.snd)).comp (pf_cons (β := β)))
  have hfold := PF.foldl (ka := s + 2 * e + 4) (da := e + 1)
    (f := fun z : (γ × List β) × α => ((z.1.1, f (z.1.1, z.2) :: z.1.2) : γ × List β)) hstep
    (fun x r j => by
      rw [foldl_mapParam_eq]
      set N := Enc.size ((x, r) : (γ × List β) × List α) with hN
      have hx : Enc.size x ≤ N := Combine.size_fst_le x r
      have hr : Enc.size r ≤ N := Combine.size_snd_le x r
      have hx1 : Enc.size x.1 ≤ Enc.size x := size_fst_le' x
      have hx2 : Enc.size x.2 ≤ Enc.size x := size_snd_le' x
      have hrt : Enc.size (r.take j) ≤ Enc.size r := size_take_le j r
      set S := 2 ^ (s + 2 * e) * (N + 1) ^ e with hS
      have hentry : ∀ b ∈ (r.take j).map (fun a => f (x.1, a)), Enc.size b ≤ S := by
        intro b hb
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
        have h1 : Enc.size a ≤ Enc.size (r.take j) := size_mem_le ha
        have h3 : Enc.size ((x.1, a) : γ × α) ≤ 2 * Enc.size x.1 + 2 * Enc.size a :=
          Combine.size_pair_le _ _
        have h5 : (Enc.size ((x.1, a) : γ × α) + 1) ^ e ≤ (4 * N + 1) ^ e :=
          Nat.pow_le_pow_left (by omega) e
        calc Enc.size (f (x.1, a)) ≤ 2 ^ s * (Enc.size ((x.1, a) : γ × α) + 1) ^ e :=
              hf.size _
          _ ≤ 2 ^ s * (2 ^ (2 * e) * (N + 1) ^ e) :=
              Nat.mul_le_mul_left _ (h5.trans (four_mul_pow_le N e))
          _ = S := by rw [hS, pow_add]; ring
      have hmap : Enc.size ((r.take j).map (fun a => f (x.1, a))) ≤ 1 + N * (2 * S + 1) := by
        have h1 := size_list_le_of_entries _ S hentry
        have h2 : (r.take j).length ≤ Enc.size (r.take j) := length_le_size _
        have h3 : (r.take j).length * (2 * S + 1) ≤ N * (2 * S + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        rw [List.length_map] at h1
        omega
      have hW := size_foldl_map_cons_le (fun a => f (x.1, a)) (r.take j) x.2
      have hpair := Combine.size_pair_le x.1
        (List.foldl (fun y a => f (x.1, a) :: y) x.2 (r.take j))
      have h7 : N * (2 * S + 1) ≤ 3 * (2 ^ (s + 2 * e) * (N + 1) ^ (e + 1)) := by
        have := one_le_pw (s + 2 * e) e N
        calc N * (2 * S + 1) ≤ (N + 1) * (3 * S) := Nat.mul_le_mul (by omega) (by omega)
          _ = 3 * (2 ^ (s + 2 * e) * (N + 1) ^ (e + 1)) := by rw [hS]; ring
      have h8 : N + 1 ≤ 2 ^ (s + 2 * e) * (N + 1) ^ (e + 1) :=
        (by simp : N + 1 ≤ 2 ^ 0 * (N + 1) ^ 1).trans (pw_mono (by omega) (by omega))
      have c := const_mul_pw_le (c := 16) (j := 4) (k := s + 2 * e) (d := e + 1) (N := N)
        (by norm_num)
      show Enc.size ((x.1, List.foldl (fun y a => f (x.1, a) :: y) x.2 (r.take j)) :
        γ × List β) ≤ 2 ^ (s + 2 * e + 4) * (N + 1) ^ (e + 1)
      omega)
  have hin := ((PF.fst (α := γ) (β := List α)).pair
    (PF.const (α := γ × List α) ([] : List β))).pair (PF.snd (α := γ) (β := List α))
  exact (((hin.comp hfold).comp PF.snd).comp pf_reverse).of_eq (fun p => by
    dsimp only
    rw [foldl_mapParam_eq]
    dsimp only
    rw [foldl_map_cons_eq]
    simp)

/-- `RAM.PolyFun.filterParam`. -/
def PF.filterParamB {q : γ × α → Bool} {k d s e : ℕ} (hq : PF q k d s e) :
    PFB (fun p : γ × List α => p.2.filter (fun a => q (p.1, a))) := PFB.of <| by
  have hstep := ((PF.fst (α := γ × List α) (β := α)).comp PF.fst).pair
    (PF.ite ((((PF.fst (α := γ × List α) (β := α)).comp PF.fst).pair PF.snd).comp hq)
      (((PF.snd (α := γ × List α) (β := α)).pair
        ((PF.fst (α := γ × List α) (β := α)).comp PF.snd)).comp (pf_cons (β := α)))
      ((PF.fst (α := γ × List α) (β := α)).comp PF.snd))
  have hfold := PF.foldl (ka := 3) (da := 1)
    (f := fun z : (γ × List α) × α =>
      ((z.1.1, if q (z.1.1, z.2) then z.2 :: z.1.2 else z.1.2) : γ × List α)) hstep
    (fun x r j => by
      rw [foldl_filterParam_eq]
      have hx : Enc.size x ≤ Enc.size ((x, r) : (γ × List α) × List α) :=
        Combine.size_fst_le x r
      have hr : Enc.size r ≤ Enc.size ((x, r) : (γ × List α) × List α) :=
        Combine.size_snd_le x r
      have hx1 : Enc.size x.1 ≤ Enc.size x := size_fst_le' x
      have hx2 : Enc.size x.2 ≤ Enc.size x := size_snd_le' x
      have hW := size_foldl_filter_cons_le (fun a => q (x.1, a)) (r.take j) x.2
      have hrt : Enc.size (r.take j) ≤ Enc.size r := size_take_le j r
      have hpair := Combine.size_pair_le x.1
        (List.foldl (fun y a => if q (x.1, a) then a :: y else y) x.2 (r.take j))
      show Enc.size ((x.1, List.foldl (fun y a => if q (x.1, a) then a :: y else y) x.2
        (r.take j)) : γ × List α) ≤ 2 ^ 3 * (Enc.size ((x, r) : (γ × List α) × List α) + 1) ^ 1
      rw [pow_one]
      omega)
  have hin := ((PF.fst (α := γ) (β := List α)).pair
    (PF.const (α := γ × List α) ([] : List α))).pair (PF.snd (α := γ) (β := List α))
  exact (((hin.comp hfold).comp PF.snd).comp pf_reverse).of_eq (fun p => by
    dsimp only
    rw [foldl_filterParam_eq]
    dsimp only
    rw [foldl_filter_cons_eq]
    simp)

/-- `(10 N + 1)^e ≤ 2^{4e} (N + 1)^e`. -/
theorem ten_mul_pow_le (N e : ℕ) : (10 * N + 1) ^ e ≤ 2 ^ (4 * e) * (N + 1) ^ e := by
  calc (10 * N + 1) ^ e ≤ (16 * (N + 1)) ^ e := Nat.pow_le_pow_left (by omega) e
    _ = 2 ^ (4 * e) * (N + 1) ^ e := by rw [mul_pow, pow_mul]; norm_num

/-- `RAM.PolyFun.foldlParam`: the accumulator along the fold has size at most
`2^{ka} (N+1)^{da}`, for `N` the size of the input `(c, (x, r))`. -/
def PF.foldlParamB {f : γ × (σ × α) → σ} {k d s e : ℕ} (hf : PF f k d s e) (ka da : ℕ)
    (hacc : ∀ (cc : γ) (x : σ) (r : List α) (j : ℕ),
      Enc.size (List.foldl (fun y a => f (cc, (y, a))) x (r.take j))
        ≤ 2 ^ ka * (Enc.size ((cc, (x, r)) : γ × (σ × List α)) + 1) ^ da) :
    PFB (fun z : γ × (σ × List α) => List.foldl (fun y a => f (z.1, (y, a))) z.2.1 z.2.2) :=
    PFB.of <| by
  have hstep := ((PF.fst (α := γ × σ) (β := α)).comp PF.fst).pair
    ((((PF.fst (α := γ × σ) (β := α)).comp PF.fst).pair
      (((PF.fst (α := γ × σ) (β := α)).comp PF.snd).pair PF.snd)).comp hf)
  have hfold := PF.foldl (ka := ka + 4 * da + 3) (da := max da 1)
    (f := fun w : (γ × σ) × α => ((w.1.1, f (w.1.1, (w.1.2, w.2))) : γ × σ)) hstep
    (fun x r j => by
      rw [foldl_foldlParam_eq]
      obtain ⟨cc, y⟩ := x
      set N := Enc.size ((((cc, y) : γ × σ), r) : (γ × σ) × List α) with hN
      have h1 := hacc cc y r j
      have h2 := size_assoc_le cc y r
      have h4 : (Enc.size ((cc, (y, r)) : γ × (σ × List α)) + 1) ^ da ≤ (10 * N + 1) ^ da :=
        Nat.pow_le_pow_left (by omega) da
      have h5 : 2 ^ ka * (Enc.size ((cc, (y, r)) : γ × (σ × List α)) + 1) ^ da ≤
          2 ^ (ka + 4 * da) * (N + 1) ^ max da 1 := by
        calc 2 ^ ka * (Enc.size ((cc, (y, r)) : γ × (σ × List α)) + 1) ^ da
            ≤ 2 ^ ka * (2 ^ (4 * da) * (N + 1) ^ da) :=
              Nat.mul_le_mul_left _ (h4.trans (ten_mul_pow_le N da))
          _ = 2 ^ (ka + 4 * da) * (N + 1) ^ da := by rw [pow_add]; ring
          _ ≤ 2 ^ (ka + 4 * da) * (N + 1) ^ max da 1 := pw_mono le_rfl (by omega)
      have hpair := Combine.size_pair_le cc
        (List.foldl (fun yy a => f (cc, (yy, a))) y (r.take j))
      have h6 : Enc.size cc ≤ N := by
        have ha : Enc.size cc ≤ Enc.size ((cc, y) : γ × σ) := Combine.size_fst_le cc y
        have hb : Enc.size ((cc, y) : γ × σ) ≤ N := Combine.size_fst_le _ r
        omega
      have h8 : N + 1 ≤ 2 ^ (ka + 4 * da) * (N + 1) ^ max da 1 :=
        (by simp : N + 1 ≤ 2 ^ 0 * (N + 1) ^ 1).trans (pw_mono (by omega) (by omega))
      have c := const_mul_pw_le (c := 8) (j := 3) (k := ka + 4 * da) (d := max da 1) (N := N)
        (by norm_num)
      show Enc.size ((cc, List.foldl (fun yy a => f (cc, (yy, a))) y (r.take j)) : γ × σ) ≤
        2 ^ (ka + 4 * da + 3) * (N + 1) ^ max da 1
      omega)
  have hin := ((PF.fst (α := γ) (β := σ × List α)).pair
    ((PF.snd (α := γ) (β := σ × List α)).comp PF.fst)).pair
    ((PF.snd (α := γ) (β := σ × List α)).comp PF.snd)
  exact ((hin.comp hfold).comp PF.snd).of_eq (fun z => by
    dsimp only
    rw [foldl_foldlParam_eq])

end Explicit
