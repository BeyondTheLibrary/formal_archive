/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), tier 2: list routines with
explicit polynomial time. Not part of the faithful formalization.
-/
import Workspace.Explicit.Tier2.PFBase
import Workspace.Machine.ListOps4

/-!
# List routines with explicit constants

The `Explicit.PF` forms of the list routines of `Workspace/Machine/Lists.lean`,
`Cases.lean`, `ListOps.lean` and `ListOps4.lean`, each proved as the `RAM.PolyFun` lemma of the
same name: equality of naturals, the length, `Option.elim`, case analysis on a list, `join`,
the fold, `reverse` and `append`.
-/

namespace Explicit

open RAM

variable {α β γ σ : Type*} [Enc α] [Enc β] [Enc γ] [Enc σ]

theorem enc_size_zero : Enc.size (0 : ℕ) = 2 := by rw [Small.size_nat]; rfl

theorem enc_size_one : Enc.size (1 : ℕ) = 3 := by rw [Small.size_nat]; rfl

/-! ## Equality and length -/

/-- `RAM.polyFun_natEq`. -/
theorem pf_natEq : PF (fun p : ℕ × ℕ => decide (p.1 = p.2)) 31 1 2 0 :=
  (PF.ite pf_le ((PF.snd.pair PF.fst).comp pf_le) (PF.const (α := ℕ × ℕ) false)).of_eq
    (fun p => by
      by_cases h : p.1 ≤ p.2
      · simp only [h, decide_true, if_true]
        by_cases h' : p.2 ≤ p.1 <;> simp [h'] <;> omega
      · simp only [h, decide_false, Bool.false_eq_true, if_false]
        symm
        simpa using (by omega : p.1 ≠ p.2))

/-- `RAM.polyFun_length`. -/
theorem pf_length : PF (fun l : List α => l.length) 90 2 11 1 := by
  have hp := (((PF.snd (α := ℕ) (β := List α)).comp (pf_rawLength (α := List α))).pair
    (PF.const (α := ℕ × List α) (0 : ℕ))).comp pf_natEq
  have hcount := (PF.ite hp (PF.fst (α := ℕ) (β := List α)) (((PF.fst (α := ℕ) (β := List α)).pair (PF.const (α := ℕ × List α) (1 : ℕ))).comp
    pf_add)).of_eq (g := fun s : ℕ × List α =>
      if decide (rawLength s.2 = 0) then s.1 else s.1 + 1) (fun s => rfl)
  have htail := (PF.snd (α := ℕ) (β := List α)).comp (pf_tail (α := α))
  have hlenStep := (hcount.pair htail).of_eq (g := (lenStep : ℕ × List α → ℕ × List α))
    (fun s => rfl)
  have hstep := (((PF.fst (α := ℕ) (β := ℕ × List α)).pair (PF.const (α := ℕ × (ℕ × List α)) (1 : ℕ))).comp pf_sub).pair
    ((PF.snd (α := ℕ) (β := ℕ × List α)).comp hlenStep)
  have hk := (pf_rawLength (α := ℕ × List α)).pair PF.id
  have hiter := PF.iterate (kq := 0) (dq := 1) (kp := 5) (dp := 1) hstep hk
    (fun a => by have := rawLength_lt_size a; norm_num; omega)
    (fun a j hj => by have := lenStep_size_bound a j hj; norm_num; omega)
  have hzero := (PF.const (α := List α) (0 : ℕ)).pair PF.id
  exact ((hzero.comp hiter).comp (PF.fst (α := ℕ) (β := List α))).of_eq
    (fun l => lenStep_result l)

/-! ## Case analysis -/

/-- `RAM.PolyFun.optionElim`. -/
theorem PF.optionElim {g : σ → γ} {h : β × σ → γ} {kg dg sg eg kh dh sh eh : ℕ}
    (hg : PF g kg dg sg eg) (hh : PF h kh dh sh eh) :
    PF (fun p : Option β × σ => p.1.elim (g p.2) (fun b => h (b, p.2)))
      (max kg kh + dg + 10) (max (max dg dh) 1) (max sg sh + eg) (max eg eh) := by
  rcases isEmpty_or_nonempty β with hβ | hβ
  · refine (((PF.snd (α := Option β) (β := σ)).comp hg).mono (by omega) (by omega) (by omega)
      (by omega)).of_eq (fun p => ?_)
    obtain ⟨o, s⟩ := p
    cases o with
    | none => rfl
    | some b => exact (hβ.false b).elim
  obtain ⟨⟨Pg, hPg⟩, hsg⟩ := hg
  obtain ⟨⟨Ph, hPh⟩, hsh⟩ := hh
  refine ⟨⟨_, (cleanComputeAt_optionElim (K := 16) (by norm_num) hβ hPg hPh
    (fun n n' h => pw_le_of_le h) (fun n n' h => pw_le_of_le h)).mono fun N => ?_⟩,
    fun p => ?_⟩
  · set A := max kg kh
    set B := max (max dg dh) 1
    have hN : N ≤ 2 ^ A * (N + 1) ^ B := (self_le_pw N).trans (pw_mono (by omega) (by omega))
    have h1 := one_le_pw A B N
    have h2 : 2 ^ kg * (N + 1) ^ dg ≤ 2 ^ A * (N + 1) ^ B := pw_mono (by omega) (by omega)
    have h3 : 2 ^ kh * (N + 1) ^ dh ≤ 2 ^ A * (N + 1) ^ B := pw_mono (by omega) (by omega)
    have c := const_mul_pw_le (c := 1024) (j := 10) (k := A) (d := B) (N := N) (by norm_num)
    have c2 : 2 ^ (A + 10) * (N + 1) ^ B ≤ 2 ^ (A + dg + 10) * (N + 1) ^ B :=
      pw_mono (by omega) le_rfl
    omega
  · obtain ⟨o, s⟩ := p
    cases o with
    | none =>
        have hx : Enc.size s ≤ Enc.size ((none, s) : Option β × σ) := Combine.size_snd_le _ s
        exact (hsg s).trans ((pw_le_of_le hx).trans (pw_mono (by omega) (by omega)))
    | some b =>
        have hx := size_strip_le b s
        exact (hsh (b, s)).trans ((pw_le_of_le hx).trans (pw_mono (by omega) (by omega)))

/-- `RAM.PolyFun.listCases`. -/
theorem PF.listCases {g : σ → γ} {h : (α × List α) × σ → γ} {kg dg sg eg kh dh sh eh : ℕ}
    (hg : PF g kg dg sg eg) (hh : PF h kh dh sh eh) :
    PF (fun p : List α × σ =>
      match p.1 with
      | [] => g p.2
      | a :: l => h ((a, l), p.2))
      (max 19 (max kg kh + dg + 10 + 5 * max (max dg dh) 1) + 1) (max (max dg dh) 1)
      (max sg sh + eg + 5 * max eg eh) (max eg eh) := by
  have huncons := ((PF.fst (α := List α) (β := σ)).comp (pf_uncons (α := α))).pair
    (PF.snd (α := List α) (β := σ))
  refine ((huncons.comp (hg.optionElim hh)).mono (by norm_num <;> omega) (by norm_num)
    (by norm_num <;> omega) (by norm_num)).of_eq (fun p => ?_)
  obtain ⟨l, s⟩ := p
  cases l with
  | nil => rfl
  | cons a t => rfl

/-- `RAM.polyFun_join`. -/
theorem pf_join : PF (fun o : Option (Option β) => o.join) 26 1 7 1 := by
  have h1 := (PF.id (α := Option (Option β))).pair (PF.const (α := Option (Option β)) (0 : ℕ))
  exact (h1.comp (PF.optionElim (g := fun _ : ℕ => (none : Option β))
    (h := fun q : Option β × ℕ => q.1) (PF.const none) PF.fst)).of_eq
    (g := fun o : Option (Option β) => o.join) (fun o => by
      cases o <;> rfl)

/-! ## Folds -/

/-- `RAM.polyFun_foldlStep`. -/
theorem pf_foldlStep {f : σ × α → σ} {kf df sf ef : ℕ} (hf : PF f kf df sf ef) :
    PF (foldlStep f) (kf + sf + 16 * df + 16 * ef + 120) (max (max df ef) 1)
      (sf + 16 * ef + 60) (max ef 1) := by
  have hg := (PF.id (α := σ)).pair (PF.const (α := σ) ([] : List α))
  have hh := ((((PF.snd (α := α × List α) (β := σ)).pair
    ((PF.fst (α := α × List α) (β := σ)).comp (PF.fst (α := α) (β := List α)))).comp hf).pair
    ((PF.fst (α := α × List α) (β := σ)).comp (PF.snd (α := α) (β := List α))))
  have hcases := PF.listCases hg hh
  refine ((((PF.snd (α := σ) (β := List α)).pair (PF.fst (α := σ) (β := List α))).comp
    hcases).mono (by norm_num [size_nil] <;> omega) (by norm_num <;> omega)
    (by norm_num [size_nil] <;> omega) (by norm_num <;> omega)).of_eq (fun s => ?_)
  obtain ⟨x, r⟩ := s
  cases r <;> rfl

/-- The time constant of one round of `RAM.PolyFun.foldl` (counter and `foldlStep`). -/
def foldlKS (kf df sf ef : ℕ) : ℕ := kf + 2 * sf + 17 * df + 34 * ef + 200

/-- The time degree of one round of `RAM.PolyFun.foldl`. -/
def foldlDS (df ef : ℕ) : ℕ := max (max df ef) 1

/-- `RAM.PolyFun.foldl`: the accumulator along the fold has size at most
`2^{ka} (N+1)^{da}`, for `N` the size of the input pair. -/
theorem PF.foldl {f : σ × α → σ} {kf df sf ef ka da : ℕ} (hf : PF f kf df sf ef)
    (hacc : ∀ (x : σ) (r : List α) (j : ℕ),
      Enc.size (List.foldl (fun y a => f (y, a)) x (r.take j))
        ≤ 2 ^ ka * (Enc.size ((x, r) : σ × List α) + 1) ^ da) :
    PF (fun s : σ × List α => List.foldl (fun y a => f (y, a)) s.1 s.2)
      (foldlKS kf df sf ef + (ka + 5) * foldlDS df ef + ka + 20)
      (max da 1 * foldlDS df ef + 1) (ka + 5) (max da 1) := by
  have hstepF := pf_foldlStep hf
  have hstep := ((((PF.fst (α := ℕ) (β := σ × List α)).pair
    (PF.const (α := ℕ × (σ × List α)) (1 : ℕ))).comp pf_sub).pair
    ((PF.snd (α := ℕ) (β := σ × List α)).comp hstepF)).mono
    (k' := foldlKS kf df sf ef) (d' := foldlDS df ef) (s' := foldlKS kf df sf ef) (e' := max ef 1)
    (by simp only [foldlKS, enc_size_one]; omega) (by simp only [foldlDS]; omega)
    (by simp only [foldlKS, enc_size_one]; omega) (by omega)
  have hk := ((pf_rawLength (α := σ × List α)).pair PF.id).mono (k' := 16) (d' := 1) (s' := 2)
    (e' := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hbound : ∀ (a : σ × List α), ∀ j ≤ rawLength a,
      Enc.size ((rawLength a - j, (foldlStep f)^[j] a) : ℕ × (σ × List α))
        ≤ 2 ^ (ka + 4) * (Enc.size a + 1) ^ max da 1 := by
    rintro ⟨x, r⟩ j _
    rw [foldlStep_iterate]
    set N : ℕ := Enc.size ((x, r) : σ × List α) with hN
    set X : ℕ := rawLength ((x, r) : σ × List α) - j with hX
    set Y : σ := List.foldl (fun y a => f (y, a)) x (r.take j) with hY
    set Z : List α := r.drop j with hZ
    have hraw : rawLength ((x, r) : σ × List α) < N := rawLength_lt_size _
    have hsX : Enc.size X ≤ N + 2 := by
      have h1 : Enc.size X = Nat.size X + 2 := Small.size_nat X
      have h2 : Nat.size X ≤ X := size_le_self X
      omega
    have hsY : Enc.size Y ≤ 2 ^ ka * (N + 1) ^ max da 1 :=
      (hacc x r j).trans (pw_mono le_rfl (by omega))
    have hsZ : Enc.size Z ≤ N :=
      le_trans (size_drop_le j r) (Combine.size_snd_le x r)
    have hpair : Enc.size ((Y, Z) : σ × List α) ≤ 2 * Enc.size Y + 2 * Enc.size Z :=
      Combine.size_pair_le Y Z
    have htop : Enc.size ((X, (Y, Z)) : ℕ × (σ × List α))
        ≤ 2 * Enc.size X + 2 * Enc.size ((Y, Z) : σ × List α) := Combine.size_pair_le _ _
    have hN1 : N + 1 ≤ 2 ^ ka * (N + 1) ^ max da 1 :=
      (by simp : N + 1 ≤ 2 ^ 0 * (N + 1) ^ 1).trans (pw_mono (by omega) (by omega))
    have c := const_mul_pw_le (c := 16) (j := 4) (k := ka) (d := max da 1) (N := N) (by norm_num)
    omega
  have hiter := PF.iterate (kq := 0) (dq := 1) hstep hk
    (fun a => by have := rawLength_lt_size a; norm_num; omega) hbound
  have e1 : (ka + 4 + 1) * foldlDS df ef = (ka + 5) * foldlDS df ef := rfl
  have e2 : max da 1 ≤ max da 1 * foldlDS df ef :=
    Nat.le_mul_of_pos_right _ (by simp only [foldlDS]; omega)
  refine ((hiter.comp (PF.fst (α := σ) (β := List α))).mono (by omega) (by omega) (by omega)
    (by omega)).of_eq (fun s => ?_)
  obtain ⟨x, r⟩ := s
  show ((foldlStep f)^[rawLength ((x, r) : σ × List α)] (x, r)).1 = _
  rw [foldlStep_iterate]
  have hle := length_le_rawLength_pair x r
  have ht : r.take (rawLength ((x, r) : σ × List α)) = r := List.take_of_length_le hle
  rw [ht]

/-- `RAM.polyFun_foldlCons`. -/
theorem pf_foldlCons :
    PF (fun s : List α × List α => List.foldl (fun y a => a :: y) s.1 s.2) 301 2 6 1 := by
  have hf := ((PF.snd (α := List α) (β := α)).pair (PF.fst (α := List α) (β := α))).comp
    (pf_cons (β := α))
  exact PF.foldl (ka := 1) (da := 1) hf (fun x r j => by
    have h1 : Enc.size (List.foldl (fun y a => a :: y) x (r.take j))
        ≤ Enc.size x + Enc.size (r.take j) := size_foldl_cons_le _ _
    have h2 : Enc.size (r.take j) ≤ Enc.size r := size_take_le j r
    have h3 : Enc.size x ≤ Enc.size ((x, r) : List α × List α) := Combine.size_fst_le x r
    have h4 : Enc.size r ≤ Enc.size ((x, r) : List α × List α) := Combine.size_snd_le x r
    show Enc.size (List.foldl (fun y a => a :: y) x (r.take j)) ≤
      2 ^ 1 * (Enc.size ((x, r) : List α × List α) + 1) ^ 1
    rw [pow_one, pow_one]
    omega)

/-- `RAM.polyFun_reverse`. -/
theorem pf_reverse : PF (fun l : List α => l.reverse) 310 2 10 1 :=
  (((PF.const (α := List α) ([] : List α)).pair PF.id).comp (pf_foldlCons (α := α))).of_eq
    (fun l => by
      show List.foldl (fun y a => a :: y) ([] : List α) l = l.reverse
      rw [foldl_cons_eq]
      simp)

/-- `RAM.polyFun_append`. -/
theorem pf_append : PF (fun p : List α × List α => p.1 ++ p.2) 330 2 20 1 :=
  (((PF.snd (α := List α) (β := List α)).pair
    ((PF.fst (α := List α) (β := List α)).comp pf_reverse)).comp (pf_foldlCons (α := α))).of_eq
    (fun p => by
      show List.foldl (fun y a => a :: y) p.2 p.1.reverse = p.1 ++ p.2
      rw [foldl_cons_eq]
      simp)

/-- The time constant of `RAM.PolyFun.map`. -/
def mapK (kg dg sg eg : ℕ) : ℕ :=
  foldlKS (kg + dg + sg + eg + 30) (max (max dg eg) 1) (sg + eg + 3) (max eg 1) +
    (sg + 7) * foldlDS (max (max dg eg) 1) (max eg 1) +
    4 * ((eg + 1) * foldlDS (max (max dg eg) 1) (max eg 1)) + 2 * sg + 8 * eg + 800

/-- The time degree of `RAM.PolyFun.map`. -/
def mapD (dg eg : ℕ) : ℕ := (eg + 1) * foldlDS (max (max dg eg) 1) (max eg 1) + 2 * eg + 2

/-- `RAM.PolyFun.map`. -/
theorem PF.map {g : α → β} {kg dg sg eg : ℕ} (hg : PF g kg dg sg eg) :
    PF (fun l : List α => l.map g) (mapK kg dg sg eg) (mapD dg eg) (sg + 4 * eg + 30)
      (eg + 1) := by
  have hf := (((((PF.snd (α := List β) (β := α)).comp hg).pair
    (PF.fst (α := List β) (β := α))).comp (pf_cons (β := β)))).mono
    (k' := kg + dg + sg + eg + 30) (d' := max (max dg eg) 1) (s' := sg + eg + 3)
    (e' := max eg 1) (by omega) (by omega) (by omega) (by omega)
  have hfold := PF.foldl (ka := sg + 2) (da := eg + 1) hf (fun x r j => ?_)
  · have hin := (PF.const (α := List α) ([] : List β)).pair (PF.id (α := List α))
    refine (((hin.comp hfold).comp (pf_reverse (α := β))).mono ?_ ?_ ?_ ?_).of_eq
      (fun l => ?_)
    · simp only [mapK, size_nil]
      generalize foldlDS (max (max dg eg) 1) (max eg 1) = X
      have e1 : (sg + 2 + 5) * X = (sg + 7) * X := by ring
      have e2 : max (eg + 1) 1 = eg + 1 := by omega
      rw [e2]
      norm_num <;> omega
    · simp only [mapD]
      generalize foldlDS (max (max dg eg) 1) (max eg 1) = X
      have e2 : max (eg + 1) 1 = eg + 1 := by omega
      rw [e2]
      norm_num <;> omega
    · simp only [size_nil]; norm_num <;> omega
    · norm_num <;> omega
    · show (List.foldl (fun y a => g a :: y) ([] : List β) l).reverse = _
      rw [foldl_map_cons_eq]
      simp
  · set N := Enc.size ((x, r) : List β × List α) with hN
    have h1 := size_foldl_map_cons_le g (r.take j) x
    have h2 := size_map_le (c := 2 ^ sg) (d := eg) hg.size (r.take j)
    have h3 : Enc.size (r.take j) ≤ Enc.size r := size_take_le j r
    have h4 : Enc.size x ≤ N := Combine.size_fst_le x r
    have h5 : Enc.size r ≤ N := Combine.size_snd_le x r
    have hrN : Enc.size (r.take j) ≤ N := by omega
    have hpw := pw_le_of_le (k := sg) (d := eg) hrN
    have h6 : Enc.size (r.take j) * (2 * (2 ^ sg * (Enc.size (r.take j) + 1) ^ eg) + 1)
        ≤ N * (2 * (2 ^ sg * (N + 1) ^ eg) + 1) :=
      Nat.mul_le_mul hrN (by omega)
    have h7 : N * (2 * (2 ^ sg * (N + 1) ^ eg) + 1) ≤ 3 * (2 ^ sg * (N + 1) ^ (eg + 1)) := by
      have := one_le_pw sg eg N
      calc N * (2 * (2 ^ sg * (N + 1) ^ eg) + 1) ≤ (N + 1) * (3 * (2 ^ sg * (N + 1) ^ eg)) :=
            Nat.mul_le_mul (by omega) (by omega)
        _ = 3 * (2 ^ sg * (N + 1) ^ (eg + 1)) := by ring
    have h8 : N + 1 ≤ 2 ^ sg * (N + 1) ^ (eg + 1) :=
      (by simp : N + 1 ≤ 2 ^ 0 * (N + 1) ^ 1).trans (pw_mono (by omega) (by omega))
    have c := const_mul_pw_le (c := 4) (j := 2) (k := sg) (d := eg + 1) (N := N) (by norm_num)
    show Enc.size (List.foldl (fun y a => g a :: y) x (r.take j)) ≤
      2 ^ (sg + 2) * (N + 1) ^ (eg + 1)
    omega

end Explicit
