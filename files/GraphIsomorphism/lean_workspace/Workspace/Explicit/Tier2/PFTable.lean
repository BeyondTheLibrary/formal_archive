/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), tier 2: the sifting table and
the Schreier–Sims loop with explicit constants. Not part of the faithful formalization.
-/
import Workspace.Explicit.Tier2.PFPerm
import Workspace.Algo.ChainBuildPoly

/-!
# The sifting table and the closure loop, with explicit constants

The `Explicit.PF` forms of `Algo.polyFun_rawTableGet`, `Algo.polyFun_rawInsert`,
`Algo.polyFun_rawStuckStep`, `Algo.polyFun_rawEntries`, `Algo.polyFun_rawNewItems`,
`Algo.polyFun_rawSiftStuck`, `Algo.polyFun_rawBuildRound`, `Algo.polyFun_rawInitTable`,
`Algo.polyFun_rawSquare`, `Algo.polyFun_rawFuelList`, `Algo.polyFun_rawBuildTable`
(Schreier–Sims) and `Algo.polyFun_rawShorten`, proved along the same compositions and with the
same accumulator bounds, written as `2^k (N+1)^d`.
-/

set_option maxRecDepth 100000

namespace Explicit

open RAM Algo

variable {α β γ σ : Type*} [Enc α] [Enc β] [Enc γ] [Enc σ]

/-- `Algo.polyFun_rawTableGet`. -/
theorem pf_rawTableGet : PF rawTableGet 476 2 51 1 := by
  have hrow := (((PF.fst (α := RawTable) (β := ℕ × ℕ)).pair
    ((PF.snd (α := RawTable) (β := ℕ × ℕ)).comp PF.fst)).pair
      (PF.const (α := RawTable × (ℕ × ℕ)) ([] : RawRow))).comp (pf_getD (α := RawRow))
  have h := (hrow.pair ((PF.snd (α := RawTable) (β := ℕ × ℕ)).comp PF.snd)).comp
    (pf_natListLookup (β := RawPerm))
  exact h.of_eq (fun _ => rfl)

/-- `Algo.polyFun_rawInsert`. -/
theorem pf_rawInsert : PF rawInsert 858 16 256 8 := by
  have hf := PF.ite
    ((((PF.snd (α := (ℕ × RawPerm) × ℕ) (β := RawRow × ℕ)).comp PF.snd).pair
      ((PF.fst (α := (ℕ × RawPerm) × ℕ) (β := RawRow × ℕ)).comp PF.snd)).comp pf_natEq)
    ((((PF.fst (α := (ℕ × RawPerm) × ℕ) (β := RawRow × ℕ)).comp PF.fst).pair
      ((PF.snd (α := (ℕ × RawPerm) × ℕ) (β := RawRow × ℕ)).comp PF.fst)).comp
        (pf_cons (β := ℕ × RawPerm)))
    ((PF.snd (α := (ℕ × RawPerm) × ℕ) (β := RawRow × ℕ)).comp PF.fst)
  have hin := ((PF.fst (α := ℕ × RawPerm) (β := RawTable × ℕ)).pair
    ((PF.snd (α := ℕ × RawPerm) (β := RawTable × ℕ)).comp PF.snd)).pair
      (((PF.snd (α := ℕ × RawPerm) (β := RawTable × ℕ)).comp PF.fst).comp pf_zipIdx)
  have h := hin.comp (PF.mapParamB hf).pf
  exact h.of_eq (fun p => by
    show (p.2.1.zipIdx).map
        (fun z => if (decide (z.2 = p.2.2) : Bool) then p.1 :: z.1 else z.1) = rawInsert p
    rw [rawInsert]
    refine List.map_congr_left ?_
    intro z _
    by_cases h : z.2 = p.2.2 <;> simp [h])

/-- `Algo.polyFun_rawStuckStep`. -/
theorem pf_rawStuckStep : PF rawStuckStep 6365 40 2223 16 := by
  have hlook := ((PF.fst (α := RawTable) (β := RawPerm × ℕ)).pair
    (((PF.snd (α := RawTable) (β := RawPerm × ℕ)).comp PF.snd).pair
      ((((PF.snd (α := RawTable) (β := RawPerm × ℕ)).comp PF.fst).pair
        ((PF.snd (α := RawTable) (β := RawPerm × ℕ)).comp PF.snd)).comp pf_rawApply))).comp
    pf_rawTableGet
  have hnone := ((((PF.snd (α := RawTable) (β := RawPerm × ℕ)).comp PF.snd).pair
    ((PF.snd (α := RawTable) (β := RawPerm × ℕ)).comp PF.fst)).comp pf_some).pair
    ((PF.snd (α := RawTable) (β := RawPerm × ℕ)).comp PF.fst)
  have hsome := (PF.const (α := RawPerm × (RawTable × (RawPerm × ℕ)))
    (none : Option (ℕ × RawPerm))).pair
    ((((PF.fst (α := RawPerm) (β := RawTable × (RawPerm × ℕ))).comp pf_rawInv).pair
      (((PF.snd (α := RawPerm) (β := RawTable × (RawPerm × ℕ))).comp PF.snd).comp
        PF.fst)).comp pf_rawMul)
  have hinner := ((hlook.pair PF.id).comp (PF.optionElim hnone hsome)).of_eq
    (g := fun z : RawTable × (RawPerm × ℕ) =>
      match rawTableGet (z.1, (z.2.2, rawApply (z.2.1, z.2.2))) with
      | none => ((some (z.2.2, z.2.1) : Option (ℕ × RawPerm)), z.2.1)
      | some τ => ((none : Option (ℕ × RawPerm)), rawMul (rawInv τ, z.2.1)))
    (fun z => by dsimp only; rcases rawTableGet (z.1, (z.2.2, rawApply (z.2.1, z.2.2))) with _ | τ <;> rfl)
  have houter := ((PF.fst (α := ℕ × RawPerm) (β := RawTable × (RawPerm × ℕ))).comp
    pf_some).pair (((PF.snd (α := ℕ × RawPerm) (β := RawTable × (RawPerm × ℕ))).comp
      PF.snd).comp PF.fst)
  have hin := (((PF.snd (α := RawTable) (β := (Option (ℕ × RawPerm) × RawPerm) × ℕ)).comp
    PF.fst).comp PF.fst).pair
    ((PF.fst (α := RawTable) (β := (Option (ℕ × RawPerm) × RawPerm) × ℕ)).pair
      ((((PF.snd (α := RawTable) (β := (Option (ℕ × RawPerm) × RawPerm) × ℕ)).comp
        PF.fst).comp PF.snd).pair
        ((PF.snd (α := RawTable) (β := (Option (ℕ × RawPerm) × RawPerm) × ℕ)).comp PF.snd)))
  have h := hin.comp (PF.optionElim hinner houter)
  exact h.of_eq (g := rawStuckStep) (fun p => by
    obtain ⟨t, ⟨o, r⟩, i⟩ := p
    cases o <;> rfl)

/-- `Algo.polyFun_rawEntries`. -/
theorem pf_rawEntries : PF rawEntries 1212 12 64 4 := by
  have h := (pf_flatten (α := ℕ × RawPerm)).comp (PF.map (PF.snd (α := ℕ) (β := RawPerm)))
  exact h.of_eq (fun _ => rfl)

/-- `Algo.polyFun_rawNewItems`. -/
theorem pf_rawNewItems : PF (fun p : RawTable × RawPerm => rawNewItems p.1 p.2) 3335 64 680 24 := by
  have h2 := ((PF.snd (α := RawPerm) (β := RawPerm)).pair PF.fst).comp pf_rawMul
  have hpair := (pf_rawMul.pair ((h2.pair (PF.const (α := RawPerm × RawPerm)
    ([] : List RawPerm))).comp (pf_cons (β := RawPerm)))).comp (pf_cons (β := RawPerm))
  have hin := (PF.snd (α := RawTable) (β := RawPerm)).pair
    ((PF.fst (α := RawTable) (β := RawPerm)).comp pf_rawEntries)
  have h := (hin.comp (PF.mapParamB hpair).pf).comp pf_flatten
  exact h.of_eq (fun p => by
    show ((rawEntries p.1).map (fun e => [rawMul (p.2, e), rawMul (e, p.2)])).flatten
      = rawNewItems p.1 p.2
    rw [rawNewItems, flatMap_eq_flatten_map])

/-- The bound on the accumulator of `Algo.rawSiftStuck` of `Algo.polyFun_rawSiftStuck`, with the
size bound `2^251 (N+1)^8` of `Explicit.pf_rawInv`. -/
theorem size_rawStuckFold_le (cc : RawTable) (x : Option (ℕ × RawPerm) × RawPerm) (r : List ℕ)
    (j : ℕ) :
    Enc.size (List.foldl (fun y a => rawStuckStep (cc, (y, a))) x (r.take j))
      ≤ 2 ^ 257 * (Enc.size ((cc, (x, r)) :
          RawTable × ((Option (ℕ × RawPerm) × RawPerm) × List ℕ)) + 1) ^ 9 := by
  set N := Enc.size ((cc, (x, r)) :
    RawTable × ((Option (ℕ × RawPerm) × RawPerm) × List ℕ)) with hN
  set P := 2 ^ 251 * (N + 1) ^ 8 with hP
  set Q := 2 ^ 251 * (N + 1) ^ 9 with hQ
  have hNP : N + 1 ≤ P :=
    (by simp : N + 1 ≤ 2 ^ 0 * (N + 1) ^ 1).trans (pw_mono (by omega) (by omega))
  have hPQ : P * (N + 1) = Q := by rw [hP, hQ]; ring
  have h7 : N * (2 * (N + P) + 1) ≤ 4 * Q := by
    calc N * (2 * (N + P) + 1) ≤ (N + 1) * (4 * P) := Nat.mul_le_mul (by omega) (by omega)
      _ = 4 * Q := by rw [← hPQ]; ring
  have hNQ : N + 1 ≤ Q := hNP.trans (by rw [← hPQ]; exact Nat.le_mul_of_pos_right _ (by omega))
  have h64 : 2 ^ 257 * (N + 1) ^ 9 = 64 * Q := by
    rw [hQ, show 257 = 6 + 251 from rfl, pow_add]; ring
  rw [h64]
  have hcc : Enc.size cc ≤ N :=
    Combine.size_fst_le cc ((x, r) : (Option (ℕ × RawPerm) × RawPerm) × List ℕ)
  have hxr : Enc.size ((x, r) : (Option (ℕ × RawPerm) × RawPerm) × List ℕ) ≤ N :=
    Combine.size_snd_le cc ((x, r) : (Option (ℕ × RawPerm) × RawPerm) × List ℕ)
  have hx : Enc.size x ≤ N := le_trans (Combine.size_fst_le x r) hxr
  have hr : Enc.size r ≤ N := le_trans (Combine.size_snd_le x r) hxr
  have hS : ∀ τ : RawPerm, TableEntry cc τ → ∀ y ∈ rawInv τ, Enc.size y ≤ N + P := by
    intro τ hτ y hy
    have h1 : Enc.size y ≤ Enc.size (rawInv τ) := size_mem_le hy
    have h2 : Enc.size (rawInv τ) ≤ 2 ^ 251 * (Enc.size τ + 1) ^ 8 := pf_rawInv.size τ
    have h3 : Enc.size τ ≤ N := le_trans (size_le_of_tableEntry hτ) hcc
    have h4 : (Enc.size τ + 1) ^ 8 ≤ (N + 1) ^ 8 := Nat.pow_le_pow_left (by omega) 8
    have h5 := Nat.mul_le_mul_left (2 ^ 251) h4
    omega
  obtain ⟨o, r₀⟩ := x
  have hr₀ : Enc.size r₀ ≤ N := le_trans (Combine.size_snd_le o r₀) hx
  cases o with
  | some z =>
      rw [rawStuckFold_frozen]
      omega
  | none =>
      set F := List.foldl (fun y a => rawStuckStep (cc, (y, a)))
        (((none : Option (ℕ × RawPerm)), r₀)) (r.take j) with hF
      obtain ⟨⟨hlen, hmem⟩, hrep⟩ := rawStuckFold_struct cc (r.take j) r₀
      rw [← hF] at hlen hmem hrep
      have hentry : ∀ y ∈ F.2, Enc.size y ≤ N + P := by
        intro y hy
        rcases hmem y hy with h | ⟨τ, hτ, h⟩
        · have h1 : Enc.size y ≤ Enc.size r₀ := size_mem_le h
          omega
        · exact hS τ hτ y h
      have hlen2 : F.2.length ≤ N := by
        have h1 : r₀.length ≤ Enc.size r₀ := length_le_size r₀
        omega
      have hsnd : Enc.size F.2 ≤ 1 + N * (2 * (N + P) + 1) := by
        have h1 := size_list_le_of_entries F.2 (N + P) hentry
        have h2 : F.2.length * (2 * (N + P) + 1) ≤ N * (2 * (N + P) + 1) :=
          Nat.mul_le_mul_right _ hlen2
        omega
      have hfst : Enc.size F.1 ≤ 2 * N + 2 * (1 + N * (2 * (N + P) + 1)) + 2 := by
        rcases hres : F.1 with _ | ⟨i, ρ⟩
        · rw [size_none]
          omega
        · obtain ⟨hi, hρl, hρm⟩ := hrep i ρ hres
          have hiN : Enc.size i ≤ N := by
            have h1 : i ∈ r := List.take_subset j r hi
            have h2 : Enc.size i ≤ Enc.size r := size_mem_le h1
            omega
          have hρentry : ∀ y ∈ ρ, Enc.size y ≤ N + P := by
            intro y hy
            rcases hρm y hy with h | ⟨τ, hτ, h⟩
            · have h1 : Enc.size y ≤ Enc.size r₀ := size_mem_le h
              omega
            · exact hS τ hτ y h
          have hρlen : ρ.length ≤ N := by
            have h1 : r₀.length ≤ Enc.size r₀ := length_le_size r₀
            omega
          have hρsize : Enc.size ρ ≤ 1 + N * (2 * (N + P) + 1) := by
            have h1 := size_list_le_of_entries ρ (N + P) hρentry
            have h2 : ρ.length * (2 * (N + P) + 1) ≤ N * (2 * (N + P) + 1) :=
              Nat.mul_le_mul_right _ hρlen
            omega
          have h3 : Enc.size ((i, ρ) : ℕ × RawPerm) ≤ 2 * Enc.size i + 2 * Enc.size ρ :=
            Combine.size_pair_le i ρ
          have h4 := size_some_eq ((i, ρ) : ℕ × RawPerm)
          omega
      have hpair : Enc.size F ≤ 2 * Enc.size F.1 + 2 * Enc.size F.2 :=
        Combine.size_pair_le F.1 F.2
      omega

/-- `Algo.polyFun_rawSiftStuck`. -/
theorem pf_rawSiftStuck : PF rawSiftStuck 39842 722 672 18 := by
  have hfold := (PF.foldlParamB pf_rawStuckStep 257 9 size_rawStuckFold_le).pf
  have hin := (PF.fst (α := RawTable) (β := RawPerm)).pair
    (((PF.const (α := RawTable × RawPerm) (none : Option (ℕ × RawPerm))).pair PF.snd).pair
      ((PF.snd (α := RawTable) (β := RawPerm)).comp pf_rangeLength))
  have h := (hin.comp hfold).comp PF.fst
  exact h.of_eq (fun p => rfl)

/-- `Algo.polyFun_rawBuildRound`. -/
theorem pf_rawBuildRound : PF rawBuildRound 495925 9216 185411 3456 := by
  have hins := (((((PF.fst (α := ℕ × RawPerm) (β := (RawPerm × List RawPerm) × RawTable)).comp
      PF.snd).pair ((PF.fst (α := ℕ × RawPerm) (β := (RawPerm × List RawPerm) × RawTable)).comp
        PF.fst)).comp pf_rawApply).pair
      ((PF.fst (α := ℕ × RawPerm) (β := (RawPerm × List RawPerm) × RawTable)).comp PF.snd)).pair
    (((PF.snd (α := ℕ × RawPerm) (β := (RawPerm × List RawPerm) × RawTable)).comp PF.snd).pair
      ((PF.fst (α := ℕ × RawPerm) (β := (RawPerm × List RawPerm) × RawTable)).comp PF.fst))
    |>.comp pf_rawInsert
  have hrest := (((PF.snd (α := RawTable)
    (β := (ℕ × RawPerm) × ((RawPerm × List RawPerm) × RawTable))).comp PF.snd).comp
      PF.fst).comp PF.snd
  have hnew := ((PF.fst (α := RawTable)
    (β := (ℕ × RawPerm) × ((RawPerm × List RawPerm) × RawTable))).pair
    (((PF.snd (α := RawTable)
      (β := (ℕ × RawPerm) × ((RawPerm × List RawPerm) × RawTable))).comp PF.fst).comp
        PF.snd)).comp pf_rawNewItems
  have hafter := (PF.fst (α := RawTable)
    (β := (ℕ × RawPerm) × ((RawPerm × List RawPerm) × RawTable))).pair
    ((hrest.pair hnew).comp pf_append)
  have hsome := (hins.pair PF.id).comp hafter
  have hnone := (PF.snd (α := RawPerm × List RawPerm) (β := RawTable)).pair
    ((PF.fst (α := RawPerm × List RawPerm) (β := RawTable)).comp PF.snd)
  have hlook := ((PF.snd (α := RawPerm × List RawPerm) (β := RawTable)).pair
    ((PF.fst (α := RawPerm × List RawPerm) (β := RawTable)).comp PF.fst)).comp pf_rawSiftStuck
  have hcons := ((hlook.pair PF.id).comp (PF.optionElim hnone hsome)).of_eq
    (g := fun v : (RawPerm × List RawPerm) × RawTable => rawBuildRound (v.2, v.1.1 :: v.1.2))
    (fun v => by
      obtain ⟨⟨g, rest⟩, t⟩ := v
      show _ = rawBuildRound (t, g :: rest)
      rcases hst : rawSiftStuck (t, g) with _ | ⟨i, ρ⟩
      · rw [rawBuildRound_cons_none hst]; simp [hst]
      · rw [rawBuildRound_cons_some hst]; simp [hst])
  have hnil := (PF.id (α := RawTable)).pair (PF.const (α := RawTable) ([] : List RawPerm))
  have hcases := PF.listCases (α := RawPerm) (σ := RawTable) hnil hcons
  have h := ((PF.snd (α := RawTable) (β := List RawPerm)).pair PF.fst).comp hcases
  exact h.of_eq (fun st => by
    obtain ⟨t, w⟩ := st
    cases w with
    | nil => rfl
    | cons g rest => rfl)

/-- `Algo.buildBound N ≤ 2^10 (N+1)^5` (the sum of its coefficients is `buildBound 1 = 540`). -/
theorem buildBound_le (N : ℕ) : buildBound N ≤ 2 ^ 10 * (N + 1) ^ 5 := by
  unfold buildBound buildSize
  ring_nf
  omega

/-- `Algo.polyFun_rawBuildRoundFold`. -/
theorem pf_rawBuildRoundFold : PF (fun s : (RawTable × List RawPerm) × List ℕ =>
    List.foldl (fun y (_ : ℕ) => rawBuildRound y) s.1 s.2) 1295522 46081 15 5 := by
  have h := PF.foldl (ka := 10) (da := 5)
    (f := fun z : (RawTable × List RawPerm) × ℕ => rawBuildRound z.1)
    ((PF.fst (α := RawTable × List RawPerm) (β := ℕ)).comp pf_rawBuildRound)
    (fun x r j => (size_foldl_rawBuildRound_le x r j).trans (buildBound_le _))
  exact h

/-- `Algo.polyFun_rawInitTable`. -/
theorem pf_rawInitTable : PF rawInitTable 522 8 102 4 := by
  have hf := (((PF.snd (α := RawPerm) (β := ℕ)).pair PF.fst).pair
    (PF.const (α := RawPerm × ℕ) ([] : List (ℕ × RawPerm)))).comp (pf_cons (β := ℕ × RawPerm))
  have h := (pf_rawOne.pair pf_rawOne).comp (PF.mapParamB hf).pf
  exact h.of_eq (fun _ => rfl)

/-- `Algo.polyFun_rawSquare`. -/
theorem pf_rawSquare : PF rawSquare 903 10 98 4 := by
  have h := (((PF.id (α := List ℕ)).pair PF.id).comp
    (PF.mapParamB (PF.fst (α := List ℕ) (β := ℕ))).pf).comp pf_flatten
  exact h.of_eq (fun _ => rfl)

/-- `Algo.polyFun_rawFuelList`. -/
theorem pf_rawFuelList : PF rawFuelList 1964 40 579 16 := by
  have hsq := (PF.fst (α := List ℕ) (β := List RawPerm)).comp pf_rawSquare
  have hsq2 := hsq.comp pf_rawSquare
  have hmap := (PF.snd (α := List ℕ) (β := List RawPerm)).comp
    (PF.map (PF.const (α := RawPerm) (0 : ℕ)))
  have h1 := (hsq2.pair hsq2).comp pf_append
  have h2 := (h1.pair hsq).comp pf_append
  have h := (h2.pair hmap).comp pf_append
  exact h.of_eq (fun _ => by rfl)

/-- `Algo.polyFun_rawBuildTable` (Schreier–Sims). -/
theorem pf_rawBuildTable : PF rawBuildTable 28114666 737296 2926 80 := by
  have hin := (((PF.fst (α := List ℕ) (β := List RawPerm)).comp pf_rawInitTable).pair
    PF.snd).pair pf_rawFuelList
  have h := (hin.comp pf_rawBuildRoundFold).comp PF.fst
  exact h.of_eq (fun _ => rfl)

/-- `Algo.polyFun_rawShorten`. -/
theorem pf_rawShorten : PF rawShorten 28114667 737296 11772 320 := by
  have h := pf_rawBuildTable.comp pf_rawEntries
  exact h.of_eq (fun _ => rfl)

/-- `Algo.polyFun_tidyGens`. -/
theorem pf_tidyGens : PF tidyGens 194006268 3686480 83772 1600 := by
  have h := ((PF.fst (α := RawStr) (β := RawGens)).pair pf_normGens).comp pf_rawShorten
  exact h.of_eq (fun _ => rfl)

end Explicit
