/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: lifting an answer on the window back to the whole domain
(§11.1, Observation 11.1.11).
-/
import Workspace.Algo.Restrict

/-!
# Constructive membership on a window, and the lift back

Observation 11.1.11 lets a recursive call work on the window `Δ` alone, but the caller needs
the answer on the whole domain `Ω`: "While we concentrate on the action of the elements of `G`
on the window, we maintain their 'tails' — their action on the rest of the permutation
domain."  So the caller must turn a permutation `h` of the window into some `g ∈ G` with
`g|_Δ = h`.  That is constructive membership testing, Proposition 2.2.6 (b).

## How this is done, and why this way

The sifting table of `Workspace/Algo/ChainBuild*.lean` decides membership but returns no
witness.  The note on work package A4 session 4 of `Workspace/Algo/DESIGN.md` proposed a
*labelled* table, whose entries are pairs "(permutation of the window, a full-domain element
restricting to it)", built by running the closure loop in the group of pairs `{(g|_Δ, g)}`.

That is not needed, and the cheaper design is used here.  The point is that a *labelled table
for the window is already a table for `G` whose base lists the window first*: a permutation
group acting on `Fin n` whose base order starts with `Δ` has, for the levels `i < |Δ|`, rows
whose keys are window points and whose entries are full-domain permutations.  So:

* conjugate the generators by the permutation `Algo.rawOrd (dom, Δ)` that lists `Δ` first —
  the same conjugation `Algo.rawPointStab` already uses;
* build the ordinary table with `Algo.rawBuildTable`;
* sift the *target on the window only*, through the first `|Δ|` levels, multiplying the table
  entries together instead of stripping them off;
* conjugate the product back.

The sift never needs the unknown tail: at the level `i` it looks up the key
`cur⁻¹(h(i))`, and `h(i)` and `cur` are both known.  No new table, no group of pairs, and the
whole of `Workspace/Algo/ChainBuild.lean` — its closure loop, `Algo.isTable_buildTable` and
`Algo.complete_buildTable` — applies unchanged.

## Main definitions and results

* `Algo.winSiftAux` — the mathematics of the window sift, and `Algo.winSiftAux_sound`,
  `Algo.winSiftAux_complete`;
* `Algo.rawWinStep`, `Algo.rawWinSift` — the loop on raw data, `Algo.rawWinSift_spec`,
  `Algo.polyFun_rawWinSift`;
* `Algo.rawPreimage` — a preimage of a window permutation, with
  `Algo.rawPreimage_eq_some`, `Algo.rawPreimage_eq_none`, `Algo.polyFun_rawPreimage`.

No axiom and no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)
open scoped Pointwise

variable {n : ℕ}

/-! ## The window sift, as mathematics

`Algo.sift` of `Workspace/Algo/Chain.lean` strips a *known* permutation level by level.  Here
the permutation is known on the levels `0, …, |Δ|−1` only, and the answer wanted is not the
residue but a group element with the prescribed values there.  So the loop multiplies: it
keeps the product `cur` of the entries chosen so far, and at the level `i` it asks the table
for an entry sending `i` to the point `cur⁻¹(f i)`, where `f` is the prescribed target. -/

/-- **Sifting a prescribed target on the first levels.**  `winSiftAux T f k i cur` runs the `k`
levels `i, i+1, …, i+k−1`: at the level `i` it looks up the entry `τ` at the position
`(i, cur⁻¹(f i))` and continues with `cur * τ`.  A missing entry answers `none`. -/
def winSiftAux (T : Table n) (f : ℕ → ℕ) :
    ℕ → ℕ → Perm (Fin n) → Option (Perm (Fin n))
  | 0, _, cur => some cur
  | (k + 1), i, cur =>
      match T i (evalAt cur⁻¹ (f i)) with
      | none => none
      | some τ => winSiftAux T f k (i + 1) (cur * τ)

@[simp] theorem winSiftAux_zero (T : Table n) (f : ℕ → ℕ) (i : ℕ) (cur : Perm (Fin n)) :
    winSiftAux T f 0 i cur = some cur := rfl

theorem winSiftAux_succ_of_none {T : Table n} {f : ℕ → ℕ} {k i : ℕ} {cur : Perm (Fin n)}
    (h : T i (evalAt cur⁻¹ (f i)) = none) : winSiftAux T f (k + 1) i cur = none := by
  show (match T i (evalAt cur⁻¹ (f i)) with
      | none => none
      | some τ => winSiftAux T f k (i + 1) (cur * τ)) = none
  rw [h]

theorem winSiftAux_succ_of_some {T : Table n} {f : ℕ → ℕ} {k i : ℕ} {cur τ : Perm (Fin n)}
    (h : T i (evalAt cur⁻¹ (f i)) = some τ) :
    winSiftAux T f (k + 1) i cur = winSiftAux T f k (i + 1) (cur * τ) := by
  show (match T i (evalAt cur⁻¹ (f i)) with
      | none => none
      | some τ => winSiftAux T f k (i + 1) (cur * τ)) = _
  rw [h]

/-- Reading a level through the inverse and back. -/
theorem evalAt_inv_right (σ : Perm (Fin n)) (i : ℕ) : evalAt σ (evalAt σ⁻¹ i) = i := by
  have h := evalAt_inv_left σ⁻¹ i
  rwa [inv_inv] at h

/-- **The window sift is sound.**  Whatever the sift returns lies in `G`, agrees with the
earlier product below the starting level, and hits the prescribed target on the levels it
ran. -/
theorem winSiftAux_sound {T : Table n} {G : Subgroup (Perm (Fin n))} (hT : IsTable T G)
    (f : ℕ → ℕ) :
    ∀ (k i : ℕ) (cur res : Perm (Fin n)), cur ∈ G → winSiftAux T f k i cur = some res →
      res ∈ G ∧ (∀ j < i, evalAt res j = evalAt cur j) ∧
        (∀ j, i ≤ j → j < i + k → evalAt res j = f j) := by
  intro k
  induction k with
  | zero =>
      intro i cur res hcur h
      have hres : res = cur := (Option.some.inj h).symm
      subst hres
      exact ⟨hcur, fun _ _ => rfl, fun j _ hj => absurd hj (by omega)⟩
  | succ k ih =>
      intro i cur res hcur h
      rcases hlook : T i (evalAt cur⁻¹ (f i)) with _ | τ
      · rw [winSiftAux_succ_of_none hlook] at h; exact absurd h (by simp)
      · rw [winSiftAux_succ_of_some hlook] at h
        have hτG : τ ∈ G := hT.mem hlook
        have hτfix : Fixes i τ := hT.fixes hlook
        have himg : evalAt τ i = evalAt cur⁻¹ (f i) := hT.img hlook
        obtain ⟨hresG, hbelow, hhits⟩ := ih (i + 1) (cur * τ) res (G.mul_mem hcur hτG) h
        refine ⟨hresG, ?_, ?_⟩
        · intro j hj
          rw [hbelow j (by omega), evalAt_mul, hτfix.evalAt hj]
        · intro j hij hj
          rcases Nat.lt_or_ge j (i + 1) with hj1 | hj1
          · have hji : j = i := by omega
            subst hji
            rw [hbelow j (by omega), evalAt_mul, himg, evalAt_inv_right]
          · exact hhits j hj1 (by omega)

/-- **The window sift is complete.**  If some element of `G` has the prescribed values on the
levels to be run, and the product so far is compatible with it, the sift does not get
stuck. -/
theorem winSiftAux_complete {T : Table n} {G : Subgroup (Perm (Fin n))} (hT : IsTable T G)
    (hC : Complete T G) (f : ℕ → ℕ) :
    ∀ (k i : ℕ), i + k ≤ n → ∀ (cur σ : Perm (Fin n)), σ ∈ G → cur ∈ G →
      (∀ j < i, evalAt (cur⁻¹ * σ) j = j) →
      (∀ j, i ≤ j → j < i + k → evalAt σ j = f j) →
      winSiftAux T f k i cur ≠ none := by
  intro k
  induction k with
  | zero => intro i _ cur σ _ _ _ _; simp
  | succ k ih =>
      intro i hik cur σ hσ hcur hfix hf
      have hin : i < n := by omega
      have hρG : cur⁻¹ * σ ∈ G := G.mul_mem (G.inv_mem hcur) hσ
      have hρ : cur⁻¹ * σ ∈ chainStab G i := ⟨hρG, fixes_of_evalAt hfix⟩
      have hkey : evalAt (cur⁻¹ * σ) i = evalAt cur⁻¹ (f i) := by
        rw [evalAt_mul, hf i le_rfl (by omega)]
      rcases hlook : T i (evalAt cur⁻¹ (f i)) with _ | τ
      · exact absurd (hkey ▸ hlook) (hC i hin _ hρ)
      · rw [winSiftAux_succ_of_some hlook]
        have hτG : τ ∈ G := hT.mem hlook
        have hτfix : Fixes i τ := hT.fixes hlook
        have himg : evalAt τ i = evalAt cur⁻¹ (f i) := hT.img hlook
        refine ih (i + 1) (by omega) (cur * τ) σ hσ (G.mul_mem hcur hτG) ?_ ?_
        · intro j hj
          have hsplit : (cur * τ)⁻¹ * σ = τ⁻¹ * (cur⁻¹ * σ) := by
            rw [mul_inv_rev, mul_assoc]
          rcases Nat.lt_or_ge j i with hj1 | hj1
          · rw [hsplit, evalAt_mul, hfix j hj1, hτfix.inv.evalAt hj1]
          · have hji : j = i := by omega
            subst hji
            rw [hsplit, evalAt_mul, hkey, ← himg, evalAt_inv_left]
        · intro j hij hj
          exact hf j (by omega) (by omega)

/-! ## The window sift, on raw data -/

/-- **One round of the window sift.**  The parameter is the table together with the target on
the window; the accumulator is the product so far, or `none` once a level has had no entry. -/
def rawWinStep (p : (RawTable × RawPerm) × (Option RawPerm × ℕ)) : Option RawPerm :=
  match p.2.1 with
  | none => none
  | some cur =>
      match rawTableGet (p.1.1, (p.2.2, rawApply (rawInv cur, rawApply (p.1.2, p.2.2)))) with
      | none => none
      | some τ => some (rawMul (cur, τ))

/-- **The window sift on raw data.**  One round per level of the window. -/
def rawWinSift (p : (RawTable × RawPerm) × (Option RawPerm × List ℕ)) : Option RawPerm :=
  List.foldl (fun acc i => rawWinStep (p.1, (acc, i))) p.2.1 p.2.2

theorem rawWinStep_none (t : RawTable) (hr : RawPerm) (i : ℕ) :
    rawWinStep ((t, hr), (none, i)) = none := rfl

theorem rawWinFold_none (t : RawTable) (hr : RawPerm) :
    ∀ l : List ℕ, List.foldl (fun acc i => rawWinStep ((t, hr), (acc, i))) none l = none := by
  intro l
  induction l with
  | nil => rfl
  | cons a s ih => rw [List.foldl_cons, rawWinStep_none]; exact ih

/-- **The specification of the raw loop**: it computes `Algo.winSiftAux` of the decoded
table, for the target read off the raw window permutation. -/
theorem rawWinFold_spec {t : RawTable} (ht : RawTable.WF n t) (hr : RawPerm) :
    ∀ (k i : ℕ) (c : Perm (Fin n)),
      List.foldl (fun acc j => rawWinStep ((t, hr), (acc, j))) (some (encPerm n c))
          (List.range' i k)
        = (winSiftAux (decTable n t) (fun j => rawApply (hr, j)) k i c).map (encPerm n) := by
  intro k
  induction k with
  | zero => intro i c; rfl
  | succ k ih =>
      intro i c
      have hlist : List.range' i (k + 1) = i :: List.range' (i + 1) k := rfl
      rw [hlist, List.foldl_cons]
      have hkey : rawApply (rawInv (encPerm n c), rawApply (hr, i))
          = evalAt c⁻¹ (rawApply (hr, i)) := by
        rw [rawInv_encPerm, rawApply_encPerm_eq_evalAt]
      have hstep : rawWinStep ((t, hr), (some (encPerm n c), i))
          = (rawTableGet (t, (i, evalAt c⁻¹ (rawApply (hr, i))))).map
              (fun τ => rawMul (encPerm n c, τ)) := by
        show (match rawTableGet (t, (i, rawApply (rawInv (encPerm n c), rawApply (hr, i)))) with
            | none => none
            | some τ => some (rawMul (encPerm n c, τ))) = _
        rw [hkey]
        rcases rawTableGet (t, (i, evalAt c⁻¹ (rawApply (hr, i)))) with _ | τ <;> rfl
      rcases hlook : rawTableGet (t, (i, evalAt c⁻¹ (rawApply (hr, i)))) with _ | τ
      · rw [hstep, hlook]
        simp only [Option.map_none]
        rw [rawWinFold_none t hr]
        have hdec : decTable n t i (evalAt c⁻¹ (rawApply (hr, i))) = none := by
          rw [decTable, hlook]; rfl
        rw [winSiftAux_succ_of_none (f := fun j => rawApply (hr, j)) hdec]
        rfl
      · have hwf : RawPerm.WF n τ := wf_of_tableEntry ht ⟨i, _, hlook⟩
        have hdec : decTable n t i (evalAt c⁻¹ (rawApply (hr, i))) = some (decPerm n τ) := by
          rw [decTable, hlook]; rfl
        rw [hstep, hlook]
        simp only [Option.map_some]
        have hres : rawMul (encPerm n c, τ) = encPerm n (c * decPerm n τ) := by
          rw [← encPerm_decPerm hwf, rawMul_encPerm, encPerm_decPerm hwf]
        rw [hres, ih (i + 1) (c * decPerm n τ), winSiftAux_succ_of_some (f := fun j => rawApply (hr, j)) hdec]

/-- **The specification of `Algo.rawWinSift`**, started at the identity and run over the
levels of the window. -/
theorem rawWinSift_spec {t : RawTable} (ht : RawTable.WF n t) (hr : RawPerm) (dom Δ : List ℕ)
    (hdom : dom.length = n) :
    rawWinSift ((t, hr), (some (rawOne dom), rawOne Δ))
      = (winSiftAux (decTable n t) (fun j => rawApply (hr, j)) Δ.length 0 1).map
          (encPerm n) := by
  subst hdom
  rw [rawWinSift, rawOne_eq dom, rawOne, List.range_eq_range']
  exact rawWinFold_spec ht hr Δ.length 0 1

/-! ## The running time of the window sift

The accumulator is a product of table entries, so its length is the length of the last entry
used (or of the start), and its own entries are entries of the start or of a table entry.
That is the bound `RAM.PolyFun.foldlParam` asks for. -/

theorem rawWinFold_struct (t : RawTable) (hr : RawPerm) :
    ∀ (l : List ℕ) (r : RawPerm),
      List.foldl (fun acc i => rawWinStep ((t, hr), (acc, i))) (some r) l = none ∨
      ∃ r', List.foldl (fun acc i => rawWinStep ((t, hr), (acc, i))) (some r) l = some r' ∧
        (r'.length ≤ r.length ∨ ∃ τ, TableEntry t τ ∧ r'.length ≤ τ.length) ∧
        (∀ x ∈ r', x ∈ r ∨ ∃ τ, TableEntry t τ ∧ x ∈ τ) := by
  intro l
  induction l with
  | nil => intro r; exact Or.inr ⟨r, rfl, Or.inl le_rfl, fun x hx => Or.inl hx⟩
  | cons a s ih =>
      intro r
      rw [List.foldl_cons]
      rcases hstep : rawWinStep ((t, hr), (some r, a)) with _ | r₁
      · left; exact rawWinFold_none t hr s
      · have hr₁ : ∃ τ, TableEntry t τ ∧ r₁ = rawMul (r, τ) := by
          rcases hlook : rawTableGet (t, (a, rawApply (rawInv r, rawApply (hr, a)))) with _ | τ
          · exfalso
            have hz : rawWinStep ((t, hr), (some r, a)) = none := by
              show (match rawTableGet (t, (a, rawApply (rawInv r, rawApply (hr, a)))) with
                  | none => none
                  | some τ => some (rawMul (r, τ))) = none
              rw [hlook]
            rw [hz] at hstep
            exact absurd hstep (by simp)
          · refine ⟨τ, ⟨a, _, hlook⟩, ?_⟩
            have hz : rawWinStep ((t, hr), (some r, a)) = some (rawMul (r, τ)) := by
              show (match rawTableGet (t, (a, rawApply (rawInv r, rawApply (hr, a)))) with
                  | none => none
                  | some τ => some (rawMul (r, τ))) = _
              rw [hlook]
            rw [hz] at hstep
            exact (Option.some.inj hstep).symm
        obtain ⟨τ, hτ, hr₁eq⟩ := hr₁
        have hlen : r₁.length = τ.length := by rw [hr₁eq, length_rawMul]
        have hmem : ∀ x ∈ r₁, x ∈ r ∨ ∃ τ, TableEntry t τ ∧ x ∈ τ := by
          intro x hx
          rw [hr₁eq] at hx
          rcases mem_rawMul hx with h | h
          · exact Or.inl h
          · exact Or.inr ⟨τ, hτ, h⟩
        rcases ih r₁ with h | ⟨r', hr', hlen', hmem'⟩
        · exact Or.inl h
        · refine Or.inr ⟨r', hr', ?_, ?_⟩
          · rcases hlen' with h1 | ⟨τ', hτ', h1⟩
            · exact Or.inr ⟨τ, hτ, by omega⟩
            · exact Or.inr ⟨τ', hτ', h1⟩
          · intro x hx
            rcases hmem' x hx with h1 | h1
            · exact hmem x h1
            · exact Or.inr h1

theorem polyFun_rawWinStep : PolyFun rawWinStep := by
  have hinner : PolyFun (fun z : RawPerm × ((RawTable × RawPerm) × ℕ) =>
      match rawTableGet (z.2.1.1, (z.2.2, rawApply (rawInv z.1, rawApply (z.2.1.2, z.2.2)))) with
      | none => none
      | some τ => some (rawMul (z.1, τ))) := by
    have hlook : PolyFun (fun z : RawPerm × ((RawTable × RawPerm) × ℕ) =>
        rawTableGet (z.2.1.1, (z.2.2, rawApply (rawInv z.1, rawApply (z.2.1.2, z.2.2))))) :=
      ((((polyFun_snd.comp polyFun_fst).comp polyFun_fst)).pair
        ((polyFun_snd.comp polyFun_snd).pair
          (((polyFun_fst.comp polyFun_rawInv).pair
            (((((polyFun_snd.comp polyFun_fst).comp polyFun_snd)).pair
              (polyFun_snd.comp polyFun_snd)).comp polyFun_rawApply)).comp
            polyFun_rawApply))).comp polyFun_rawTableGet
    have hsome : PolyFun (fun w : RawPerm × (RawPerm × ((RawTable × RawPerm) × ℕ)) =>
        (some (rawMul (w.2.1, w.1)) : Option RawPerm)) :=
      (((polyFun_snd.comp polyFun_fst).pair polyFun_fst).comp polyFun_rawMul).comp polyFun_some
    refine ((hlook.pair polyFun_id).comp
      (PolyFun.optionElim (polyFun_none (β := RawPerm)) hsome)).of_eq (fun z => ?_)
    rcases rawTableGet (z.2.1.1, (z.2.2, rawApply (rawInv z.1, rawApply (z.2.1.2, z.2.2))))
      with _ | τ <;> simp
  have hin : PolyFun (fun p : (RawTable × RawPerm) × (Option RawPerm × ℕ) =>
      ((p.2.1, ((p.1, p.2.2) : (RawTable × RawPerm) × ℕ)) :
        Option RawPerm × ((RawTable × RawPerm) × ℕ))) :=
    (polyFun_snd.comp polyFun_fst).pair (polyFun_fst.pair (polyFun_snd.comp polyFun_snd))
  refine (hin.comp (PolyFun.optionElim (polyFun_none (β := RawPerm)) hinner)).of_eq
    (fun p => ?_)
  obtain ⟨c, o, i⟩ := p
  cases o <;> rfl

set_option maxHeartbeats 1000000 in
/-- **The window sift is a `RAM.PolyFun`.** -/
theorem polyFun_rawWinSift : PolyFun rawWinSift := by
  have hacc : ∀ (cc : RawTable × RawPerm) (x : Option RawPerm) (r : List ℕ) (j : ℕ),
      Enc.size (List.foldl (fun y a => rawWinStep (cc, (y, a))) x (r.take j))
        ≤ (fun m => 3 + m * (2 * m + 1))
            (Enc.size ((cc, (x, r)) : (RawTable × RawPerm) × (Option RawPerm × List ℕ))) := by
    intro cc x r j
    obtain ⟨t, hr⟩ := cc
    set N := Enc.size (((t, hr), (x, r)) :
      (RawTable × RawPerm) × (Option RawPerm × List ℕ)) with hN
    have hcc : Enc.size ((t, hr) : RawTable × RawPerm) ≤ N :=
      Combine.size_fst_le ((t, hr) : RawTable × RawPerm) ((x, r) : Option RawPerm × List ℕ)
    have ht : Enc.size t ≤ N := le_trans (Combine.size_fst_le t hr) hcc
    have hxr : Enc.size ((x, r) : Option RawPerm × List ℕ) ≤ N :=
      Combine.size_snd_le ((t, hr) : RawTable × RawPerm) ((x, r) : Option RawPerm × List ℕ)
    have hx : Enc.size x ≤ N := le_trans (Combine.size_fst_le x r) hxr
    have hentry : ∀ τ : RawPerm, TableEntry t τ → Enc.size τ ≤ N :=
      fun τ hτ => le_trans (size_le_of_tableEntry hτ) ht
    rcases x with _ | r₀
    · rw [rawWinFold_none]
      have : Enc.size (none : Option RawPerm) = 2 := size_none
      dsimp only
      omega
    · have hr₀ : Enc.size r₀ ≤ N := by
        have := size_some_eq r₀
        omega
      rcases rawWinFold_struct t hr (r.take j) r₀ with h | ⟨r', h, hlen, hmem⟩
      · rw [h]
        have : Enc.size (none : Option RawPerm) = 2 := size_none
        dsimp only
        omega
      · rw [h]
        have hent : ∀ y ∈ r', Enc.size y ≤ N := by
          intro y hy
          rcases hmem y hy with hy' | ⟨τ, hτ, hy'⟩
          · exact le_trans (size_mem_le hy') hr₀
          · exact le_trans (size_mem_le hy') (hentry τ hτ)
        have hsize := size_list_le_of_entries r' N hent
        have hlen2 : r'.length ≤ N := by
          rcases hlen with h1 | ⟨τ, hτ, h1⟩
          · have := length_le_size r₀
            omega
          · have h2 := length_le_size τ
            have h3 := hentry τ hτ
            omega
        have hmul : r'.length * (2 * N + 1) ≤ N * (2 * N + 1) := Nat.mul_le_mul_right _ hlen2
        have hsome := size_some_eq r'
        dsimp only
        omega
  have hfold := PolyFun.foldlParam polyFun_rawWinStep
    (p := fun m => 3 + m * (2 * m + 1))
    ((polyBound_const 3).add (polyBound_id.mul
      (((polyBound_const 2).mul polyBound_id).add (polyBound_const 1))))
    hacc
  exact hfold.of_eq (fun p => rfl)

/-! ## A preimage under the restriction to the window

The routine conjugates the generators so that the window becomes the initial segment
`{0, …, |Δ|−1}` of the domain, builds the ordinary table, sifts the target through the levels
of the window, and conjugates the product back.  Paper: Observation 11.1.11 (§11.1), and
Proposition 2.2.6 (b) for the constructive membership it rests on. -/

/-- **The table in which the window is the initial segment.**  The generators are conjugated by
`Algo.rawOrd`, which lists `Δ` first, exactly as in `Algo.rawPointStab`. -/
def rawWinTable (p : (List ℕ × List RawPerm) × List ℕ) : RawTable :=
  rawBuildTable (p.1.1, rawConj (rawOrd (p.1.1, p.2), p.1.2))

/-- **A preimage of a permutation of the window.**  `p.1` is the domain witness with the
generator list, `p.2.1` is the window `Δ` and `p.2.2` is the wanted permutation of the window,
in window labels.  The answer is some `g ∈ G` with `g|_Δ = h`, or `none` when there is
none. -/
def rawPreimage (p : (List ℕ × List RawPerm) × (List ℕ × RawPerm)) : Option RawPerm :=
  match rawWinSift ((rawWinTable (p.1, p.2.1), p.2.2), (some (rawOne p.1.1), rawOne p.2.1)) with
  | none => none
  | some cur =>
      some (rawMul (rawOrd (p.1.1, p.2.1), rawMul (cur, rawInv (rawOrd (p.1.1, p.2.1)))))

theorem rawPreimage_of_none {p : (List ℕ × List RawPerm) × (List ℕ × RawPerm)}
    (h : rawWinSift ((rawWinTable (p.1, p.2.1), p.2.2), (some (rawOne p.1.1), rawOne p.2.1))
      = none) : rawPreimage p = none := by
  show (match rawWinSift ((rawWinTable (p.1, p.2.1), p.2.2),
      (some (rawOne p.1.1), rawOne p.2.1)) with
    | none => none
    | some cur =>
        some (rawMul (rawOrd (p.1.1, p.2.1), rawMul (cur, rawInv (rawOrd (p.1.1, p.2.1)))))) = _
  rw [h]

theorem rawPreimage_of_some {p : (List ℕ × List RawPerm) × (List ℕ × RawPerm)} {cur : RawPerm}
    (h : rawWinSift ((rawWinTable (p.1, p.2.1), p.2.2), (some (rawOne p.1.1), rawOne p.2.1))
      = some cur) :
    rawPreimage p
      = some (rawMul (rawOrd (p.1.1, p.2.1), rawMul (cur, rawInv (rawOrd (p.1.1, p.2.1))))) := by
  show (match rawWinSift ((rawWinTable (p.1, p.2.1), p.2.2),
      (some (rawOne p.1.1), rawOne p.2.1)) with
    | none => none
    | some cur =>
        some (rawMul (rawOrd (p.1.1, p.2.1), rawMul (cur, rawInv (rawOrd (p.1.1, p.2.1)))))) = _
  rw [h]

section Preimage

variable {dom Δ : List ℕ} {gens : List (Perm (Fin n))}

/-- **The base reordering sends the label `k` to the point `Δ[k]`.** -/
theorem decPerm_rawOrd_lt (hdom : dom.length = n) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    {k : ℕ} (hk : k < Δ.length) (hkn : k < n) :
    ((decPerm n (rawOrd (dom, Δ))) ⟨k, hkn⟩ : ℕ) = Δ[k] := by
  have hwf := wf_rawOrd hdom hnd hlt
  rw [decPerm_val_of_wf hwf ⟨k, hkn⟩]
  show (Δ ++ (rawOne dom).filter (fun x => if decide (x ∈ Δ) then false else true))[k]'_ = _
  exact List.getElem_append_left hk

/-- **The base reordering sends the point `Δ[j]` back to the label `j`.** -/
theorem decPerm_rawOrd_symm (hdom : dom.length = n) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    {j : ℕ} (hj : j < Δ.length) (hjn : j < n) :
    (decPerm n (rawOrd (dom, Δ)))⁻¹ ⟨Δ[j], hlt _ (List.getElem_mem hj)⟩ = ⟨j, hjn⟩ := by
  have h1 : (decPerm n (rawOrd (dom, Δ))) ⟨j, hjn⟩
      = ⟨Δ[j], hlt _ (List.getElem_mem hj)⟩ :=
    Fin.ext (decPerm_rawOrd_lt hdom hnd hlt hj hjn)
  rw [← h1]
  exact Equiv.symm_apply_apply _ _

/-- **The conjugate reads the restriction.**  Conjugating by the base reordering turns the
restriction of `σ` to the window into the action of the conjugate on the first `|Δ|`
levels. -/
theorem evalAt_conj_eq_winRestrict (hdom : dom.length = n) (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) {G : Subgroup (Perm (Fin n))}
    (hinv : Babai.IsInvariant G (winSet n Δ)) {σ : Perm (Fin n)} (hσ : σ ∈ G) {k : ℕ}
    (hk : k < Δ.length) :
    evalAt ((decPerm n (rawOrd (dom, Δ)))⁻¹ * σ * decPerm n (rawOrd (dom, Δ))) k
      = ((winRestrictHom n Δ hnd hlt G hinv ⟨σ, hσ⟩ ⟨k, hk⟩ : Fin Δ.length) : ℕ) := by
  have hmn : Δ.length ≤ n := length_le_of_nodup hnd hlt
  have hkn : k < n := lt_of_lt_of_le hk hmn
  set j : ℕ := ((winRestrictHom n Δ hnd hlt G hinv ⟨σ, hσ⟩ ⟨k, hk⟩ : Fin Δ.length) : ℕ) with hjdef
  have hjlt : j < Δ.length := (winRestrictHom n Δ hnd hlt G hinv ⟨σ, hσ⟩ ⟨k, hk⟩).isLt
  have hjn : j < n := lt_of_lt_of_le hjlt hmn
  have hval : Δ[j] = (σ ⟨Δ[k], hlt _ (List.getElem_mem hk)⟩ : ℕ) := by
    have hv := winRestrictHom_val Δ hnd hlt hinv ⟨σ, hσ⟩ ⟨k, hk⟩
    rw [List.getD_eq_getElem _ _ hjlt] at hv
    rw [hv, winEquiv_coe Δ hnd hlt hk]
  rw [evalAt_of_lt _ hkn]
  have h1 : (decPerm n (rawOrd (dom, Δ))) ⟨k, hkn⟩
      = ⟨Δ[k], hlt _ (List.getElem_mem hk)⟩ :=
    Fin.ext (decPerm_rawOrd_lt hdom hnd hlt hk hkn)
  have h2 : σ ⟨Δ[k], hlt _ (List.getElem_mem hk)⟩ = ⟨Δ[j], hlt _ (List.getElem_mem hjlt)⟩ :=
    Fin.ext hval.symm
  show (((decPerm n (rawOrd (dom, Δ)))⁻¹ (σ ((decPerm n (rawOrd (dom, Δ))) ⟨k, hkn⟩))) : ℕ) = j
  rw [h1, h2, decPerm_rawOrd_symm hdom hnd hlt hjlt hjn]

/-- The generators conjugated so that the window is the initial segment. -/
private noncomputable def conjGens (dom Δ : List ℕ) (gens : List (Perm (Fin n))) :
    List (Perm (Fin n)) :=
  gens.map (fun g => (MulAut.conj (decPerm n (rawOrd (dom, Δ)))⁻¹) g)

/-- The window sift of `Algo.rawPreimage`, read as mathematics. -/
private theorem rawPreimage_sift (hdom : dom.length = n) (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) (hw : Perm (Fin Δ.length)) :
    rawWinSift ((rawWinTable ((dom, gens.map (encPerm n)), Δ), encPerm Δ.length hw),
        (some (rawOne dom), rawOne Δ))
      = (winSiftAux (tableOf (buildTable n (conjGens dom Δ gens)))
          (fun j => rawApply (encPerm Δ.length hw, j)) Δ.length 0 1).map (encPerm n) := by
  have hwf := wf_rawOrd hdom hnd hlt
  have hconj : rawConj (rawOrd (dom, Δ), gens.map (encPerm n))
      = (conjGens dom Δ gens).map (encPerm n) := rawConj_spec hwf gens
  rw [rawWinTable]
  show rawWinSift ((rawBuildTable (dom, rawConj (rawOrd (dom, Δ), gens.map (encPerm n))),
      encPerm Δ.length hw), (some (rawOne dom), rawOne Δ)) = _
  rw [hconj, rawWinSift_spec (wf_rawBuildTable dom hdom _) _ dom Δ hdom,
    decTable_rawBuildTable dom hdom _]

/-- The conjugated group is the conjugate of the group. -/
private theorem mem_conjGens (hdom : dom.length = n) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    (x : Perm (Fin n)) :
    x ∈ genGroup (conjGens dom Δ gens) ↔
      ∃ σ ∈ genGroup gens,
        (decPerm n (rawOrd (dom, Δ)))⁻¹ * σ * decPerm n (rawOrd (dom, Δ)) = x := by
  rw [conjGens, genGroup_map_conj, Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨σ, hσ, ?_⟩
    show _ = (decPerm n (rawOrd (dom, Δ)))⁻¹ * σ * (decPerm n (rawOrd (dom, Δ)))⁻¹⁻¹
    rw [inv_inv]
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨σ, hσ, ?_⟩
    show (decPerm n (rawOrd (dom, Δ)))⁻¹ * σ * (decPerm n (rawOrd (dom, Δ)))⁻¹⁻¹ = _
    rw [inv_inv]

/-- **The routine answers a genuine preimage.**  Paper: Observation 11.1.11 (§11.1). -/
theorem rawPreimage_eq_some (hdom : dom.length = n) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    (hinv : Babai.IsInvariant (genGroup gens) (winSet n Δ)) {hw : Perm (Fin Δ.length)}
    {gres : RawPerm}
    (h : rawPreimage ((dom, gens.map (encPerm n)), (Δ, encPerm Δ.length hw)) = some gres) :
    ∃ (σ : Perm (Fin n)) (hσ : σ ∈ genGroup gens),
      gres = encPerm n σ ∧ winRestrictHom n Δ hnd hlt (genGroup gens) hinv ⟨σ, hσ⟩ = hw := by
  have hordwf := wf_rawOrd (Δ := Δ) hdom hnd hlt
  have hordenc : encPerm n (decPerm n (rawOrd (dom, Δ))) = rawOrd (dom, Δ) :=
    encPerm_decPerm hordwf
  have hsift := rawPreimage_sift (gens := gens) hdom hnd hlt hw
  rcases hs : rawWinSift ((rawWinTable ((dom, gens.map (encPerm n)), Δ), encPerm Δ.length hw),
      (some (rawOne dom), rawOne Δ)) with _ | curRaw
  · rw [rawPreimage_of_none (p := ((dom, gens.map (encPerm n)), (Δ, encPerm Δ.length hw))) hs]
      at h
    exact absurd h (by simp)
  · rw [hs] at hsift
    rcases hmath : winSiftAux (tableOf (buildTable n (conjGens dom Δ gens)))
        (fun j => rawApply (encPerm Δ.length hw, j)) Δ.length 0 1 with _ | c
    · rw [hmath] at hsift; exact absurd hsift (by simp)
    · rw [hmath] at hsift
      have hcur : curRaw = encPerm n c := by
        simpa using hsift
      obtain ⟨hcG, -, hhits⟩ := winSiftAux_sound
        (isTable_buildTable n (conjGens dom Δ gens)) _ Δ.length 0 1 c
        (Subgroup.one_mem _) hmath
      obtain ⟨σ, hσ, hcσ⟩ := (mem_conjGens (gens := gens) hdom hnd hlt c).1 hcG
      refine ⟨σ, hσ, ?_, ?_⟩
      · rw [rawPreimage_of_some (p := ((dom, gens.map (encPerm n)), (Δ, encPerm Δ.length hw)))
          hs] at h
        have hg := Option.some.inj h
        rw [← hg, hcur, ← hordenc, rawInv_encPerm, rawMul_encPerm, rawMul_encPerm]
        congr 1
        rw [← hcσ]
        group
      · refine Equiv.ext (fun k => Fin.ext ?_)
        have hkk := hhits (k : ℕ) (Nat.zero_le _) (by simpa using k.isLt)
        have hbridge := evalAt_conj_eq_winRestrict (dom := dom) hdom hnd hlt hinv hσ k.isLt
        rw [hcσ] at hbridge
        rw [← hbridge, hkk, rawApply_encPerm Δ.length hw k.isLt]

/-- **The routine answers `none` only when there is no preimage.**  Paper: Observation 11.1.11
(§11.1). -/
theorem rawPreimage_eq_none (hdom : dom.length = n) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    (hinv : Babai.IsInvariant (genGroup gens) (winSet n Δ)) {hw : Perm (Fin Δ.length)}
    (h : rawPreimage ((dom, gens.map (encPerm n)), (Δ, encPerm Δ.length hw)) = none)
    (σ : Perm (Fin n)) (hσ : σ ∈ genGroup gens) :
    winRestrictHom n Δ hnd hlt (genGroup gens) hinv ⟨σ, hσ⟩ ≠ hw := by
  intro heq
  have hsift := rawPreimage_sift (gens := gens) hdom hnd hlt hw
  rcases hs : rawWinSift ((rawWinTable ((dom, gens.map (encPerm n)), Δ), encPerm Δ.length hw),
      (some (rawOne dom), rawOne Δ)) with _ | curRaw
  · rw [hs] at hsift
    have hmath : winSiftAux (tableOf (buildTable n (conjGens dom Δ gens)))
        (fun j => rawApply (encPerm Δ.length hw, j)) Δ.length 0 1 = none := by
      rcases hm : winSiftAux (tableOf (buildTable n (conjGens dom Δ gens)))
          (fun j => rawApply (encPerm Δ.length hw, j)) Δ.length 0 1 with _ | c
      · rfl
      · rw [hm] at hsift; exact absurd hsift.symm (by simp)
    refine winSiftAux_complete (isTable_buildTable n (conjGens dom Δ gens))
      (complete_buildTable n (conjGens dom Δ gens)) _ Δ.length 0
      (by simpa using length_le_of_nodup hnd hlt) 1
      ((decPerm n (rawOrd (dom, Δ)))⁻¹ * σ * decPerm n (rawOrd (dom, Δ)))
      ((mem_conjGens (gens := gens) hdom hnd hlt _).2 ⟨σ, hσ, rfl⟩)
      (Subgroup.one_mem _) (fun j hj => absurd hj (by omega)) ?_ hmath
    intro j _ hj
    have hjΔ : j < Δ.length := by simpa using hj
    rw [evalAt_conj_eq_winRestrict hdom hnd hlt hinv hσ hjΔ, heq,
      rawApply_encPerm Δ.length hw hjΔ]
  · rw [rawPreimage_of_some (p := ((dom, gens.map (encPerm n)), (Δ, encPerm Δ.length hw)))
      hs] at h
    exact absurd h (by simp)

end Preimage

/-! ## The running time of the preimage -/

theorem polyFun_rawWinTable : PolyFun rawWinTable := by
  have hord : PolyFun (fun p : (List ℕ × List RawPerm) × List ℕ => rawOrd (p.1.1, p.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_rawOrd
  have hconj : PolyFun (fun p : (List ℕ × List RawPerm) × List ℕ =>
      rawConj (rawOrd (p.1.1, p.2), p.1.2)) :=
    (hord.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_rawConj
  exact (((polyFun_fst.comp polyFun_fst).pair hconj).comp polyFun_rawBuildTable).of_eq
    (fun _ => rfl)

set_option maxHeartbeats 1000000 in
theorem polyFun_rawPreimage : PolyFun rawPreimage := by
  have hord : PolyFun (fun p : (List ℕ × List RawPerm) × (List ℕ × RawPerm) =>
      rawOrd (p.1.1, p.2.1)) :=
    ((polyFun_fst.comp polyFun_fst).pair (polyFun_snd.comp polyFun_fst)).comp polyFun_rawOrd
  have htab : PolyFun (fun p : (List ℕ × List RawPerm) × (List ℕ × RawPerm) =>
      rawWinTable (p.1, p.2.1)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_rawWinTable
  have hsift : PolyFun (fun p : (List ℕ × List RawPerm) × (List ℕ × RawPerm) =>
      rawWinSift ((rawWinTable (p.1, p.2.1), p.2.2),
        (some (rawOne p.1.1), rawOne p.2.1))) :=
    ((htab.pair (polyFun_snd.comp polyFun_snd)).pair
      ((((polyFun_fst.comp polyFun_fst).comp polyFun_rawOne).comp polyFun_some).pair
        ((polyFun_snd.comp polyFun_fst).comp polyFun_rawOne))).comp polyFun_rawWinSift
  have hsome : PolyFun (fun w : RawPerm × ((List ℕ × List RawPerm) × (List ℕ × RawPerm)) =>
      (some (rawMul (rawOrd (w.2.1.1, w.2.2.1),
        rawMul (w.1, rawInv (rawOrd (w.2.1.1, w.2.2.1))))) : Option RawPerm)) := by
    have hord' : PolyFun (fun w : RawPerm × ((List ℕ × List RawPerm) × (List ℕ × RawPerm)) =>
        rawOrd (w.2.1.1, w.2.2.1)) := (polyFun_snd.comp hord)
    exact ((hord'.pair ((polyFun_fst.pair (hord'.comp polyFun_rawInv)).comp
      polyFun_rawMul)).comp polyFun_rawMul).comp polyFun_some
  refine ((hsift.pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_none (β := RawPerm)) hsome)).of_eq (fun p => ?_)
  show _ = (match rawWinSift ((rawWinTable (p.1, p.2.1), p.2.2),
      (some (rawOne p.1.1), rawOne p.2.1)) with
    | none => none
    | some cur =>
        some (rawMul (rawOrd (p.1.1, p.2.1), rawMul (cur, rawInv (rawOrd (p.1.1, p.2.1)))))) 
  rcases rawWinSift ((rawWinTable (p.1, p.2.1), p.2.2), (some (rawOne p.1.1), rawOne p.2.1))
    with _ | cur <;> simp

/-! ## Observation 11.1.11: generators of the full preimage

> Adding to `S` a set of generators of the kernel of the `G`-action on `Δ` we obtain a set of
> generators of `Aut^Δ_G(x)`.

`Babai.Observation_11_1_11_generators` of `Workspace/Luks/Framework.lean` is that sentence.
The routine `Algo.rawLiftGens` is that sentence as a program: a preimage of each generator of
the answer group on the window, together with `Algo.rawPointStab`, which is the kernel. -/

section Lift

variable {dom Δ : List ℕ} {gens : List (Perm (Fin n))}

theorem restrictHom_coe {G : Subgroup (Perm (Fin n))} (hinv : Babai.IsInvariant G (winSet n Δ))
    (g : G) (u : ↥(winSet n Δ)) :
    ((Babai.restrictHom G (winSet n Δ) hinv g u : ↥(winSet n Δ)) : Fin n)
      = (g : Perm (Fin n)) (u : Fin n) := rfl

/-- **The kernel of the restriction to the window fixes the window pointwise.**  Paper: "the
kernel of the `G`-action on `Δ`", Observation 11.1.11 (§11.1). -/
theorem mem_ker_winRestrictHom (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    {G : Subgroup (Perm (Fin n))} (hinv : Babai.IsInvariant G (winSet n Δ)) (a : G) :
    a ∈ (winRestrictHom n Δ hnd hlt G hinv).ker ↔
      ∀ u ∈ winSet n Δ, (a : Perm (Fin n)) u = u := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h u hu
    have hk := congrArg (fun p : Perm (Fin Δ.length) =>
      p ((winEquiv n Δ hnd hlt).symm ⟨u, hu⟩)) h
    simp only [winRestrictHom_apply, Equiv.Perm.coe_one, id_eq] at hk
    rw [Equiv.apply_symm_apply] at hk
    have hk2 := congrArg (winEquiv n Δ hnd hlt) hk
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hk2
    exact congrArg (fun z : ↥(winSet n Δ) => (z : Fin n)) hk2
  · intro h
    refine Equiv.ext (fun k => ?_)
    rw [winRestrictHom_apply]
    have hfix : Babai.restrictHom G (winSet n Δ) hinv a (winEquiv n Δ hnd hlt k)
        = winEquiv n Δ hnd hlt k :=
      Subtype.ext (h _ (winEquiv n Δ hnd hlt k).2)
    rw [hfix, Equiv.symm_apply_apply]
    rfl

/-- **The full preimage of a subgroup of `G^Δ`.**  This is `Aut^Δ_G(x)` of Observation
11.1.11 when `H` is `Aut_{G^Δ}(x^Δ)`. -/
noncomputable def winPreimage (n : ℕ) (Δ : List ℕ) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    (G : Subgroup (Perm (Fin n))) (hinv : Babai.IsInvariant G (winSet n Δ))
    (H : Subgroup (Perm (Fin Δ.length))) : Subgroup (Perm (Fin n)) :=
  (Subgroup.comap (winRestrictHom n Δ hnd hlt G hinv) H).map G.subtype

theorem mem_winPreimage (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    {G : Subgroup (Perm (Fin n))} (hinv : Babai.IsInvariant G (winSet n Δ))
    (H : Subgroup (Perm (Fin Δ.length))) (g : Perm (Fin n)) :
    g ∈ winPreimage n Δ hnd hlt G hinv H ↔
      ∃ hg : g ∈ G, winRestrictHom n Δ hnd hlt G hinv ⟨g, hg⟩ ∈ H := by
  rw [winPreimage, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨y, hy⟩, hmem, rfl⟩
    exact ⟨hy, hmem⟩
  · rintro ⟨hg, hmem⟩
    exact ⟨⟨g, hg⟩, hmem, rfl⟩

/-- The group generated by a concatenated list of raw generators. -/
theorem decGroup_append (n : ℕ) (a b : RawGens) :
    decGroup n (a ++ b) = decGroup n a ⊔ decGroup n b := by
  rw [decGroup, decGroup, decGroup, genGroup, genGroup, genGroup, List.map_append,
    ← Subgroup.closure_union]
  congr 1
  ext y
  simp

/-- **Generators of the full preimage of a subgroup of `G^Δ`.**  `p.2.2` is a generating list
of the subgroup of `G^Δ`, in window labels; the answer is one preimage per generator, together
with `Algo.rawPointStab`, the kernel.  Paper: Observation 11.1.11 (§11.1). -/
def rawLiftGens (p : (List ℕ × List RawPerm) × (List ℕ × List RawPerm)) : List RawPerm :=
  p.2.2.map (fun hh => (rawPreimage (p.1, (p.2.1, hh))).getD (rawOne p.1.1))
    ++ rawPointStab (p.1, p.2.1)

/-- **The routine returns a generating list of the full preimage.**  Paper: Observation
11.1.11 (§11.1), and `Babai.Observation_11_1_11_generators`. -/
theorem decGroup_rawLiftGens (hdom : dom.length = n) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    (hinv : Babai.IsInvariant (genGroup gens) (winSet n Δ))
    (gensH : List (Perm (Fin Δ.length)))
    (hH : genGroup gensH ≤ (winRestrictHom n Δ hnd hlt (genGroup gens) hinv).range) :
    decGroup n (rawLiftGens ((dom, gens.map (encPerm n)), (Δ, gensH.map (encPerm Δ.length))))
      = winPreimage n Δ hnd hlt (genGroup gens) hinv (genGroup gensH) := by
  set G := genGroup gens with hG
  set θ := winRestrictHom n Δ hnd hlt G hinv with hθ
  set H := genGroup gensH with hHdef
  -- a preimage of every generator of `H`
  have hkey : ∀ y ∈ gensH, ∃ (σ : Perm (Fin n)) (hσ : σ ∈ G),
      (rawPreimage ((dom, gens.map (encPerm n)), (Δ, encPerm Δ.length y))).getD (rawOne dom)
        = encPerm n σ ∧ θ ⟨σ, hσ⟩ = y := by
    intro y hy
    obtain ⟨⟨σ₀, hσ₀⟩, hσ₀y⟩ := hH (Subgroup.subset_closure hy)
    rcases hp : rawPreimage ((dom, gens.map (encPerm n)), (Δ, encPerm Δ.length y)) with _ | g
    · exact absurd hσ₀y (rawPreimage_eq_none hdom hnd hlt hinv hp σ₀ hσ₀)
    · obtain ⟨σ, hσ, hg, hres⟩ := rawPreimage_eq_some hdom hnd hlt hinv hp
      exact ⟨σ, hσ, hg, hres⟩
  -- the two halves of the answer
  set A : RawGens :=
    (gensH.map (encPerm Δ.length)).map
      (fun hh => (rawPreimage ((dom, gens.map (encPerm n)), (Δ, hh))).getD (rawOne dom))
    with hA
  have hsplit : rawLiftGens ((dom, gens.map (encPerm n)), (Δ, gensH.map (encPerm Δ.length)))
      = A ++ rawPointStab ((dom, gens.map (encPerm n)), Δ) := rfl
  have hstab : decGroup n (rawPointStab ((dom, gens.map (encPerm n)), Δ))
      = Babai.pointwiseStabilizer G (winSet n Δ) :=
    decGroup_rawPointStab dom hdom gens Δ hnd hlt
  have hAdec : ∀ z ∈ A.map (decPerm n), ∃ hz : z ∈ G, θ ⟨z, hz⟩ ∈ H := by
    intro z hz
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hz
    rw [hA] at hr
    obtain ⟨hh, hhh, rfl⟩ := List.mem_map.1 hr
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hhh
    obtain ⟨σ, hσ, heq, hres⟩ := hkey y hy
    rw [heq, decPerm_encPerm]
    exact ⟨hσ, by rw [hres]; exact Subgroup.subset_closure hy⟩
  rw [hsplit, decGroup_append]
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rw [decGroup, genGroup, Subgroup.closure_le]
      intro z hz
      obtain ⟨hzG, hmem⟩ := hAdec z hz
      exact (mem_winPreimage hnd hlt hinv H z).2 ⟨hzG, hmem⟩
    · rw [hstab]
      intro z hz
      obtain ⟨hzG, hzfix⟩ := hz
      refine (mem_winPreimage hnd hlt hinv H z).2 ⟨hzG, ?_⟩
      have : (⟨z, hzG⟩ : G) ∈ θ.ker :=
        (mem_ker_winRestrictHom hnd hlt hinv ⟨z, hzG⟩).2 hzfix
      rw [MonoidHom.mem_ker] at this
      rw [this]
      exact Subgroup.one_mem _
  · -- the other inclusion: Observation 11.1.11, generators plus the kernel
    set L := decGroup n A ⊔ decGroup n (rawPointStab ((dom, gens.map (encPerm n)), Δ)) with hL
    have hstabL : Babai.pointwiseStabilizer G (winSet n Δ) ≤ L := by
      rw [hL, ← hstab]; exact le_sup_right
    have hAleL : decGroup n A ≤ L := by rw [hL]; exact le_sup_left
    have hAL : ∀ (σ : Perm (Fin n)) (hσ : σ ∈ G) (y : Perm (Fin Δ.length)), y ∈ gensH →
        θ ⟨σ, hσ⟩ = y → σ ∈ L := by
      intro σ hσ y hy hres
      obtain ⟨σ', hσ', heq, hres'⟩ := hkey y hy
      have hin : σ' ∈ decGroup n A := by
        refine Subgroup.subset_closure ?_
        refine List.mem_map.2 ⟨(rawPreimage ((dom, gens.map (encPerm n)),
          (Δ, encPerm Δ.length y))).getD (rawOne dom), ?_, ?_⟩
        · exact List.mem_map.2 ⟨encPerm Δ.length y, List.mem_map.2 ⟨y, hy, rfl⟩, rfl⟩
        · rw [heq, decPerm_encPerm]
      have hker : (⟨σ * σ'⁻¹, G.mul_mem hσ (G.inv_mem hσ')⟩ : G) ∈ θ.ker := by
        rw [MonoidHom.mem_ker]
        have h1 : (⟨σ * σ'⁻¹, G.mul_mem hσ (G.inv_mem hσ')⟩ : G)
            = (⟨σ, hσ⟩ : G) * (⟨σ', hσ'⟩ : G)⁻¹ := rfl
        rw [h1, map_mul, map_inv, hres, hres', mul_inv_cancel]
      have hfix := (mem_ker_winRestrictHom hnd hlt hinv
        ⟨σ * σ'⁻¹, G.mul_mem hσ (G.inv_mem hσ')⟩).1 hker
      have hmem : σ * σ'⁻¹ ∈ L := hstabL ⟨G.mul_mem hσ (G.inv_mem hσ'), hfix⟩
      have hprod : σ * σ'⁻¹ * σ' ∈ L := Subgroup.mul_mem _ hmem (hAleL hin)
      simpa using hprod
    have himg : θ '' {s : G | θ s ∈ {y : Perm (Fin Δ.length) | y ∈ gensH}}
        = {y : Perm (Fin Δ.length) | y ∈ gensH} := by
      ext y
      constructor
      · rintro ⟨s, hs, rfl⟩; exact hs
      · intro hy
        obtain ⟨s, hs⟩ := hH (Subgroup.subset_closure hy)
        exact ⟨s, by show θ s ∈ {y : Perm (Fin Δ.length) | y ∈ gensH}; rw [hs]; exact hy, hs⟩
    have hcomap : Subgroup.comap θ H
        = Subgroup.closure ({s : G | θ s ∈ {y : Perm (Fin Δ.length) | y ∈ gensH}}
            ∪ (θ.ker : Set G)) :=
      Babai.comap_eq_closure_union_ker θ _ H (by rw [himg]; exact hHdef.symm)
    rw [winPreimage, ← hθ, hcomap, MonoidHom.map_closure, Subgroup.closure_le]
    rintro x ⟨s, hs, rfl⟩
    rcases hs with hs | hs
    · exact hAL (s : Perm (Fin n)) s.2 (θ s) hs (by rw [Subtype.coe_eta])
    · exact hstabL ⟨s.2, (mem_ker_winRestrictHom hnd hlt hinv s).1 hs⟩

/-- **The coset version of Observation 11.1.11.**  "and `Iso^Δ_G(x,y) = Aut^Δ_G(x)σ`": once a
preimage `σ` of a representative `τ` on the window is known, the answer on `Ω` is the preimage
of the answer on `Δ`.  The paper's right coset `Hτ` is `τ • H` here. -/
theorem winPreimage_smul (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    {G : Subgroup (Perm (Fin n))} (hinv : Babai.IsInvariant G (winSet n Δ))
    (H : Subgroup (Perm (Fin Δ.length))) {τ : Perm (Fin Δ.length)} {σ : Perm (Fin n)}
    (hσ : σ ∈ G) (hτ : winRestrictHom n Δ hnd hlt G hinv ⟨σ, hσ⟩ = τ) :
    {g : Perm (Fin n) | ∃ hg : g ∈ G,
        winRestrictHom n Δ hnd hlt G hinv ⟨g, hg⟩ ∈ τ • (H : Set (Perm (Fin Δ.length)))}
      = σ • (winPreimage n Δ hnd hlt G hinv H : Set (Perm (Fin n))) := by
  ext g
  rw [Babai.mem_perm_smul_set]
  constructor
  · rintro ⟨hg, hmem⟩
    rw [Babai.mem_perm_smul_set] at hmem
    refine (mem_winPreimage hnd hlt hinv H _).2 ⟨G.mul_mem (G.inv_mem hσ) hg, ?_⟩
    have h1 : (⟨σ⁻¹ * g, G.mul_mem (G.inv_mem hσ) hg⟩ : G)
        = (⟨σ, hσ⟩ : G)⁻¹ * (⟨g, hg⟩ : G) := rfl
    rw [h1, map_mul, map_inv, hτ]
    exact hmem
  · intro hmem
    obtain ⟨hgG, hmem'⟩ := (mem_winPreimage hnd hlt hinv H _).1 hmem
    have hg : g ∈ G := by
      have : σ * (σ⁻¹ * g) ∈ G := G.mul_mem hσ hgG
      simpa using this
    refine ⟨hg, ?_⟩
    rw [Babai.mem_perm_smul_set]
    have h1 : (⟨σ⁻¹ * g, hgG⟩ : G) = (⟨σ, hσ⟩ : G)⁻¹ * (⟨g, hg⟩ : G) := rfl
    rw [h1, map_mul, map_inv, hτ] at hmem'
    exact hmem'

end Lift

theorem polyFun_rawLiftGens : PolyFun rawLiftGens := by
  have hf : PolyFun (fun z : ((List ℕ × List RawPerm) × List ℕ) × RawPerm =>
      (rawPreimage ((z.1.1, (z.1.2, z.2)) : (List ℕ × List RawPerm) × (List ℕ × RawPerm))).getD
        (rawOne z.1.1.1)) := by
    have hpre : PolyFun (fun z : ((List ℕ × List RawPerm) × List ℕ) × RawPerm =>
        rawPreimage ((z.1.1, (z.1.2, z.2)) :
          (List ℕ × List RawPerm) × (List ℕ × RawPerm))) :=
      ((polyFun_fst.comp polyFun_fst).pair
        ((polyFun_fst.comp polyFun_snd).pair polyFun_snd)).comp polyFun_rawPreimage
    exact (hpre.pair (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp
      polyFun_rawOne)).comp polyFun_optionGetD
  have hmap : PolyFun (fun p : (List ℕ × List RawPerm) × (List ℕ × List RawPerm) =>
      p.2.2.map (fun hh => (rawPreimage (p.1, (p.2.1, hh))).getD (rawOne p.1.1))) :=
    ((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).pair
      (polyFun_snd.comp polyFun_snd)).comp (PolyFun.mapParam hf)
  have hstab : PolyFun (fun p : (List ℕ × List RawPerm) × (List ℕ × List RawPerm) =>
      rawPointStab (p.1, p.2.1)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp polyFun_rawPointStab
  exact ((hmap.pair hstab).comp polyFun_append).of_eq (fun _ => rfl)

end Algo
