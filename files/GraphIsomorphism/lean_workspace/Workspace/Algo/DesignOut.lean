/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the objects Procedure "Design Lemma" returns (§8.2, lines 05 and 08).
-/
import Workspace.Algo.DesignScan

/-!
# §8.2 Procedure "Design Lemma" — reading off the outcome

Lines 05 and 08 of the procedure do not return the string `x⃗`: they return

```
05 then return the vertex-coloring, exit           (: goal (i) achieved :)
08     return X* := (X_x⃗)^{(2)}, exit              (: goal (ii) achieved :)
```

Both objects are functions of `x⃗` and of the table of line 01, and `Workspace/Algo/DesignRaw.lean`
already computes them at a string: the vertex coloring of the restriction is `Algo.restrVColors`,
the dominant class `C(x⃗)` of line 06 is `Algo.dominantList`, and the number of colors the
`2`-skeleton realizes on it — the rank of `X*[C(x⃗)]`, which line 07 compares with `2` — is
`Algo.cliqueRank`.  This file reads those three off at the string the procedure returns and
proves that the answer is **polynomially small**, so that the whole of §8.2 is a
`RAM.QuasiPolyFun` and not merely a `RAM.QuasiFun`: the pattern of
`Algo.sizeBound_guardedVertexColoring` (A8).  This is what risk R-A9-5 asked for.

The `2`-skeleton itself, as a table of pair colors, is *not* returned: it has `n²` entries and
is read at a pair by `Algo.restrPairColorAt`, a `RAM.PolyFun` of the table and the pair.  What
Sec. 9 consumes of it is its rank on `C(x⃗)`, which is returned.

## Main definitions

* `Algo.designAt` — the input of the tests at the returned string;
* `Algo.designOutRaw` — the three objects at a string;
* `Algo.designOutcome` — the whole procedure with its outcome.

## Main results

* `Algo.designOutcome_spec` — what the three components are, in the language of §8;
* `Algo.sizeBound_designOutcome`, `Algo.quasiPolyFun_designOutcome` — the answer is
  polynomially small, and the procedure is a `RAM.QuasiPolyFun`.

No axiom and no `sorry`.
-/

open scoped Classical

namespace Algo

open Babai RAM

/-! ## The read-off -/

/-- The input of the tests of lines 04–08 at a string, with the table of line 01. -/
def designAt (c₀ : ℕ) (g : GIn) (xs : List ℕ) : DIn :=
  (((g.1.1.1, xs), guardedPipeline321 c₀ g.1), g.2)

/-- The objects lines 05 and 08 return, at a string: the vertex coloring of `X_x⃗` over the
vertex list (goal (i)), the dominant class `C(x⃗)`, and the rank of the `2`-skeleton on it
(goal (ii)). -/
def designOutRaw (z : DIn) : List ℕ × (List ℕ × ℕ) :=
  (restrVColors z, (dominantList z, cliqueRank z))

/-- **Procedure "Design Lemma" with its outcome.**  Lines 01–08: refine, scan, and return the
objects of lines 05 and 08 at the string found. -/
def designOutcome (c₀ : ℕ) (g : GIn) : Option (List ℕ × (List ℕ × ℕ)) :=
  (designProcedure c₀ g).elim none
    (fun xs => some (designOutRaw (designAt c₀ g xs)))

theorem designOutcome_of_some {c₀ : ℕ} {g : GIn} {xs : List ℕ}
    (hs : designProcedure c₀ g = some xs) :
    designOutcome c₀ g = some (designOutRaw (designAt c₀ g xs)) := by
  rw [designOutcome, hs]; rfl

theorem designOutcome_of_none {c₀ : ℕ} {g : GIn} (hs : designProcedure c₀ g = none) :
    designOutcome c₀ g = none := by
  rw [designOutcome, hs]; rfl

theorem designOutcome_eq_none_iff {c₀ : ℕ} {g : GIn} :
    designOutcome c₀ g = none ↔ designProcedure c₀ g = none := by
  cases hs : designProcedure c₀ g with
  | none => exact ⟨fun _ => rfl, fun _ => designOutcome_of_none hs⟩
  | some xs =>
      rw [designOutcome_of_some hs]
      exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp)⟩

/-! ## What the outcome is -/

section Spec

variable {n k a b c₀ : ℕ} {ks dom : List ℕ}

/-- **Lines 05 and 08.**  The procedure returns the objects of Theorem 8.1.5 at a string `x⃗` of
distinct vertices of least returning length `ℓ ≤ k − 1`: the vertex coloring of `X_x⃗` over the
vertex list, the dominant class `C(x⃗)`, and the rank of the `2`-skeleton `(X_x⃗)^{(2)}` induced
on `C(x⃗)` (the number line 07 compares with `2`). -/
theorem designOutcome_spec {α : ℝ} {rels : RawRelStruct} (hnd : dom.Nodup)
    (hmem : ∀ c, c ∈ dom ↔ c < n) (hk : ks.length = k) (hb : 0 < b)
    (hab : α = (a : ℝ) / (b : ℝ)) (hg : ks.length ≤ guardBound c₀ dom.length)
    {w : List ℕ × (List ℕ × ℕ)}
    (hs : designOutcome c₀ (((ks, dom), rels), (a, b)) = some w) :
    ∃ (xs : List ℕ) (l : ℕ) (hl : l < k) (x : Str (Fin n) l),
      tupleOf x = xs ∧ w = designOutRaw (designAt c₀ (((ks, dom), rels), (a, b)) xs) ∧
      Babai.KAryPartStruct.Returns α (decRel n k rels).F1.F2.F3 hl.le x ∧
      (∀ (l' : ℕ) (_ : l' < l), ∀ y : Str (Fin n) l',
        ¬ Babai.KAryPartStruct.Returns α (decRel n k rels).F1.F2.F3
            (by omega : l' ≤ k) y) ∧
      (∀ u : Fin n, restrVColorAt (designAt c₀ (((ks, dom), rels), (a, b)) xs, (u : ℕ))
        = ((decWL n k (guardedPipeline321 c₀ ((ks, dom), rels))).restrTo hl.le x).vcolor u) ∧
      (∀ u : Fin n, (u : ℕ) ∈ w.2.1 ↔ u ∈ Babai.KAryPartStruct.dominantClass α
        ((decWL n k (guardedPipeline321 c₀ ((ks, dom), rels))).restrTo hl.le x)) ∧
      (∀ _ : l + 2 ≤ k, w.2.2 =
        ((((decWL n k (guardedPipeline321 c₀ ((ks, dom), rels))).restrTo hl.le x).skel2
            (by omega)).induced
          (Babai.KAryPartStruct.dominantClass α
            ((decWL n k (guardedPipeline321 c₀ ((ks, dom), rels))).restrTo hl.le x))).rank) := by
  classical
  have hwf : RawWL.WF n k (guardedPipeline321 c₀ ((ks, dom), rels)) :=
    wf_line01 (rels := rels) hnd hmem hk hg
  cases hp : designProcedure c₀ (((ks, dom), rels), (a, b)) with
  | none => rw [designOutcome_of_none hp] at hs; exact absurd hs (by simp)
  | some xs =>
      obtain ⟨l, hl, x, hx, hret, hmin⟩ :=
        designProcedure_some (n := n) (rels := rels) hnd hmem hk hb hab hg hp
      have hw : w = designOutRaw (designAt c₀ (((ks, dom), rels), (a, b)) xs) := by
        rw [designOutcome_of_some hp] at hs
        exact (Option.some.inj hs).symm
      have hz : designAt c₀ (((ks, dom), rels), (a, b)) xs
          = (((ks, tupleOf x), guardedPipeline321 c₀ ((ks, dom), rels)), (a, b)) := by
        rw [designAt, hx]
      refine ⟨xs, l, hl, x, hx, hw, hret, hmin, ?_, ?_, ?_⟩
      · intro u
        rw [hz]
        exact restrVColorAt_spec hk hl.le x u
      · intro u
        rw [hw]
        show (u : ℕ) ∈ dominantList (designAt c₀ (((ks, dom), rels), (a, b)) xs) ↔ _
        rw [hz]
        exact mem_dominantList hwf hk hl.le x hb hab u
      · intro h2
        rw [hw]
        show cliqueRank (designAt c₀ (((ks, dom), rels), (a, b)) xs) = _
        rw [hz]
        exact cliqueRank_spec hwf hk hl.le h2 x hb hab

end Spec

/-! ## The cost -/

theorem polyFun_designOutRaw : PolyFun designOutRaw :=
  polyFun_restrVColors.pair (polyFun_dominantList.pair polyFun_cliqueRank)

theorem quasiFun_designOutcome (c₀ : ℕ) : QuasiFun (designOutcome c₀) := by
  have hz : QuasiFun (fun g : GIn => designAt c₀ g []) :=
    (((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).pair
      (polyFun_const ([] : List ℕ))).quasiFun.pair
      (polyFun_fst.comp_quasiFun (quasiFun_guardedPipeline321 c₀))).pair polyFun_snd.quasiFun)
  have hpair : QuasiFun (fun g : GIn => ((designProcedure c₀ g, designAt c₀ g []) :
      Option (List ℕ) × DIn)) :=
    (hz.comp (quasiFun_rawDesignScan c₀)).pair hz
  have hh : QuasiFun (fun q : List ℕ × DIn =>
      (some (designOutRaw (withStr (q.2, q.1))) : Option (List ℕ × (List ℕ × ℕ)))) :=
    ((polyFun_snd.pair polyFun_fst).comp polyFun_withStr |>.comp polyFun_designOutRaw
      |>.comp polyFun_some).quasiFun
  refine (hpair.comp (QuasiFun.optionElim (quasiFun_const none) hh)).of_eq (fun g => ?_)
  cases hs : designProcedure c₀ g with
  | none => rw [designOutcome_of_none hs]; simp [hs]
  | some xs =>
      rw [designOutcome_of_some hs]
      simp only [hs]
      rfl

/-! ### The answer is polynomially small

The colors are ranks of the refined table, hence below the number of its rows, which is `n^k`
with `k` below the guard (`Algo.col_guardedPipeline_le`); the dominant class is a sublist of the
vertex list; the rank is at most the square of its length. -/

theorem length_pairColors (z : DIn) :
    (pairColors z).length = (dominantList z).length * (dominantList z).length := by
  rw [pairColors, List.length_flatten, List.map_map]
  have hc : (List.length ∘ fun u => (dominantList z).map
      fun v => restrPairColorAt (z, (u, v)))
      = fun _ : ℕ => (dominantList z).length := by
    funext u; simp
  rw [hc, List.map_const', List.sum_replicate, smul_eq_mul]

theorem cliqueRank_le (z : DIn) :
    cliqueRank z ≤ (dominantList z).length * (dominantList z).length := by
  rw [cliqueRank, length_dedupG_eq_card, ← length_pairColors]
  exact List.toFinset_card_le _

theorem length_dominantList_le (z : DIn) : (dominantList z).length ≤ z.1.2.1.length :=
  List.length_filter_le _ _

/-- The polynomial bound on the size of the answer. -/
def outSizeBound (c₀ N : ℕ) : ℕ :=
  2 * (1 + N * (2 * ((Nat.log 2 N + 2) ^ (c₀ + 1) + 3) + 1))
    + 2 * (2 * (1 + N * (2 * N + 1)) + 2 * (2 * N + 2))

theorem polyBound_outSizeBound (c₀ : ℕ) : PolyBound (outSizeBound c₀) := by
  have h1 : PolyBound (fun N : ℕ => 1 + N * (2 * ((Nat.log 2 N + 2) ^ (c₀ + 1) + 3) + 1)) :=
    (polyBound_const 1).add (polyBound_id.mul
      (((polyBound_const 2).mul ((polyBound_logPow (c₀ + 1)).add (polyBound_const 3))).add
        (polyBound_const 1)))
  have h2 : PolyBound (fun N : ℕ => 1 + N * (2 * N + 1)) :=
    (polyBound_const 1).add (polyBound_id.mul
      (((polyBound_const 2).mul polyBound_id).add (polyBound_const 1)))
  exact ((polyBound_const 2).mul h1).add ((polyBound_const 2).mul
    (((polyBound_const 2).mul h2).add ((polyBound_const 2).mul
      (((polyBound_const 2).mul polyBound_id).add (polyBound_const 2)))))

/-- **The answer of the whole procedure is polynomially small.** -/
theorem sizeBound_designOutcome (c₀ : ℕ) : SizeBound (designOutcome c₀) := by
  classical
  have hbound : ∀ g : GIn, Enc.size (designOutcome c₀ g) ≤ outSizeBound c₀ (Enc.size g) + 2 := by
    intro g
    set N := Enc.size g with hN
    set m := (Nat.log 2 N + 2) ^ (c₀ + 1) with hm
    cases hs : designProcedure c₀ g with
    | none => rw [designOutcome_of_none hs, size_none]; omega
    | some xs =>
        rw [designOutcome_of_some hs, size_some_eq]
        set z : DIn := designAt c₀ g xs with hz
        have hgN : Enc.size g.1 ≤ N := size_fst_le' g
        have hdom : z.1.2.1 = g.1.1.2 := by
          rw [hz, designAt]; exact fst_guardedPipeline321 c₀ g.1
        have hdomN : Enc.size z.1.2.1 ≤ N := by
          rw [hdom]
          exact le_trans (size_snd_le' g.1.1) (le_trans (size_fst_le' g.1) hgN)
        have hnN : z.1.2.1.length ≤ N := le_trans (length_le_size _) hdomN
        -- the colors
        have hcolval : ∀ c ∈ restrVColors z, Enc.size c ≤ m + 3 := by
          intro c hc
          obtain ⟨u, -, rfl⟩ := List.mem_map.1 hc
          have hle : restrVColorAt (z, u) ≤ 2 ^ m := by
            refine le_trans (tblGet_le (B := 2 ^ ((Nat.log 2 (Enc.size g.1.1) + 2) ^ (c₀ + 1)))
              _ _ (col_guardedPipeline321_le c₀ g.1)) ?_
            have hg1 : Enc.size g.1.1 ≤ N := le_trans (size_fst_le' g.1) hgN
            exact Nat.pow_le_pow_right (by norm_num)
              (Nat.pow_le_pow_left (by
                have := Nat.log_mono_right (b := 2) hg1
                omega) _)
          have hsize : Nat.size (restrVColorAt (z, u)) ≤ m + 1 :=
            Nat.size_le.2 (lt_of_le_of_lt hle
              (Nat.pow_lt_pow_right (by norm_num) (by omega)))
          have hEnc : Enc.size (restrVColorAt (z, u)) = Nat.size (restrVColorAt (z, u)) + 2 :=
            Small.size_nat _
          omega
        have hcols : Enc.size (restrVColors z) ≤ 1 + N * (2 * (m + 3) + 1) := by
          have h := size_list_le_of_entries (restrVColors z) (m + 3) hcolval
          have hlen : (restrVColors z).length ≤ N := by
            rw [restrVColors, List.length_map]; exact hnN
          have := Nat.mul_le_mul_right (2 * (m + 3) + 1) hlen
          omega
        -- the dominant class
        have hclsval : ∀ c ∈ dominantList z, Enc.size c ≤ N := by
          intro c hc
          exact le_trans (size_mem_le (List.mem_filter.1 hc).1) hdomN
        have hcls : Enc.size (dominantList z) ≤ 1 + N * (2 * N + 1) := by
          have h := size_list_le_of_entries (dominantList z) N hclsval
          have hlen : (dominantList z).length ≤ N :=
            le_trans (length_dominantList_le z) hnN
          have := Nat.mul_le_mul_right (2 * N + 1) hlen
          omega
        -- the rank
        have hrank : Enc.size (cliqueRank z) ≤ 2 * N + 2 := by
          have hle : cliqueRank z ≤ N * N :=
            le_trans (cliqueRank_le z)
              (Nat.mul_le_mul (le_trans (length_dominantList_le z) hnN)
                (le_trans (length_dominantList_le z) hnN))
          have hlt : N * N < 2 ^ (2 * N) := by
            have h1 : N < 2 ^ N := Nat.lt_two_pow_self
            calc N * N < 2 ^ N * 2 ^ N := Nat.mul_lt_mul'' h1 h1
              _ = 2 ^ (2 * N) := by rw [← pow_add, two_mul]
          have hsize : Nat.size (cliqueRank z) ≤ 2 * N :=
            Nat.size_le.2 (lt_of_le_of_lt hle hlt)
          have hEnc : Enc.size (cliqueRank z) = Nat.size (cliqueRank z) + 2 := Small.size_nat _
          omega
        have hp2 : Enc.size ((dominantList z, cliqueRank z) : List ℕ × ℕ)
            ≤ 2 * Enc.size (dominantList z) + 2 * Enc.size (cliqueRank z) := size_pair_le' _
        have hp1 : Enc.size (designOutRaw z)
            ≤ 2 * Enc.size (restrVColors z)
              + 2 * Enc.size ((dominantList z, cliqueRank z) : List ℕ × ℕ) := size_pair_le' _
        rw [outSizeBound, ← hm]
        omega
  obtain ⟨c, d, hc⟩ := polyBound_outSizeBound c₀
  refine ⟨c + 2, d, fun g => le_trans (hbound g) ?_⟩
  have h := hc (Enc.size g)
  have h1 : 1 ≤ (Enc.size g + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have hexp : (c + 2) * (Enc.size g + 1) ^ d
      = c * (Enc.size g + 1) ^ d + 2 * (Enc.size g + 1) ^ d := by ring
  omega

/-- **The whole of Procedure "Design Lemma" is a `RAM.QuasiPolyFun`.**  Lines 01–08 with the
arity in the input and guarded by `k ≤ (log₂ n + 1)^{c₀}`: quasipolynomial time, polynomially
small answer.  This is the form in which Sec. 9 calls the Design Lemma. -/
theorem quasiPolyFun_designOutcome (c₀ : ℕ) : QuasiPolyFun (designOutcome c₀) :=
  (quasiFun_designOutcome c₀).quasiPolyFun (sizeBound_designOutcome c₀)

end Algo
