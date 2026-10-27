/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align (§14.1), line 1 — the isomorphism test for two
Johnson schemes, on the unit-cost RAM.
-/
import Workspace.Algo.AlignJohnsonIso

/-!
# §14.1, Procedure Align, line 1 for Johnson schemes

> 1. If `X(x)` and `X(y)` are not `G^ϕ`-isomorphic then reject isomorphism, exit.

and (§14.1) *"This is trivial in linear time for colored equipartitions, and polynomial time
for Johnson schemes."*

**The test** is `Algo.alignJTest`: the two headers agree, `m*(x) = m*(y)` and
`t*(x) = t*(y)`.  Nothing else has to be compared.  The size `|W|` of the class that carries
the scheme is *not* a separate condition: well-formedness already forces
`|W| = C(m*, t*)`, so equal parameters give equal `|W|`.

**The test is complete** — equal parameters give an isomorphism, namely `Algo.alignJPerm`
(`Workspace/Algo/AlignJohnsonIso.lean`) — and **sound**, which is the content of this file:
the parameters of a Johnson scheme are determined by the decoded structure.  The route is

1. an isomorphism preserves the vertex coloring, so it carries `W` onto `W'`, and therefore
   `C(m*, t*) = |W| = |W'| = C(m'*, t'*)`;
2. `t*` is the **largest** value of the pair coloring on `W × W`.  It is a bound because
   `|S ∖ T| ≤ |S| = t*`, and it is attained because `m* ≥ 2t*` gives two disjoint
   `t*`-subsets, and `Algo.RawJohnson.WF.rowBinom_bijective` says that both are rows;
3. so `t* = t'*`; and `C(·, t*)` is strictly increasing above `t*`, so `|W| = C(m*, t*)`
   determines `m*`.

## Main definitions

* `Algo.alignJTest` — **line 1** for Johnson schemes.

## Main results

* `Algo.alignJ_params_of_smul` — **the parameters are an isomorphism invariant**;
* `Algo.alignJTest_eq_false_structIso` — a failed test means `Iso_K(X(x), X(y)) = ∅` for
  **every** `K ⊆ S(Γ)`, in particular for `K = G^ϕ`;
* `Algo.alignJTest_iff` — the test answers `true` exactly when an isomorphism exists;
* `Algo.polyFun_alignJTest` — **the running time**.

No axiom, no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

/-! ## Binomial coefficients are strictly increasing in the top index -/

/-- `C(·, k)` is strictly increasing on `[k, ∞)` for `k ≥ 1`. -/
theorem alignJ_choose_lt {k : ℕ} (hk : 1 ≤ k) :
    ∀ {a b : ℕ}, k ≤ a → a < b → a.choose k < b.choose k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  intro a b hka hab
  induction b with
  | zero => omega
  | succ n ih =>
    have hjn : j ≤ n := by omega
    have hstep : n.choose (j + 1) < (n + 1).choose (j + 1) := by
      have hp := Nat.choose_pos hjn
      have he : (n + 1).choose (j + 1) = n.choose j + n.choose (j + 1) := by
        simp [Nat.choose_succ_succ]
      omega
    rcases Nat.lt_or_ge a n with hlt | hge
    · exact lt_trans (ih hlt) hstep
    · have : a = n := by omega
      subst this
      exact hstep

/-- `C(·, k)` is injective on `[k, ∞)` for `k ≥ 1`. -/
theorem alignJ_choose_inj {k a b : ℕ} (hk : 1 ≤ k) (hka : k ≤ a) (hkb : k ≤ b)
    (h : a.choose k = b.choose k) : a = b := by
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (alignJ_choose_lt hk hka hlt))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (alignJ_choose_lt hk hkb hgt))

/-! ## `t*` is the largest pair color on `W` -/

section Params

variable {m ms ts : ℕ} {r : RawJohnson}

/-- The Johnson color `|S ∖ T|` never exceeds `t*`. -/
theorem alignJ_ecol_le (h : RawJohnson.WF m ms ts r) {u v : Fin m} (hu : (u : ℕ) ∈ r.1)
    (hv : (v : ℕ) ∈ r.1) : (decJohnson m r).ecol u v ≤ ts := by
  rw [decJohnson_ecol_mem m r hu hv, rawJDiff]
  calc ((rawJRow (r, (u : ℕ))).filter
          (fun a => !decide (a ∈ rawJRow (r, (v : ℕ))))).length
      ≤ (rawJRow (r, (u : ℕ))).length := List.length_filter_le _ _
    _ = ts := h.rowLen _ (h.rawJRow_mem hu)

/-- Two disjoint `t*`-subsets exist, because `m* ≥ 2t*`; both are rows, so `t*` **is
attained** as a pair color on `W`. -/
theorem alignJ_exists_ecol_eq (h : RawJohnson.WF m ms ts r) :
    ∃ u v : Fin m, (u : ℕ) ∈ r.1 ∧ (v : ℕ) ∈ r.1 ∧ (decJohnson m r).ecol u v = ts := by
  classical
  have hms : ts ≤ (Finset.univ : Finset (Fin ms)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    have := h.params; omega
  obtain ⟨S, -, hScard⟩ := Finset.exists_subset_card_eq hms
  have hms2 : ts ≤ ((Finset.univ : Finset (Fin ms)) \ S).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, hScard]
    have := h.params; omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hms2
  obtain ⟨u, hu⟩ := h.toBinom_bijective.2 (⟨S, hScard⟩ : Babai.binom (Fin ms) ts)
  obtain ⟨v, hv⟩ := h.toBinom_bijective.2 (⟨T, hTcard⟩ : Babai.binom (Fin ms) ts)
  have hSu : rawJSet ms (rawJRow (r, ((u : Fin m) : ℕ))) = S := congrArg Subtype.val hu
  have hTv : rawJSet ms (rawJRow (r, ((v : Fin m) : ℕ))) = T := congrArg Subtype.val hv
  refine ⟨(u : Fin m), (v : Fin m), u.2, v.2, ?_⟩
  rw [decJohnson_ecol_mem m r u.2 v.2,
    rawJDiff_eq_card (ms := ms) (h.rowNodup (h.rawJRow_mem u.2)) (h.rowLt _ (h.rawJRow_mem u.2)),
    hSu, hTv]
  have hdisj : S \ T = S := by
    refine Finset.sdiff_eq_self_of_disjoint ?_
    refine Finset.disjoint_left.2 (fun a haS haT => ?_)
    exact (Finset.mem_sdiff.1 (hTsub haT)).2 haS
  rw [hdisj, hScard]

end Params

/-! ## The parameters are an isomorphism invariant -/

section Invariance

variable {m ms ts ms' ts' : ℕ} {r r' : RawJohnson}

private theorem alignJT_ite_eq {p q : Prop} [Decidable p] [Decidable q]
    (h : (if p then (1 : ℕ) else 0) = (if q then (1 : ℕ) else 0)) : p ↔ q := by
  split_ifs at h <;> simp_all

/-- §14.1, line 1.  **The parameters of a Johnson scheme are determined by the decoded
structure.** -/
theorem alignJ_params_of_smul (h : RawJohnson.WF m ms ts r) (h' : RawJohnson.WF m ms' ts' r')
    {f : Perm (Fin m)} (hf : f • decJohnson m r = decJohnson m r') :
    ms = ms' ∧ ts = ts' ∧ r.1.length = r'.1.length := by
  classical
  have hinvself : ∀ u : Fin m, f⁻¹ (f u) = u := fun u => Equiv.symm_apply_apply f u
  have hselfinv : ∀ u : Fin m, f (f⁻¹ u) = u := fun u => Equiv.apply_symm_apply f u
  -- the vertex coloring carries `W` onto `W'`
  have hvcol : ∀ u : Fin m, ((f u : Fin m) : ℕ) ∈ r'.1 ↔ (u : ℕ) ∈ r.1 := by
    intro u
    have hx : (decJohnson m r).vcol (f⁻¹ (f u)) = (decJohnson m r').vcol (f u) :=
      congrArg (fun X : Babai.ColStruct (Fin m) ℕ => X.vcol (f u)) hf
    rw [hinvself u] at hx
    exact alignJT_ite_eq hx.symm
  have hecol : ∀ u v : Fin m,
      (decJohnson m r').ecol (f u) (f v) = (decJohnson m r).ecol u v := by
    intro u v
    have hx : (decJohnson m r).ecol (f⁻¹ (f u)) (f⁻¹ (f v))
        = (decJohnson m r').ecol (f u) (f v) :=
      congrArg (fun X : Babai.ColStruct (Fin m) ℕ => X.ecol (f u) (f v)) hf
    rw [hinvself u, hinvself v] at hx
    exact hx.symm
  -- `|W| = |W'|`
  have hcard : r.1.length = r'.1.length := by
    have h1 : (rawJSet m r.1).card = r.1.length := card_rawJSet h.wNodup h.wLt
    have h2 : (rawJSet m r'.1).card = r'.1.length := card_rawJSet h'.wNodup h'.wLt
    rw [← h1, ← h2]
    refine Finset.card_bij' (fun u _ => f u) (fun u _ => f⁻¹ u) ?_ ?_ ?_ ?_
    · intro u hu
      exact mem_rawJSet.2 ((hvcol u).2 (mem_rawJSet.1 hu))
    · intro u hu
      refine mem_rawJSet.2 ?_
      have hk := (hvcol (f⁻¹ u)).1
      rw [hselfinv u] at hk
      exact hk (mem_rawJSet.1 hu)
    · intro u _; exact hinvself u
    · intro u _; exact hselfinv u
  -- `t* = t'*`: both are the largest pair color on the carrier
  have hts : ts = ts' := by
    obtain ⟨u, v, hu, hv, huv⟩ := alignJ_exists_ecol_eq h
    obtain ⟨u', v', hu', hv', huv'⟩ := alignJ_exists_ecol_eq h'
    have hle1 : ts ≤ ts' := by
      rw [← huv, ← hecol u v]
      exact alignJ_ecol_le h' ((hvcol u).2 hu) ((hvcol v).2 hv)
    have hle2 : ts' ≤ ts := by
      have hiu : ((f⁻¹ u' : Fin m) : ℕ) ∈ r.1 := by
        have hk := (hvcol (f⁻¹ u')).1
        rw [hselfinv u'] at hk
        exact hk hu'
      have hiv : ((f⁻¹ v' : Fin m) : ℕ) ∈ r.1 := by
        have hk := (hvcol (f⁻¹ v')).1
        rw [hselfinv v'] at hk
        exact hk hv'
      have hk := hecol (f⁻¹ u') (f⁻¹ v')
      rw [hselfinv u', hselfinv v', huv'] at hk
      rw [hk]
      exact alignJ_ecol_le h hiu hiv
    omega
  subst hts
  refine ⟨?_, rfl, hcard⟩
  -- `C(·, t*)` determines `m*`
  have hchoose : ms.choose ts = ms'.choose ts := by
    have e1 : r.2.2.length = ms.choose ts := h.card
    have e2 : r'.2.2.length = ms'.choose ts := h'.card
    rw [← e1, ← e2, h.rowsLen, h'.rowsLen, hcard]
  exact alignJ_choose_inj (by have := h.two_le; omega)
    (by have := h.two_le; have := h.params; omega)
    (by have := h'.two_le; have := h'.params; omega) hchoose

end Invariance

/-! ## The test -/

/-- §14.1, **line 1** for Johnson schemes: the two headers agree.  The parameter `t*` is the
stored header, and `m*` is `Algo.rawJDeg`, read off the rows. -/
def alignJTest (p : RawJohnson × RawJohnson) : Bool :=
  decide (rawJDeg p.1 = rawJDeg p.2) && decide (p.1.2.1 = p.2.2.1)

theorem alignJTest_eq_true_iff (r r' : RawJohnson) :
    alignJTest (r, r') = true ↔ rawJDeg r = rawJDeg r' ∧ r.2.1 = r'.2.1 := by
  simp [alignJTest]

section Spec

variable {m : ℕ} {r r' : RawJohnson}

/-- §14.1, **line 1**, the reject exit for Johnson schemes: when the test fails there is no
isomorphism at all, in any subset `K` of `S(Γ)` — in particular none in `G^ϕ`. -/
theorem alignJTest_eq_false_structIso (h : RawJohnson.WF m (rawJDeg r) r.2.1 r)
    (h' : RawJohnson.WF m (rawJDeg r') r'.2.1 r') (hfail : alignJTest (r, r') = false)
    (K : Set (Perm (Fin m))) :
    Babai.structIso K (decJohnson m r) (decJohnson m r') = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro f ⟨-, hf⟩
  obtain ⟨h1, h2, -⟩ := alignJ_params_of_smul h h' hf
  rw [← Bool.not_eq_true, alignJTest_eq_true_iff] at hfail
  exact hfail ⟨h1, h2⟩

/-- §14.1, **line 1** for Johnson schemes: the test answers `true` **exactly when** an
isomorphism exists. -/
theorem alignJTest_iff (h : RawJohnson.WF m (rawJDeg r) r.2.1 r)
    (h' : RawJohnson.WF m (rawJDeg r') r'.2.1 r') :
    alignJTest (r, r') = true ↔
      ∃ f : Perm (Fin m), f • decJohnson m r = decJohnson m r' := by
  constructor
  · intro htest
    obtain ⟨h1, h2⟩ := (alignJTest_eq_true_iff r r').1 htest
    have h'' : RawJohnson.WF m (rawJDeg r) r.2.1 r' := by rw [h1, h2]; exact h'
    have hd : (List.range m).length = m := List.length_range
    exact ⟨decPerm m (alignJPerm (List.range m, (r, r'))), alignJPerm_smul hd h h''⟩
  · rintro ⟨f, hf⟩
    obtain ⟨h1, h2, -⟩ := alignJ_params_of_smul h h' hf
    exact (alignJTest_eq_true_iff r r').2 ⟨h1, h2⟩

/-- §14.1, **line 1 / line 2 (i)**: when the test succeeds the second scheme is well formed
for the parameters of the first, which is what `Algo.alignJPerm` needs. -/
theorem alignJTest_wf_right (h' : RawJohnson.WF m (rawJDeg r') r'.2.1 r')
    (htest : alignJTest (r, r') = true) :
    RawJohnson.WF m (rawJDeg r) r.2.1 r' := by
  obtain ⟨h1, h2⟩ := (alignJTest_eq_true_iff r r').1 htest
  rw [h1, h2]; exact h'

end Spec

/-! ## The running time -/

/-- §14.1, **line 1** for Johnson schemes **runs in polynomial time**. -/
theorem polyFun_alignJTest : PolyFun alignJTest := by
  have hms : PolyFun (fun p : RawJohnson × RawJohnson =>
      decide (rawJDeg p.1 = rawJDeg p.2)) :=
    (((polyFun_fst.comp polyFun_rawJDeg)).pair
      ((polyFun_snd.comp polyFun_rawJDeg))).comp polyFun_natEq
  have hts : PolyFun (fun p : RawJohnson × RawJohnson => decide (p.1.2.1 = p.2.2.1)) :=
    ((((polyFun_fst.comp polyFun_snd)).comp polyFun_fst).pair
      (((polyFun_snd.comp polyFun_snd)).comp polyFun_fst)).comp polyFun_natEq
  exact polyFun_rawJAnd hms hts

end Algo
