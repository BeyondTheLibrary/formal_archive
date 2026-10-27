import Workspace.Machine.IterateInv
import Workspace.Machine.ListOps4

/-!
# `QuasiFun`: quasipolynomial time with a quasipolynomially large answer

`RAM.QuasiPolyFun` (`Workspace/Machine/PolyFun.lean`) asks for quasipolynomial time **and** a
*polynomial* bound on the size of the answer.  That pair of demands is right for the final
obligation `RAM.SIWorkspaceRoutine`, whose answer is a list of generators, and for the bridge
`RAM.QuasiPolyFun.quasiPolyTime`, which copies the answer out.  It is wrong for the paper's
procedures with `k = O(log n)`: the table of all `k`-tuples has about `k · n^k = 2^{O(log² n)}`
entries, so a routine that returns it is in quasipolynomial time but its answer is not
polynomially large.

This file adds the class for those routines:

`RAM.QuasiFun f` : `f` is computed by a clean quasipolynomial-time routine at the workspace
convention with sixteen work registers, and the encoding of `f a` is *quasipolynomially* bounded
in the encoding of `a`.

The class is closed under everything `RAM.QuasiPolyFun` is closed under, and for the same
reasons, with `RAM.QuasiPolyBound.comp` ("a quasipolynomial of a quasipolynomial is
quasipolynomial") doing the work that `RAM.QuasiPolyBound.comp_poly` does there.  The two
classes meet again in `RAM.QuasiFun.quasiPolyFun`: as soon as the answer is polynomially small,
a `QuasiFun` is a `QuasiPolyFun`.  **Return to `QuasiPolyFun` at the first opportunity**: nothing
above the machine layer accepts a `QuasiFun`.

## Main definitions

* `RAM.QuasiSizeBound`, `RAM.QuasiFun`.

## Main results

* `RAM.PolyFun.quasiFun`, `RAM.QuasiPolyFun.quasiFun`, `RAM.QuasiFun.quasiPolyFun`;
* `RAM.QuasiFun.comp`, `.pair`, `.of_eq`, `.optionElim`, `.listCases`, `.ite`;
* `RAM.QuasiFun.iterateSetup`: iteration whose *state* is quasipolynomially large.

No axiom and no `sorry`.
-/

namespace RAM

variable {α β γ σ : Type*}

/-! ## Quasipolynomially bounded output size -/

/-- `QuasiSizeBound f`: the encoding of `f a` is quasipolynomially bounded in the encoding of
`a`.  The bound is given in the explicit monotone form `2 ^ ((log₂ n + 2) ^ c)`, which is the
witness shape of `RAM.QuasiPolyBound` (`RAM.quasiPolyBound_witness`). -/
def QuasiSizeBound [Enc α] [Enc β] (f : α → β) : Prop :=
  ∃ c : ℕ, ∀ a, Enc.size (f a) ≤ 2 ^ ((Nat.log 2 (Enc.size a) + 2) ^ c)

namespace QuasiSizeBound

/-- Any quasipolynomial bound on the answer gives a `QuasiSizeBound`. -/
theorem of_bound [Enc α] [Enc β] {f : α → β} {S : ℕ → ℕ} (hS : QuasiPolyBound S)
    (h : ∀ a, Enc.size (f a) ≤ S (Enc.size a)) : QuasiSizeBound f := by
  obtain ⟨c, hc⟩ := hS
  exact ⟨c, fun a => le_trans (h a) (hc _)⟩

/-- The bound as a monotone `QuasiPolyBound`, in the form the composition rules take. -/
theorem exists_quasiPolyBound [Enc α] [Enc β] {f : α → β} (h : QuasiSizeBound f) :
    ∃ S : ℕ → ℕ, QuasiPolyBound S ∧ (∀ n n', n ≤ n' → S n ≤ S n') ∧
      ∀ a, Enc.size (f a) ≤ S (Enc.size a) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun n => 2 ^ ((Nat.log 2 n + 2) ^ c), quasiPolyBound_witness c,
    fun _ _ h => quasiPolyBound_witness_mono c h, hc⟩

theorem of_le [Enc α] [Enc β] [Enc γ] {f : α → β} {g : α → γ} (hg : QuasiSizeBound g)
    (h : ∀ a, Enc.size (f a) ≤ Enc.size (g a)) : QuasiSizeBound f := by
  obtain ⟨c, hc⟩ := hg
  exact ⟨c, fun a => le_trans (h a) (hc a)⟩

/-- **A quasipolynomial of a quasipolynomial is quasipolynomial**
(`RAM.QuasiPolyBound.comp`), so the size bounds compose. -/
theorem comp [Enc α] [Enc β] [Enc γ] {f : α → β} {g : β → γ} (hf : QuasiSizeBound f)
    (hg : QuasiSizeBound g) : QuasiSizeBound (fun a => g (f a)) := by
  obtain ⟨S, hSb, _, hS⟩ := hf.exists_quasiPolyBound
  obtain ⟨T, hTb, hTm, hT⟩ := hg.exists_quasiPolyBound
  exact of_bound (hTb.comp hSb) (fun a => le_trans (hT (f a)) (hTm _ _ (hS a)))

theorem pair [Enc α] [Enc β] [Enc γ] {f : α → β} {g : α → γ} (hf : QuasiSizeBound f)
    (hg : QuasiSizeBound g) : QuasiSizeBound (fun a => (f a, g a)) := by
  obtain ⟨S, hSb, _, hS⟩ := hf.exists_quasiPolyBound
  obtain ⟨T, hTb, _, hT⟩ := hg.exists_quasiPolyBound
  refine of_bound (S := fun n => 2 * S n + 2 * T n)
    (((polyBound_const 2).quasiPoly.mul hSb).add ((polyBound_const 2).quasiPoly.mul hTb))
    (fun a => ?_)
  have h1 := Combine.size_pair_le (f a) (g a)
  have h2 := hS a
  have h3 := hT a
  dsimp only
  omega

end QuasiSizeBound

/-- Every polynomial size bound is a quasipolynomial one. -/
theorem SizeBound.quasiSizeBound [Enc α] [Enc β] {f : α → β} (h : SizeBound f) :
    QuasiSizeBound f := by
  obtain ⟨S, hSb, _, hS⟩ := h.exists_polyBound
  exact QuasiSizeBound.of_bound hSb.quasiPoly hS

/-! ## The class -/

/-- `QuasiFun f`: `f` is computed by a clean quasipolynomial-time routine at the workspace
convention with sixteen work registers, and the size of the output is *quasipolynomially*
bounded in the size of the input.

This is `RAM.QuasiPolyFun` with the polynomial size bound relaxed.  It is the class of the
paper's procedures with `k = O(log n)`, whose intermediate data — the table of all `k`-tuples —
is of size `2^{O(log² n)}`. -/
structure QuasiFun [Enc α] [Enc β] (f : α → β) : Prop where
  /-- A clean quasipolynomial-time routine at the workspace convention `K = 16`. -/
  time : QuasiPolyTimeCleanAt 16 f
  /-- The encoding of `f a` is quasipolynomially bounded in the encoding of `a`. -/
  size : QuasiSizeBound f

theorem PolyFun.quasiFun [Enc α] [Enc β] {f : α → β} (h : PolyFun f) : QuasiFun f :=
  ⟨h.time.quasiPolyTimeCleanAt, h.size.quasiSizeBound⟩

theorem QuasiPolyFun.quasiFun [Enc α] [Enc β] {f : α → β} (h : QuasiPolyFun f) : QuasiFun f :=
  ⟨h.time, h.size.quasiSizeBound⟩

/-- **The return to the small class.**  A `QuasiFun` whose answer is polynomially small is a
`RAM.QuasiPolyFun`, hence reaches `RAM.QuasiPolyTime` through `RAM.QuasiPolyFun.quasiPolyTime`.
Every use of `QuasiFun` should end in this lemma. -/
theorem QuasiFun.quasiPolyFun [Enc α] [Enc β] {f : α → β} (h : QuasiFun f) (hs : SizeBound f) :
    QuasiPolyFun f := ⟨h.time, hs⟩

/-- Membership depends only on the function, so a pointwise identity transfers it. -/
theorem QuasiFun.of_eq [Enc α] [Enc β] {f g : α → β} (h : QuasiFun f) (hfg : ∀ a, f a = g a) :
    QuasiFun g := by
  have : f = g := funext hfg
  exact this ▸ h

theorem quasiFun_id [Enc α] : QuasiFun (id : α → α) := polyFun_id.quasiFun

theorem quasiFun_const [Enc α] [Enc β] (b : β) : QuasiFun (fun _ : α => b) :=
  (polyFun_const b).quasiFun

/-! ## Composition and pairing

Both rules are the corresponding rules for `RAM.QuasiPolyFun` with the *polynomial* bound on the
intermediate size replaced by a quasipolynomial one.  For composition this is exactly
`RAM.QuasiPolyTimeCleanAt.comp_quasiSize`; for pairing the time bound of
`RAM.Pairing.cleanComputeAt_pair` is linear in the two answers, so a quasipolynomial bound on
them keeps the total quasipolynomial. -/

/-- **Composition.**  Quasipolynomial time after a quasipolynomially large intermediate result
is quasipolynomial time. -/
theorem QuasiFun.comp [Enc α] [Enc β] [Enc γ] {f : α → β} {g : β → γ} (hf : QuasiFun f)
    (hg : QuasiFun g) : QuasiFun (fun a => g (f a)) := by
  obtain ⟨S, hSb, -, hS⟩ := hf.size.exists_quasiPolyBound
  exact ⟨hf.time.comp_quasiSize hg.time hSb hS, hf.size.comp hg.size⟩

theorem QuasiFun.comp_poly [Enc α] [Enc β] [Enc γ] {f : α → β} {g : β → γ} (hf : QuasiFun f)
    (hg : PolyFun g) : QuasiFun (fun a => g (f a)) := hf.comp hg.quasiFun

theorem PolyFun.comp_quasiFun [Enc α] [Enc β] [Enc γ] {f : α → β} {g : β → γ} (hf : PolyFun f)
    (hg : QuasiFun g) : QuasiFun (fun a => g (f a)) := hf.quasiFun.comp hg

set_option maxRecDepth 10000 in
/-- **Pairing.** -/
theorem QuasiFun.pair [Enc α] [Enc β] [Enc γ] {f : α → β} {g : α → γ} (hf : QuasiFun f)
    (hg : QuasiFun g) : QuasiFun (fun a => (f a, g a)) := by
  obtain ⟨Sf, hSfb, -, hSf⟩ := hf.size.exists_quasiPolyBound
  obtain ⟨Sg, hSgb, -, hSg⟩ := hg.size.exists_quasiPolyBound
  obtain ⟨Pf, Tf, hTf, hPf⟩ := hf.time
  obtain ⟨Pg, Tg, hTg, hPg⟩ := hg.time
  refine ⟨⟨Pairing.pairProg 16 Pf Pg, _, ?_,
    Pairing.cleanComputeAt_pair (by omega) hPf hPg hSf hSg⟩, hf.size.pair hg.size⟩
  refine QuasiPolyBound.mono (T := fun n => 19 * n + 19 * Sf n + 19 * Sg n + 10 * Tf n
    + 10 * Tg n + (11 * 16 + 200)) ?_ (fun n => by dsimp only; omega)
  exact ((((((polyBound_const 19).mul polyBound_id).quasiPoly.add
    ((polyBound_const 19).quasiPoly.mul hSfb)).add
    ((polyBound_const 19).quasiPoly.mul hSgb)).add
    ((polyBound_const 10).quasiPoly.mul hTf)).add
    ((polyBound_const 10).quasiPoly.mul hTg)).add
    (polyBound_const (11 * 16 + 200)).quasiPoly

/-! ## The conditionals

The dispatchers of `Workspace/Machine/Cases.lean` and `Workspace/Machine/ListOps4.lean`, whose
machine-level time bounds already mention no size at all, so only the size fields change. -/

theorem quasiSizeBound_optionElim [Enc β] [Enc σ] [Enc γ] {g : σ → γ} {h : β × σ → γ}
    (hg : QuasiSizeBound g) (hh : QuasiSizeBound h) :
    QuasiSizeBound (fun p : Option β × σ => p.1.elim (g p.2) (fun b => h (b, p.2))) := by
  obtain ⟨S, hSb, hSm, hS⟩ := hg.exists_quasiPolyBound
  obtain ⟨T, hTb, hTm, hT⟩ := hh.exists_quasiPolyBound
  refine QuasiSizeBound.of_bound (S := fun n => S n + T n) (hSb.add hTb) ?_
  rintro ⟨o, s⟩
  cases o with
  | none =>
      show Enc.size (g s) ≤ S (Enc.size ((none, s) : Option β × σ))
        + T (Enc.size ((none, s) : Option β × σ))
      have h1 := hS s
      have h2 := hSm _ _ (Combine.size_snd_le (none : Option β) s)
      omega
  | some b =>
      show Enc.size (h (b, s)) ≤ S (Enc.size ((some b, s) : Option β × σ))
        + T (Enc.size ((some b, s) : Option β × σ))
      have h1 := hT (b, s)
      have h2 := hTm _ _ (size_strip_le b s)
      omega

/-- **`Option.elim` with a case-dependent default.** -/
theorem QuasiFun.optionElim [Enc β] [Enc σ] [Enc γ] {g : σ → γ} {h : β × σ → γ}
    (hg : QuasiFun g) (hh : QuasiFun h) :
    QuasiFun (fun p : Option β × σ => p.1.elim (g p.2) (fun b => h (b, p.2))) := by
  rcases isEmpty_or_nonempty β with hβ | hβ
  · refine (polyFun_snd.quasiFun.comp hg).of_eq (fun p => ?_)
    obtain ⟨o, s⟩ := p
    cases o with
    | none => rfl
    | some b => exact (hβ.false b).elim
  · exact ⟨quasiPolyTimeCleanAt_optionElim (by omega) hβ hg.time hh.time,
      quasiSizeBound_optionElim hg.size hh.size⟩

/-- **Case analysis on a list carried alongside a state.** -/
theorem QuasiFun.listCases [Enc α] [Enc σ] [Enc γ] {g : σ → γ} {h : (α × List α) × σ → γ}
    (hg : QuasiFun g) (hh : QuasiFun h) :
    QuasiFun (fun p : List α × σ =>
      match p.1 with
      | [] => g p.2
      | a :: l => h ((a, l), p.2)) := by
  have huncons : QuasiFun (fun p : List α × σ => (uncons p.1, p.2)) :=
    ((polyFun_fst.comp polyFun_uncons).pair polyFun_snd).quasiFun
  refine (huncons.comp (hg.optionElim hh)).of_eq (fun p => ?_)
  obtain ⟨l, s⟩ := p
  cases l with
  | nil => rfl
  | cons a t => rfl

/-- **The conditional**: a cheap test, two quasipolynomial branches. -/
theorem QuasiFun.ite [Enc α] [Enc β] {p : α → Bool} {f g : α → β} (hp : PolyFun p)
    (hf : QuasiFun f) (hg : QuasiFun g) :
    QuasiFun (fun a => if p a then f a else g a) := by
  have hpair : QuasiFun (fun a : α => ((if p a then none else some a), a)) :=
    ((PolyFun.ite hp (polyFun_const none) polyFun_some).pair polyFun_id).quasiFun
  refine (hpair.comp (hf.optionElim (polyFun_snd.quasiFun.comp hg))).of_eq (fun a => ?_)
  by_cases h : p a
  · simp [h]
  · simp [h]

/-! ## Iteration with a quasipolynomially large state

This is `RAM.QuasiPolyFun.iterateSetup` (`Workspace/Machine/IterateInv.lean`) with the
polynomial bound `p` on the state replaced by a quasipolynomial one.  Nothing changes on the
machine: `RAM.quasiPolyTimeCleanAt_recursion` (`Workspace/Machine/Iterate.lean`) already takes a
`RAM.QuasiPolyBound` for the cost of one round, and a quasipolynomial cost evaluated at a
quasipolynomially bounded state is again quasipolynomial (`RAM.QuasiPolyBound.comp`).  What blocks
the old statement is only the *size field* of `RAM.QuasiPolyFun`, and that is what `QuasiFun`
relaxes. -/

/-- **Bounded iteration from a set-up, over quasipolynomially large states.**  The routine
computes `setUp a = (k, s)`, iterates `step` exactly `k` times from `s`, and reads the answer off
the final state.  The number of rounds and the size of every state along the orbit of `s` are
bounded by quasipolynomials of the input size; the total cost is rounds × (cost of one round at
that size), which is quasipolynomial. -/
theorem QuasiFun.iterateSetup [Enc α] [Enc β] [Enc σ] {setUp : α → ℕ × σ} {step : σ → σ}
    {readOff : σ → β} {q p : ℕ → ℕ}
    (hsetUp : QuasiFun setUp)
    (hstep : QuasiFun (fun x : ℕ × σ => (x.1 - 1, step x.2)))
    (hread : QuasiFun readOff)
    (hq : ∀ a : α, (setUp a).1 ≤ q (Enc.size a)) (hqb : QuasiPolyBound q)
    (hp : ∀ (a : α), ∀ j ≤ (setUp a).1, Enc.size (step^[j] (setUp a).2) ≤ p (Enc.size a))
    (hpb : QuasiPolyBound p) :
    QuasiFun (fun a => readOff (step^[(setUp a).1] (setUp a).2)) := by
  obtain ⟨cq, hcq⟩ := hqb
  -- the size of the pair `(counter, state)` along the orbit
  set P : ℕ → ℕ := fun n => 2 * ((Nat.log 2 n + 2) ^ cq + 3) + 2 * p n with hPdef
  have hPb : QuasiPolyBound P :=
    (((polyBound_const 2).mul ((polyBound_logPow cq).add (polyBound_const 3))).quasiPoly).add
      ((polyBound_const 2).quasiPoly.mul hpb)
  have hpair : ∀ (a : α), ∀ j ≤ (setUp a).1,
      Enc.size (((setUp a).1 - j, step^[j] (setUp a).2) : ℕ × σ) ≤ P (Enc.size a) := by
    intro a j hj
    have h1 := Combine.size_pair_le ((setUp a).1 - j) (step^[j] (setUp a).2)
    have h2 : Enc.size ((setUp a).1 - j) = Nat.size ((setUp a).1 - j) + 2 :=
      Small.size_nat _
    have h3 : (setUp a).1 - j ≤ 2 ^ ((Nat.log 2 (Enc.size a) + 2) ^ cq) :=
      le_trans (Nat.sub_le _ _) (le_trans (hq a) (hcq _))
    have h4 : Nat.size ((setUp a).1 - j) ≤ (Nat.log 2 (Enc.size a) + 2) ^ cq + 1 :=
      size_counter_le h3
    have h5 := hp a j hj
    simp only [hPdef]
    omega
  -- the time bound
  obtain ⟨P₁, T₁, hT₁, hP₁⟩ := hsetUp.time
  obtain ⟨Q, T₂, ⟨c, hc⟩, hQ⟩ := hstep.time
  obtain ⟨P₃, T₃, ⟨c₃, hc₃⟩, hP₃⟩ :=
    ((polyFun_snd (α := ℕ) (β := σ)).quasiFun.comp hread).time
  refine ⟨quasiPolyTimeCleanAt_recursion (setUp := setUp) (step := step) (readOff := readOff)
    (T₂ := fun n => 2 ^ ((Nat.log 2 n + 2) ^ c)) (T₃ := fun n => 2 ^ ((Nat.log 2 n + 2) ^ c₃))
    (p := fun n => 2 ^ ((Nat.log 2 (P n) + 2) ^ c)) (q := q)
    (u := fun n => 2 ^ ((Nat.log 2 (P n) + 2) ^ c₃))
    hP₁ hT₁ (hQ.mono hc) (hP₃.mono hc₃) hq ⟨cq, hcq⟩ ?_
    ((quasiPolyBound_witness c).comp hPb) ?_
    ((quasiPolyBound_witness c₃).comp hPb), ?_⟩
  · intro a j hj
    exact quasiPolyBound_witness_mono c (hpair a j (le_of_lt hj))
  · intro a
    have h := hpair a (setUp a).1 (le_refl _)
    rw [Nat.sub_self] at h
    exact quasiPolyBound_witness_mono c₃ h
  · -- the size bound: a quasipolynomial of a quasipolynomial
    have hf₁ : QuasiSizeBound (fun a : α => step^[(setUp a).1] (setUp a).2) :=
      QuasiSizeBound.of_bound hpb (fun a => hp a (setUp a).1 (le_refl _))
    exact hf₁.comp hread.size

end RAM
