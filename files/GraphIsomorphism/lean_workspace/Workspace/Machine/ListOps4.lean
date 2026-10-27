import Workspace.Machine.ListOps3

/-!
# Case analysis in quasipolynomial time

`Workspace/Machine/Cases.lean` proves `RAM.PolyFun.optionElim` and `RAM.PolyFun.listCases`, the
two dispatchers every traversal is written with.  The algorithmic layer needs the same two for
branches that are only *quasipolynomial*: one round of Sec. 15 runs the Extended Design Lemma,
whose cost is `n^{O(k)}` with `k = O(log n)`, so the four routines of `Algo.Round.Cost` are
`RAM.QuasiPolyFun`s and not `RAM.PolyFun`s (`Workspace/Algo/Round.lean`).

Nothing new happens on the machine.  `RAM.cleanComputeAt_optionElim` is already stated for
arbitrary monotone time bounds, so the two proofs below are the proofs of `Cases.lean` with
`RAM.polyBound_witness` replaced by `RAM.quasiPolyBound_witness`, which is monotone for the
same reason.

## Main results

* `RAM.quasiPolyTimeCleanAt_optionElim`, `RAM.QuasiPolyFun.optionElim`;
* `RAM.QuasiPolyFun.listCases`, `RAM.polyFun_join`;
* `RAM.QuasiPolyFun.ite`.
-/

namespace RAM

variable {α β γ σ : Type*}

set_option maxRecDepth 4000 in
theorem quasiPolyTimeCleanAt_optionElim [Enc β] [Enc σ] [Enc γ] {K : ℕ} (hK : 16 ≤ K)
    (hb : Nonempty β) {g : σ → γ} {h : β × σ → γ} (hg : QuasiPolyTimeCleanAt K g)
    (hh : QuasiPolyTimeCleanAt K h) :
    QuasiPolyTimeCleanAt K (fun p : Option β × σ => p.1.elim (g p.2) (fun b => h (b, p.2))) := by
  obtain ⟨Pg, Tg, ⟨cg, hcg⟩, hPg⟩ := hg
  obtain ⟨Ph, Th, ⟨ch, hch⟩, hPh⟩ := hh
  refine ⟨Lists.optElimProg K Pg Ph, _, ?_,
    cleanComputeAt_optionElim hK hb (hPg.mono hcg) (hPh.mono hch)
      (fun _ _ hn => quasiPolyBound_witness_mono cg hn)
      (fun _ _ hn => quasiPolyBound_witness_mono ch hn)⟩
  refine QuasiPolyBound.mono (T := fun n => (86 * n + (4 * K + 370))
    + 2 * (2 ^ ((Nat.log 2 n + 2) ^ cg) + 2 ^ ((Nat.log 2 n + 2) ^ ch))) ?_ (fun n => by
      dsimp only
      omega)
  exact (((polyBound_const 86).mul polyBound_id).add
    (polyBound_const (4 * K + 370))).quasiPoly.add
      ((polyBound_const 2).quasiPoly.mul
        ((quasiPolyBound_witness cg).add (quasiPolyBound_witness ch)))

/-- **`Option.elim` with a case-dependent default, in quasipolynomial time.**  The
quasipolynomial copy of `RAM.PolyFun.optionElim`. -/
theorem QuasiPolyFun.optionElim [Enc β] [Enc σ] [Enc γ] {g : σ → γ} {h : β × σ → γ}
    (hg : QuasiPolyFun g) (hh : QuasiPolyFun h) :
    QuasiPolyFun (fun p : Option β × σ => p.1.elim (g p.2) (fun b => h (b, p.2))) := by
  rcases isEmpty_or_nonempty β with hβ | hβ
  · refine (polyFun_snd.quasiPolyFun.comp hg).of_eq (fun p => ?_)
    obtain ⟨o, s⟩ := p
    cases o with
    | none => rfl
    | some b => exact (hβ.false b).elim
  · exact ⟨quasiPolyTimeCleanAt_optionElim (by omega) hβ hg.time hh.time,
      sizeBound_optionElim hg.size hh.size⟩

/-- **Case analysis on a list carried alongside a state, in quasipolynomial time.**  The
quasipolynomial copy of `RAM.PolyFun.listCases`. -/
theorem QuasiPolyFun.listCases [Enc α] [Enc σ] [Enc γ] {g : σ → γ} {h : (α × List α) × σ → γ}
    (hg : QuasiPolyFun g) (hh : QuasiPolyFun h) :
    QuasiPolyFun (fun p : List α × σ =>
      match p.1 with
      | [] => g p.2
      | a :: l => h ((a, l), p.2)) := by
  have huncons : QuasiPolyFun (fun p : List α × σ => (uncons p.1, p.2)) :=
    ((polyFun_fst.comp polyFun_uncons).pair polyFun_snd).quasiPolyFun
  refine (huncons.comp (hg.optionElim hh)).of_eq (fun p => ?_)
  obtain ⟨l, s⟩ := p
  cases l with
  | nil => rfl
  | cons a t => rfl

/-- **Merging two `Option`s.**  `Option.join` is the case analysis with `none` in both empty
branches; it is what turns an answer of the shape "the machine returned nothing, or it returned
an answer which is itself `none`" into one `Option`. -/
theorem polyFun_join [Enc β] : PolyFun (fun o : Option (Option β) => o.join) := by
  have h1 : PolyFun (fun o : Option (Option β) => (o, (0 : ℕ))) :=
    polyFun_id.pair (polyFun_const 0)
  refine (h1.comp (PolyFun.optionElim (g := fun _ : ℕ => (none : Option β))
    (h := fun q : Option β × ℕ => q.1) (polyFun_const none) polyFun_fst)).of_eq (fun o => ?_)
  cases o with
  | none => rfl
  | some b => rfl

/-- **The conditional in quasipolynomial time.**  The test is cheap, the two branches are
quasipolynomial. -/
theorem QuasiPolyFun.ite [Enc α] [Enc β] {p : α → Bool} {f g : α → β} (hp : PolyFun p)
    (hf : QuasiPolyFun f) (hg : QuasiPolyFun g) :
    QuasiPolyFun (fun a => if p a then f a else g a) := by
  have hpair : QuasiPolyFun (fun a : α => ((if p a then none else some a), a)) :=
    ((PolyFun.ite hp (polyFun_const none) polyFun_some).pair polyFun_id).quasiPolyFun
  refine (hpair.comp (hf.optionElim (polyFun_snd.quasiPolyFun.comp hg))).of_eq (fun a => ?_)
  by_cases h : p a
  · simp [h]
  · simp [h]

end RAM
