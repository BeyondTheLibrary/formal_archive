/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: computing the image `ψ_T(σ)` of a *new* generator, so that the while
loop of Procedure LocalCertificates (§13.1) can keep its action data up to date.
-/
import Workspace.Algo.LocalCertAff
import Workspace.Algo.Labelled

/-!
# The forward image `σ ↦ ψ_T(σ)` (§13.1)

The while loop of Procedure LocalCertificates carries the pair `(W, H(W))` *and* the images
of the generators of `H(W)` under `ψ_T` — lines 03, 04a, 07 and 10 all need them, and no
routine can recover them from the generators alone, because `ψ_T` is known only on the
generators the caller was given.  Procedure Recompute `H(W)` returns `H(W_new)` by
generators that come out of a stabilizer-chain computation, with no expression in the old
generators.  So after every round the images have to be *recomputed*.

They can be, and with no new machinery.  Put the *old* group in its graph form on `Ω ⊔ T`
(`Algo.rawExtDom`, `Algo.rawExtGens` — the loop already holds the images of the old
generators, so this is a plain map).  The graph group is exactly
`{a ⊔ ψ_T(a) | a ∈ H(W_old)}` (`Algo.mem_ext_group_iff`), so for `σ ∈ H(W_old)` it contains
exactly one element whose restriction to the bottom half `Δ = {0, …, n−1}` is `σ`, namely
`σ ⊔ ψ_T(σ)`.  Finding that element is what `Algo.rawPreimage` does (Prop. 2.2.6 (b),
Observation 11.1.11), and reading its top half is `Algo.rawRestrictPerm` on
`Algo.rawExtWin`.  Both are already `RAM.PolyFun`.

The loop therefore stays at ground size `n`, and Procedure Recompute `H(W)`
(`Workspace/Algo/LocalCertRound.lean`) is used unchanged.  See the note "A13 session 3" in
`Workspace/Algo/DESIGN.md` for the two alternatives that were weighed against this one.

## Main definitions

* `Algo.rawImgOf` — the forward image `σ ↦ ψ_T(σ)`.

## Main results

* `Algo.isInvariant_botWin` — the bottom half `Ω` is invariant under the graph group;
* `Algo.winRestrictHom_botWin` — the restriction of `a ⊔ b` to the bottom half is `a`;
* `Algo.rawImgOf_spec` — **the routine computes `ψ_T(σ)`**;
* `Algo.wf_rawImgOf` — its answer is a well-formed permutation of the test set;
* `Algo.polyFun_rawImgOf` — it runs in polynomial time.

No axiom, no `sorry`, no `native_decide`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

variable {n m : ℕ} {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}

/-! ## The bottom half as a window

`Algo.extWin n m` is the top half of `Ω ⊔ Γ`.  The forward image needs the *bottom* half,
which is `List.range n`. -/

theorem length_botWin (n : ℕ) : (List.range n).length = n := by simp

theorem nodup_botWin (n : ℕ) : (List.range n).Nodup := List.nodup_range

theorem lt_botWin {u : ℕ} (h : u ∈ List.range n) : u < n + m := by
  have := List.mem_range.1 h
  omega

theorem getD_botWin {n j : ℕ} (h : j < n) : (List.range n).getD j 0 = j := by
  have hj : j < (List.range n).length := by rw [length_botWin]; exact h
  rw [List.getD_eq_getElem _ _ hj]
  simp

theorem mem_botWinSet {x : Fin (n + m)} :
    x ∈ winSet (n + m) (List.range n) ↔ (x : ℕ) < n := by
  rw [mem_winSet, List.mem_range]

section Graph

variable {ϕ : genGroup gens →* Perm (Fin m)}

/-- **The bottom half `Ω` is invariant under the graph of `ψ`.**  A permutation `a ⊔ b` maps
a point of `Ω` to a point of `Ω` and a point of `Γ` to a point of `Γ`. -/
theorem isInvariant_botWin (hI : ImgsOf gens imgs ϕ) :
    Babai.IsInvariant (genGroup (extGensOf n m gens imgs))
      (winSet (n + m) (List.range n)) := by
  apply (Babai.isInvariant_iff_mem _ _).2
  intro σ hσ x
  obtain ⟨a, ha, rfl⟩ := (mem_ext_group_iff hI).1 hσ
  constructor
  · intro hx
    have hxn : (x : ℕ) < n := mem_botWinSet.1 hx
    have hval : ((extPerm n m a (ϕ ⟨a, ha⟩) x : Fin (n + m)) : ℕ) = (a ⟨(x : ℕ), hxn⟩ : ℕ) := by
      have h := extPerm_val_lt a (ϕ ⟨a, ha⟩) hxn x.isLt
      rwa [Fin.eta] at h
    refine mem_botWinSet.2 ?_
    rw [hval]
    exact (a ⟨(x : ℕ), hxn⟩).isLt
  · intro hx
    have hlt := mem_botWinSet.1 hx
    refine mem_botWinSet.2 ?_
    by_contra hcon
    push_neg at hcon
    obtain ⟨j, hj, hxj⟩ : ∃ j, j < m ∧ (x : ℕ) = n + j := by
      refine ⟨(x : ℕ) - n, ?_, by omega⟩
      have := x.isLt
      omega
    have hx' : x = (⟨n + j, by omega⟩ : Fin (n + m)) := Fin.ext hxj
    have hval : ((extPerm n m a (ϕ ⟨a, ha⟩) x : Fin (n + m)) : ℕ)
        = n + ((ϕ ⟨a, ha⟩) ⟨j, hj⟩ : ℕ) := by
      rw [hx']
      exact extPerm_val_ge a (ϕ ⟨a, ha⟩) hj (by omega)
    omega

end Graph

/-! ## The restriction to the bottom half, in window labels

`Algo.rawPreimage` is specified in terms of `Algo.winRestrictHom`, whose target is
`Perm (Fin Δ.length)`.  For `Δ = List.range n` that is `Perm (Fin (List.range n).length)`,
which is `Perm (Fin n)` only propositionally, so the two are related by the transport
`Equiv.permCongr (finCongr _)`.  The next two lemmas are that transport and the value of the
restriction. -/

/-- **The transport of an encoding along `Fin k ≃ Fin k'`.** -/
theorem encPerm_finCongr {k k' : ℕ} (h : k = k') (σ : Perm (Fin k)) :
    encPerm k' ((finCongr h).permCongr σ) = encPerm k σ := by
  subst h
  refine List.ext_getElem (by simp) (fun i hi hi' => ?_)
  simp only [encPerm, List.getElem_ofFn]
  rfl

section Restrict

variable {ϕ : genGroup gens →* Perm (Fin m)}

/-- **The restriction of `a ⊔ b` to the bottom half is `a`**, in window labels. -/
theorem winRestrictHom_botWin (hI : ImgsOf gens imgs ϕ) (a : Perm (Fin n)) (b : Perm (Fin m))
    (hmem : extPerm n m a b ∈ genGroup (extGensOf n m gens imgs)) :
    winRestrictHom (n + m) (List.range n) (nodup_botWin n) (fun _ h => lt_botWin h)
        (genGroup (extGensOf n m gens imgs)) (isInvariant_botWin hI)
        ⟨extPerm n m a b, hmem⟩
      = (finCongr (length_botWin n).symm).permCongr a := by
  refine Equiv.ext (fun k => Fin.ext ?_)
  have hk : (k : ℕ) < n := lt_of_lt_of_eq k.isLt (length_botWin n)
  have hval := winRestrictHom_val (n := n + m) (List.range n) (nodup_botWin n)
    (fun _ h => lt_botWin h) (isInvariant_botWin hI)
    (⟨extPerm n m a b, hmem⟩ : genGroup (extGensOf n m gens imgs)) k
  have hjn : ((winRestrictHom (n + m) (List.range n) (nodup_botWin n)
      (fun _ h => lt_botWin h) (genGroup (extGensOf n m gens imgs)) (isInvariant_botWin hI)
      ⟨extPerm n m a b, hmem⟩ k : Fin (List.range n).length) : ℕ) < n :=
    lt_of_lt_of_eq (Fin.isLt _) (length_botWin n)
  have hpt : (((winEquiv (n + m) (List.range n) (nodup_botWin n)
      (fun _ h => lt_botWin h) k : ↥(winSet (n + m) (List.range n))) : Fin (n + m)) : ℕ)
      = (k : ℕ) := by
    rw [winEquiv_apply, winPt_val]
    exact getD_botWin hk
  have harg : ((winEquiv (n + m) (List.range n) (nodup_botWin n)
      (fun _ h => lt_botWin h) k : ↥(winSet (n + m) (List.range n))) : Fin (n + m))
      = (⟨(k : ℕ), by omega⟩ : Fin (n + m)) := Fin.ext hpt
  have harg' : ((((⟨extPerm n m a b, hmem⟩ : genGroup (extGensOf n m gens imgs)) :
        Perm (Fin (n + m)))
          ((winEquiv (n + m) (List.range n) (nodup_botWin n)
            (fun _ h => lt_botWin h) k : ↥(winSet (n + m) (List.range n))) : Fin (n + m)) :
        Fin (n + m)) : ℕ) = (a ⟨(k : ℕ), hk⟩ : ℕ) := by
    rw [harg]
    exact extPerm_val_lt a b hk (by omega)
  have hrhs : (((finCongr (length_botWin n).symm).permCongr a k :
      Fin (List.range n).length) : ℕ) = (a ⟨(k : ℕ), hk⟩ : ℕ) := rfl
  exact ((getD_botWin hjn).symm.trans (hval.trans harg')).trans hrhs.symm

end Restrict

/-! ## The routine -/

/-- **The forward image `σ ↦ ψ(σ)`** (§13.1, the images the while loop carries).  Put the
group in its graph form on `Ω ⊔ Γ`, find the element of the graph group whose bottom half is
`σ` (`Algo.rawPreimage`), and read its top half.  The junk value — the identity on `Γ` — is
returned when `σ` is not in the group, which the specification excludes. -/
def rawImgOf (p : RawAction × RawPerm) : RawPerm :=
  rawRestrictPerm (rawExtWin (p.1.1.1, p.1.2.1),
    (rawPreimage ((rawExtDom (p.1.1.1, p.1.2.1), rawExtGens (p.1.1.2, p.1.2.2)),
        (List.range p.1.1.1.length, p.2))).getD
      (rawOne (rawExtDom (p.1.1.1, p.1.2.1))))

section Spec

variable {ϕ : genGroup gens →* Perm (Fin m)} {dom gdom : List ℕ}

/-- **The routine computes the image.**  Paper: the images of the generators under `ψ_T`
that Procedure LocalCertificates carries from one round of the while loop to the next
(§13.1, lines 03, 04a, 07, 10).

*Proof.*  The graph group is `{a ⊔ ϕ(a) | a ∈ G}` (`Algo.mem_ext_group_iff`), so
`σ ⊔ ϕ(σ)` is an element of it whose restriction to the bottom half is `σ`; hence
`Algo.rawPreimage` does not answer `none` (`Algo.rawPreimage_eq_none`).  Whatever it answers
is an element `a ⊔ b` of the graph group with the same restriction
(`Algo.rawPreimage_eq_some`), and `Algo.winRestrictHom_botWin` reads that restriction as
`a`, so `a = σ`, hence `b = ϕ(σ)`.  Reading the top half is
`Algo.rawRestrictPerm_extPerm`. -/
theorem rawImgOf_spec (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) {σ : Perm (Fin n)} (hσ : σ ∈ genGroup gens) :
    rawImgOf (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), encPerm n σ)
      = encPerm m (ϕ ⟨σ, hσ⟩) := by
  classical
  set Δ : List ℕ := List.range n with hΔdef
  have hlen : Δ.length = n := length_botWin n
  have hnd : Δ.Nodup := nodup_botWin n
  have hlt : ∀ u ∈ Δ, u < n + m := fun _ h => lt_botWin h
  have hinv := isInvariant_botWin (n := n) (m := m) (gens := gens) (imgs := imgs) hI
  -- the extended data
  have hED : rawExtDom (dom, gdom) = dom ++ gdom := rfl
  have hEG : rawExtGens (gens.map (encPerm n), imgs.map (encPerm m))
      = (extGensOf n m gens imgs).map (encPerm (n + m)) := rawExtGens_spec gens imgs hI.1
  have hEW : rawExtWin (dom, gdom) = extWin n m := rawExtWin_eq dom gdom hd hg
  have hdomlen : (dom ++ gdom).length = n + m := by simp [hd, hg]
  have hrange : List.range dom.length = Δ := by rw [hd, hΔdef]
  -- the target, transported
  set hw : Perm (Fin Δ.length) := (finCongr hlen.symm).permCongr σ with hwdef
  have hwenc : encPerm Δ.length hw = encPerm n σ := encPerm_finCongr hlen.symm σ
  -- the element of the graph group with bottom half `σ`
  have hmem0 : extPerm n m σ (ϕ ⟨σ, hσ⟩) ∈ genGroup (extGensOf n m gens imgs) :=
    (mem_ext_group_iff hI).2 ⟨σ, hσ, rfl⟩
  have hrestr0 : winRestrictHom (n + m) Δ hnd hlt (genGroup (extGensOf n m gens imgs)) hinv
      ⟨extPerm n m σ (ϕ ⟨σ, hσ⟩), hmem0⟩ = hw :=
    winRestrictHom_botWin hI σ (ϕ ⟨σ, hσ⟩) hmem0
  -- unfold the routine
  have hunfold : rawImgOf (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))),
      encPerm n σ)
      = rawRestrictPerm (extWin n m,
          (rawPreimage (((dom ++ gdom), (extGensOf n m gens imgs).map (encPerm (n + m))),
            (Δ, encPerm Δ.length hw))).getD (rawOne (dom ++ gdom))) := by
    rw [rawImgOf]
    show rawRestrictPerm (rawExtWin (dom, gdom),
        (rawPreimage ((rawExtDom (dom, gdom),
          rawExtGens (gens.map (encPerm n), imgs.map (encPerm m))),
            (List.range dom.length, encPerm n σ))).getD
          (rawOne (rawExtDom (dom, gdom)))) = _
    rw [hED, hEG, hEW, hrange, hwenc]
  rw [hunfold]
  rcases hp : rawPreimage (((dom ++ gdom), (extGensOf n m gens imgs).map (encPerm (n + m))),
      (Δ, encPerm Δ.length hw)) with _ | r
  · exact absurd hrestr0
      (rawPreimage_eq_none hdomlen hnd hlt hinv hp (extPerm n m σ (ϕ ⟨σ, hσ⟩)) hmem0)
  · obtain ⟨τ, hτ, hrenc, hrrestr⟩ :=
      rawPreimage_eq_some hdomlen hnd hlt hinv hp
    obtain ⟨a, ha, rfl⟩ := (mem_ext_group_iff hI).1 hτ
    have hrestr : winRestrictHom (n + m) Δ hnd hlt (genGroup (extGensOf n m gens imgs)) hinv
        ⟨extPerm n m a (ϕ ⟨a, ha⟩), hτ⟩ = (finCongr hlen.symm).permCongr a :=
      winRestrictHom_botWin hI a (ϕ ⟨a, ha⟩) hτ
    have haσ : a = σ := by
      have h1 : (finCongr hlen.symm).permCongr a = (finCongr hlen.symm).permCongr σ := by
        rw [← hrestr, hrrestr, hwdef]
      exact (Equiv.permCongr (finCongr hlen.symm)).injective h1
    subst haσ
    rw [Option.getD_some, hrenc, rawRestrictPerm_extPerm]

/-- The answer is a well-formed permutation of the test set. -/
theorem wf_rawImgOf (hd : dom.length = n) (hg : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) {σ : Perm (Fin n)} (hσ : σ ∈ genGroup gens) :
    RawPerm.WF m
      (rawImgOf (((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))), encPerm n σ)) := by
  rw [rawImgOf_spec hd hg hI hσ]
  exact wf_encPerm m _

end Spec

/-! ## The running time -/

theorem polyFun_rawImgOf : PolyFun rawImgOf := by
  have hdom : PolyFun (fun p : RawAction × RawPerm => p.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have hgdom : PolyFun (fun p : RawAction × RawPerm => p.1.2.1) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_fst
  have hgens : PolyFun (fun p : RawAction × RawPerm => p.1.1.2) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_snd
  have himgs : PolyFun (fun p : RawAction × RawPerm => p.1.2.2) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_snd
  have hED : PolyFun (fun p : RawAction × RawPerm => rawExtDom (p.1.1.1, p.1.2.1)) :=
    (hdom.pair hgdom).comp polyFun_rawExtDom
  have hEG : PolyFun (fun p : RawAction × RawPerm => rawExtGens (p.1.1.2, p.1.2.2)) :=
    (hgens.pair himgs).comp polyFun_rawExtGens
  have hEW : PolyFun (fun p : RawAction × RawPerm => rawExtWin (p.1.1.1, p.1.2.1)) :=
    (hdom.pair hgdom).comp polyFun_rawExtWin
  have hrange : PolyFun (fun p : RawAction × RawPerm => List.range p.1.1.1.length) :=
    hdom.comp polyFun_rangeLength
  have hpre : PolyFun (fun p : RawAction × RawPerm =>
      rawPreimage ((rawExtDom (p.1.1.1, p.1.2.1), rawExtGens (p.1.1.2, p.1.2.2)),
        (List.range p.1.1.1.length, p.2))) :=
    ((hED.pair hEG).pair (hrange.pair polyFun_snd)).comp polyFun_rawPreimage
  have hgetD : PolyFun (fun p : RawAction × RawPerm =>
      (rawPreimage ((rawExtDom (p.1.1.1, p.1.2.1), rawExtGens (p.1.1.2, p.1.2.2)),
        (List.range p.1.1.1.length, p.2))).getD (rawOne (rawExtDom (p.1.1.1, p.1.2.1)))) :=
    (hpre.pair (hED.comp polyFun_rawOne)).comp polyFun_optionGetD
  exact ((hEW.pair hgetD).comp polyFun_rawRestrictPerm).of_eq (fun _ => rfl)

end Algo
