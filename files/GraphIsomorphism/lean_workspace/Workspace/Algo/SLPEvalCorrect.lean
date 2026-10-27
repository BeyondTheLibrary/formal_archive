import Workspace.Algo.SLPEvalRAM
import Workspace.Algo.Labelled

/-!
# Observation 11.1.11: the answer of the evaluator is `Iso^Δ_G(x, y)`

> **Observation 11.1.11** (Reducing to the window).  Let `G ≤ S(Ω)` and let `Δ` be a
> `G`-invariant subset of `Ω`.  Let `x^Δ` and `y^Δ` be the restriction of `x` and `y` to `Δ`,
> respectively.  Given a straight-line program of length `ℓ` that computes
> `Iso_{G^Δ}(x^Δ, y^Δ)`, we can, in time `O(nℓ) + poly(n)`, compute `Iso^Δ_G(x, y)` (where
> `n = |Ω|`).
>
> *Proof.*  While we concentrate on the action of the elements of `G` on the window, we
> maintain their "tails" – their action on the rest of the permutation domain.  The set
> `Iso_{G^Δ}(x^Δ, y^Δ)` is empty if and only if `Iso^Δ_G(x, y)` is empty.  If
> `Iso_{G^Δ}(x^Δ, y^Δ)` is not empty, in the end we obtain a subset `S ⊆ G` and an element
> `σ ∈ G` such that the restriction of the elements of `S` to `Δ` generates
> `Aut_{G^Δ}(x^Δ)` and the restriction of `σ` to `Δ` belongs to `Iso_{G^Δ}(x^Δ, y^Δ)`.
> Adding to `S` a set of generators of the kernel of the `G`-action on `Δ` we obtain a set of
> generators of `Aut^Δ_G(x)`; and `Iso^Δ_G(x, y) = Aut^Δ_G(x)σ`.

The program is given by its instructions (`Algo.RawSLPInstr`); "computes `Iso_{G^Δ}(x^Δ,
y^Δ)`" is Definition 11.1.10 for the sequence the instructions form in `G^Δ` from the
restrictions of the generators: the marked elements generate `Aut_{G^Δ}(x^Δ)` and the element
named as the representative lies in `Iso_{G^Δ}(x^Δ, y^Δ)` (`Algo.SLPComputesWindowIso`).  The
evaluator runs the same instructions on the full permutations ("we maintain their tails").

* `Algo.decCoset_obsWindow`: the answer of `Algo.obsWindow` is `Iso^Δ_G(x, y)`;
* `Algo.Observation_11_1_11_ram`: the routine `Algo.SLPRAM.obsWindowProg` on the RAM, with
  both the answer and the time `C (n + 1)(ℓ + 1) + p(size of the group and the window)`.
-/

namespace Algo

open Equiv RAM RAM.Targets

/-! ## A straight-line program in a group -/

/-- The element one instruction forms in a group `M` (Definition 11.1.10). -/
def slpStepG {M : Type*} [Group M] (S : List M) (vals : List M) (ins : RawSLPInstr) : M :=
  if ins.1 = 0 then S.getD ins.2.1 1
  else if ins.1 = 1 then vals.getD ins.2.1 1 * vals.getD ins.2.2.1 1
  else (vals.getD ins.2.1 1)⁻¹

/-- One step of the evaluation in a group. -/
def slpAccG {M : Type*} [Group M] (S : List M) (vals : List M) (ins : RawSLPInstr) : List M :=
  vals ++ [slpStepG S vals ins]

/-- **The sequence of a straight-line program in a group `M`** with generators `S`. -/
def slpValsG {M : Type*} [Group M] (S : List M) (prog : List RawSLPInstr) : List M :=
  prog.foldl (slpAccG S) []

/-- The marked elements of a sequence `V` (Definition 11.1.10, "marked as belonging to `T`"). -/
def slpMarkedOf {M : Type*} (prog : List RawSLPInstr) (V : List M) : List M :=
  (prog.zip V).filterMap (fun p => if p.1.2.2.2 = 0 then none else some p.2)

theorem slpMarked_eq (S : RawGens) (prog : List RawSLPInstr) :
    slpMarked S prog = slpMarkedOf prog (slpVals S prog) := rfl

theorem slpMarkedOf_map {M N : Type*} (f : M → N) (prog : List RawSLPInstr) (V : List M) :
    slpMarkedOf prog (V.map f) = (slpMarkedOf prog V).map f := by
  induction prog generalizing V with
  | nil => simp [slpMarkedOf]
  | cons ins prog ih =>
    cases V with
    | nil => simp [slpMarkedOf]
    | cons v V =>
      have := ih V
      simp only [slpMarkedOf] at this ⊢
      simp only [List.map_cons, List.zip_cons_cons, List.filterMap_cons]
      split_ifs <;> simp [this]

theorem getD_map_hom {M N : Type*} [Group M] [Group N] (φ : M →* N) (l : List M) (a : ℕ) :
    (l.map φ).getD a 1 = φ (l.getD a 1) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[a]? <;> simp

theorem slpStepG_map {M N : Type*} [Group M] [Group N] (φ : M →* N) (S vals : List M)
    (ins : RawSLPInstr) :
    φ (slpStepG S vals ins) = slpStepG (S.map φ) (vals.map φ) ins := by
  unfold slpStepG
  split_ifs <;> simp only [getD_map_hom, map_mul, map_inv]

/-- A homomorphism carries the sequence of a program to the sequence of the same program on
the images of the generators. -/
theorem slpValsG_map {M N : Type*} [Group M] [Group N] (φ : M →* N) (S : List M)
    (prog : List RawSLPInstr) : (slpValsG S prog).map φ = slpValsG (S.map φ) prog := by
  have key : ∀ (l : List RawSLPInstr) (init : List M),
      (l.foldl (slpAccG S) init).map φ = l.foldl (slpAccG (S.map φ)) (init.map φ) := by
    intro l
    induction l with
    | nil => intro init; rfl
    | cons ins l ih =>
      intro init
      rw [List.foldl_cons, List.foldl_cons, ih]
      congr 1
      simp [slpAccG, slpStepG_map]
  exact key prog []

/-! ## The raw sequence is the encoded sequence in `G` -/

section Raw

variable {n : ℕ} {G : Subgroup (Perm (Fin n))}

/-- The raw form of an element of `G`. -/
def encIn (g : G) : RawPerm := encPerm n (g : Perm (Fin n))

theorem slpVals_encIn (S : List G) :
    ∀ (l : List RawSLPInstr) (init : List G),
      (∀ k (hk : k < l.length), (l[k].1 = 0 → l[k].2.1 < S.length) ∧
        (l[k].1 ≠ 0 → l[k].2.1 < init.length + k) ∧
        (l[k].1 = 1 → l[k].2.2.1 < init.length + k)) →
      l.foldl (slpAcc (S.map encIn)) (init.map encIn) = (l.foldl (slpAccG S) init).map encIn := by
  intro l
  induction l with
  | nil => intro init _; rfl
  | cons ins l ih =>
    intro init hv
    obtain ⟨h0, h1, h2⟩ := hv 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h0 h1 h2
    have hstep : slpStep (S.map encIn) (init.map encIn) ins = encIn (slpStepG S init ins) := by
      unfold slpStep slpStepG
      split_ifs with hop hop1
      · rw [List.getD_eq_getElem _ _ (by simpa using h0 hop),
          List.getD_eq_getElem _ _ (h0 hop)]
        simp
      · rw [List.getD_eq_getElem _ _ (by simpa using h1 hop),
          List.getD_eq_getElem _ _ (by simpa using h2 hop1),
          List.getD_eq_getElem _ _ (h1 hop), List.getD_eq_getElem _ _ (h2 hop1)]
        simp only [List.getElem_map, encIn, Subgroup.coe_mul]
        exact rawMul_encPerm n _ _
      · rw [List.getD_eq_getElem _ _ (by simpa using h1 hop), List.getD_eq_getElem _ _ (h1 hop)]
        simp only [List.getElem_map, encIn, InvMemClass.coe_inv]
        exact rawInv_encPerm n _
    rw [List.foldl_cons, List.foldl_cons]
    have hacc : slpAcc (S.map encIn) (init.map encIn) ins = (slpAccG S init ins).map encIn := by
      simp [slpAcc, slpAccG, hstep]
    rw [hacc]
    refine ih _ (fun k hk => ?_)
    obtain ⟨g0, g1, g2⟩ := hv (k + 1) (by simp; omega)
    simp only [List.getElem_cons_succ] at g0 g1 g2
    have hl : (slpAccG S init ins).length = init.length + 1 := by simp [slpAccG]
    rw [hl]
    exact ⟨g0, fun h => by have := g1 h; omega, fun h => by have := g2 h; omega⟩

/-- **The evaluator's values are the program's values in `G`, encoded.** -/
theorem slpVals_map_encIn (S : List G) (prog : List RawSLPInstr)
    (hv : SLPValid n (S.map encIn) prog) :
    slpVals (S.map encIn) prog = (slpValsG S prog).map encIn := by
  have := slpVals_encIn S prog [] (fun k hk => by
    obtain ⟨h0, h1, h2⟩ := hv.2 k hk
    exact ⟨fun h => by simpa using h0 h, fun h => by simpa using h1 h,
      fun h => by simpa using h2 h⟩)
  simpa using this

end Raw

/-! ## The hypothesis: the program computes `Iso_{G^Δ}(x^Δ, y^Δ)` -/

section Correct

variable {A : Type*} {n : ℕ}

/-- The generators of `G = ⟨gens⟩` as elements of `G`. -/
def gensIn (gens : List (Perm (Fin n))) : List (genGroup gens) :=
  gens.attach.map (fun g => ⟨g.1, Subgroup.subset_closure g.2⟩)

theorem gensIn_map_encIn (gens : List (Perm (Fin n))) :
    (gensIn gens).map encIn = gens.map (encPerm n) := by
  simp [gensIn, encIn, List.map_attach_eq_pmap]

/-- **"A straight-line program that computes `Iso_{G^Δ}(x^Δ, y^Δ)`"** (Observation 11.1.11,
with Definition 11.1.10).  Without a program the set is empty.  With the program
`(prog, σ)`: the instructions are valid for the generators, and in the sequence `W` they form
in `G^Δ` from the restrictions of the generators, the marked elements generate
`Aut_{G^Δ}(x^Δ)` ("a subgroup is computed if a set of generators of the subgroup is
computed") and element `σ` lies in `Iso_{G^Δ}(x^Δ, y^Δ)` ("a coset is computed if the
corresponding subgroup and a coset representative are computed"). -/
def SLPComputesWindowIso (gens : List (Perm (Fin n))) {Δ : List ℕ}
    (hinv : Babai.IsInvariant (genGroup gens) (winSet n Δ)) (x y : Fin n → A) :
    Option RawSLP → Prop
  | none =>
      Babai.strIso ((Babai.restrictTo (genGroup gens) (winSet n Δ) hinv :
          Subgroup (Perm (winSet n Δ))) : Set (Perm (winSet n Δ)))
        (fun u : winSet n Δ => x (u : Fin n)) (fun u : winSet n Δ => y (u : Fin n)) = ∅
  | some (prog, σ) =>
      SLPValid n (gens.map (encPerm n)) prog ∧ σ < prog.length ∧
      Subgroup.closure {w | w ∈ slpMarkedOf prog
          (slpValsG ((gensIn gens).map (Babai.restrictHom (genGroup gens) (winSet n Δ) hinv))
            prog)} =
        Babai.strAutSubgroup (Babai.restrictTo (genGroup gens) (winSet n Δ) hinv)
          (fun u : winSet n Δ => x (u : Fin n)) ∧
      (slpValsG ((gensIn gens).map (Babai.restrictHom (genGroup gens) (winSet n Δ) hinv))
          prog).getD σ 1 ∈
        Babai.strIso ((Babai.restrictTo (genGroup gens) (winSet n Δ) hinv :
            Subgroup (Perm (winSet n Δ))) : Set (Perm (winSet n Δ)))
          (fun u : winSet n Δ => x (u : Fin n)) (fun u : winSet n Δ => y (u : Fin n))

/-- The kernel of the restriction to `Δ`, as a subgroup of `S(Ω)`, is the pointwise
stabilizer of `Δ` in `G` ("the kernel of the `G`-action on `Δ`"). -/
theorem map_ker_restrictHom (G : Subgroup (Perm (Fin n))) (D : Set (Fin n))
    (hinv : Babai.IsInvariant G D) :
    (Babai.restrictHom G D hinv).ker.map G.subtype = Babai.pointwiseStabilizer G D := by
  ext g
  constructor
  · rintro ⟨⟨g, hg⟩, hk, rfl⟩
    refine ⟨hg, fun u hu => ?_⟩
    have := congrArg (fun p : Perm D => (p ⟨u, hu⟩ : Fin n)) (MonoidHom.mem_ker.1 hk)
    exact this
  · rintro ⟨hg, hfix⟩
    refine ⟨⟨g, hg⟩, MonoidHom.mem_ker.2 (Equiv.ext fun u => Subtype.ext (hfix u u.2)), rfl⟩

/-- **Observation 11.1.11, the answer.**  If the program computes `Iso_{G^Δ}(x^Δ, y^Δ)`, the
answer of the evaluator (the marked elements with their tails, the generators of the kernel
of the `G`-action on `Δ`, and element `σ` with its tail) describes `Iso^Δ_G(x, y)`. -/
theorem decCoset_obsWindow {dom : List ℕ} (hdom : dom.length = n)
    (gens : List (Perm (Fin n))) {Δ : List ℕ} (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    (hinv : Babai.IsInvariant (genGroup gens) (winSet n Δ)) (x y : Fin n → A)
    (q : Option RawSLP) (hq : SLPComputesWindowIso gens hinv x y q) :
    decCoset n (obsWindow (((dom, gens.map (encPerm n)), Δ), q)) =
      Babai.wIso (winSet n Δ) (genGroup gens : Set (Perm (Fin n))) x y := by
  set θ := Babai.restrictHom (genGroup gens) (winSet n Δ) hinv with hθ
  cases q with
  | none =>
    show (∅ : Set (Perm (Fin n))) = _
    exact ((Babai.strIso_restrict_eq_empty_iff hinv x y).1 hq).symm
  | some q =>
    obtain ⟨prog, σ⟩ := q
    obtain ⟨hv, hσ, hgen, hrep⟩ := hq
    set VG := slpValsG (gensIn gens) prog with hVG
    have hW : slpValsG ((gensIn gens).map θ) prog = VG.map θ := (slpValsG_map θ _ prog).symm
    rw [hW] at hgen hrep
    have hv' : SLPValid n ((gensIn gens).map encIn) prog := by
      rw [gensIn_map_encIn]; exact hv
    have hraw : slpVals (gens.map (encPerm n)) prog = VG.map encIn := by
      rw [← gensIn_map_encIn]; exact slpVals_map_encIn _ prog hv'
    have hlenV : VG.length = prog.length := by
      have := congrArg List.length hraw
      simpa using this.symm
    -- the representative
    set g₀ : genGroup gens := VG.getD σ 1 with hg₀
    have hrep' : θ g₀ ∈ Babai.strIso ((Babai.restrictTo (genGroup gens) (winSet n Δ) hinv : Subgroup (Perm (winSet n Δ))) :
        Set (Perm (winSet n Δ))) (fun u : winSet n Δ => x (u : Fin n)) (fun u : winSet n Δ => y (u : Fin n)) := by
      rw [hg₀, ← getD_map_hom]; exact hrep
    have hmemIso : (g₀ : Perm (Fin n)) ∈ Babai.wIso (winSet n Δ) ((genGroup gens : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) x y :=
      (Babai.mem_wIso_iff_restrict hinv x y g₀.2).2 hrep'
    have hrawrep : (slpVals (gens.map (encPerm n)) prog).getD σ [] = encIn g₀ := by
      rw [hraw, List.getD_eq_getElem _ _ (by simpa [hlenV] using hσ), List.getElem_map, hg₀,
        List.getD_eq_getElem _ _ (by omega)]
    -- the group
    set M := slpMarkedOf prog VG with hM
    have hmarked : slpMarked (gens.map (encPerm n)) prog = M.map encIn := by
      rw [slpMarked_eq, hraw, slpMarkedOf_map]
    have hstab : decGroup n (rawPointStab ((dom, gens.map (encPerm n)), Δ)) =
        Babai.pointwiseStabilizer (genGroup gens) (winSet n Δ) := decGroup_rawPointStab dom hdom gens Δ hnd hlt
    have hMdec : decGroup n (M.map encIn) =
        Subgroup.closure ((genGroup gens).subtype '' {s | s ∈ M}) := by
      rw [decGroup, genGroup, List.map_map]
      congr 1
      ext z
      simp only [Set.mem_setOf_eq, List.mem_map, Set.mem_image, Function.comp_apply, encIn,
        decPerm_encPerm, Subgroup.coe_subtype]
    have hS : Subgroup.closure (θ '' {s | s ∈ M}) =
        Babai.strAutSubgroup (Babai.restrictTo (genGroup gens) (winSet n Δ) hinv) (fun u : winSet n Δ => x (u : Fin n)) := by
      rw [← hgen, hM, slpMarkedOf_map]
      congr 1
      ext w
      simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_map]
    have hobs := Babai.Observation_11_1_11_generators hinv x {s | s ∈ M} hS
    have hgrp : decGroup n (M.map encIn ++ rawPointStab ((dom, gens.map (encPerm n)), Δ)) =
        Babai.wAutSubgroup (genGroup gens) (winSet n Δ) hinv x := by
      rw [decGroup_append, hMdec, hstab, ← map_ker_restrictHom _ _ hinv, ← hθ]
      have hle : Babai.wAutSubgroup (genGroup gens) (winSet n Δ) hinv x ≤ genGroup gens :=
        fun g hg => hg.1
      calc Subgroup.closure ((genGroup gens).subtype '' {s | s ∈ M}) ⊔
            θ.ker.map (genGroup gens).subtype
          = (Subgroup.closure {s | s ∈ M} ⊔ θ.ker).map (genGroup gens).subtype := by
            rw [Subgroup.map_sup, MonoidHom.map_closure]
        _ = (Subgroup.closure ({s | s ∈ M} ∪ (θ.ker : Set (genGroup gens)))).map
            (genGroup gens).subtype := by
            rw [Subgroup.closure_union, Subgroup.closure_eq]
        _ = ((Babai.wAutSubgroup (genGroup gens) (winSet n Δ) hinv x).subgroupOf
            (genGroup gens)).map (genGroup gens).subtype := by rw [hobs]
        _ = _ := by rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hle]
    -- the coset
    show decCoset n (some (slpMarked (gens.map (encPerm n)) prog ++
      rawPointStab ((dom, gens.map (encPerm n)), Δ),
      (slpVals (gens.map (encPerm n)) prog).getD σ [])) = _
    rw [hmarked, hrawrep, Babai.wIso_eq_smul_wAut_one hinv hmemIso]
    ext τ
    rw [Babai.mem_perm_smul_set]
    simp only [decCoset, Set.mem_setOf_eq, hgrp, encIn, decPerm_encPerm]
    constructor
    · rintro ⟨g, hg, rfl⟩
      simpa using hg
    · intro h
      exact ⟨_, h, by simp⟩

end Correct

/-! ## Observation 11.1.11 on the RAM -/

/-- **Observation 11.1.11** (Reducing to the window), §11.1, on the RAM.  There is a program
that, on the group `G = ⟨gens⟩ ≤ S(Ω)` with `|Ω| = n`, a `G`-invariant window `Δ`, and a
straight-line program of length `ℓ` that computes `Iso_{G^Δ}(x^Δ, y^Δ)`, outputs a
description of `Iso^Δ_G(x, y)` in time `C (n + 1)(ℓ + 1) + p(size of the group and the
window)`, `p` a polynomial.

The paper's `O(nℓ) + poly(n)`: the `C (n + 1)(ℓ + 1)` is the evaluation of the program on full
permutations of `Ω`, kept in random-access arrays; the polynomial part is the kernel of the
`G`-action on `Δ` and the reading of the input, and it is polynomial in the size of the list
of generators (which the paper takes to be `poly(n)`). -/
theorem Observation_11_1_11_ram : ∃ (P : RAM.Program) (C : ℕ) (p : ℕ → ℕ), RAM.PolyBound p ∧
    ∀ {A : Type*} {n : ℕ} (dom : List ℕ), dom.length = n → ∀ (gens : List (Perm (Fin n)))
      (Δ : List ℕ), Δ.Nodup → (∀ u ∈ Δ, u < n) →
      ∀ (hinv : Babai.IsInvariant (genGroup gens) (winSet n Δ)) (x y : Fin n → A)
      (q : Option RawSLP), SLPComputesWindowIso gens hinv x y q →
      decCoset n (obsWindow (((dom, gens.map (encPerm n)), Δ), q)) =
          Babai.wIso (winSet n Δ) (genGroup gens : Set (Perm (Fin n))) x y ∧
        RAM.RunsOn 16 P (((dom, gens.map (encPerm n)), Δ), q)
          (obsWindow (((dom, gens.map (encPerm n)), Δ), q))
          (C * ((n + 1) * (SLPRAM.slpLen (obsHdr ((dom, gens.map (encPerm n)), Δ), q) + 1)) +
            p (RAM.Enc.size ((dom, gens.map (encPerm n)), Δ))) := by
  obtain ⟨P, C, p, hp, hrun⟩ := SLPRAM.obsWindow_runsOn
  refine ⟨P, C, p, hp, fun {A n} dom hdom gens Δ hnd hlt hinv x y q hq => ⟨decCoset_obsWindow
    hdom gens hnd hlt hinv x y q hq, ?_⟩⟩
  have hok : SLPRAM.SLPInputOK (obsHdr ((dom, gens.map (encPerm n)), Δ), q) := by
    cases q with
    | none => trivial
    | some q =>
      obtain ⟨prog, σ⟩ := q
      obtain ⟨hv, hσ, -⟩ := hq
      refine ⟨?_, hσ⟩
      show SLPValid dom.length (gens.map (encPerm n)) prog
      rw [hdom]; exact hv
  have := hrun (((dom, gens.map (encPerm n)), Δ), q) hok
  subst hdom
  exact this

end Algo
