/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 13.1: Notations 13.1.9 and 13.1.10, Proposition 13.1.11 (Comparing local
certificates) and Procedure Recompute H(W) and Q.
-/
import Workspace.LocalCertificates.Window
import Workspace.LocalCertificates.Calls

/-!
# §13.1 Comparing local certificates

Notation 13.1.9 (truncation of strings, `Babai.truncate`), Notation 13.1.10 (coloring of
strings, `Babai.colorByFace`), Proposition 13.1.11 and Procedure Recompute `H(W)` and `Q`.

The paired procedure runs Procedure LocalCertificates on `(x, T)` and on `(x', T')`
simultaneously and maintains, besides the two windows and the two groups, the set

> `Q = {σ ∈ Iso_G(x^W, (x')^{W'}) | σ carries T to T'}`.

Lines 04c1–04f2 replace the coset decomposition Eq. (69) of `H(W_old)` by the
corresponding decomposition of the coset `Q_old = H(W_old)π₀`; this is
`Babai.smul_eq_69` and `Babai.recomputeQ_eq` below. The counted paired loop and its
run theorem are in `ComparePaired.lean`; its invariant is proved in
`CompareInvariant.lean` and its output transport in `CompareCanonical.lean`.
-/

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise
open scoped Classical

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Equiv.Perm Ω)}

/-! ### Notations 13.1.9 and 13.1.10 -/

/-- **Notation 13.1.9** (Truncation of strings), §13.1.

> Let `∗` be a special symbol not in the alphabet `Σ`.  For the string `x : Ω → Σ` and
> "window" `W ⊆ Ω` we define the string `x^W : Ω → (Σ ∪ {∗})` by setting `x^W(u) = x(u)`
> for `u ∈ W` and `x^W(u) = ∗` for `u ∈ Ω ∖ W`.

The alphabet `Σ ∪ {∗}` is `Option Λ`, with `∗ = none`. -/
noncomputable def truncate (x : Ω → Λ) (W : Set Ω) : Ω → Option Λ :=
  fun u => if u ∈ W then some (x u) else none

@[simp] theorem truncate_of_mem {x : Ω → Λ} {W : Set Ω} {u : Ω} (h : u ∈ W) :
    truncate x W u = some (x u) := if_pos h

@[simp] theorem truncate_of_not_mem {x : Ω → Λ} {W : Set Ω} {u : Ω} (h : u ∉ W) :
    truncate x W u = none := if_neg h

/-- **Notation 13.1.10** (Coloring of strings), §13.1.

> For the string `x : Ω → Σ` and the test set `T ⊆ Γ` we define the string
> `x_T : Ω → (Σ × {0,1})` by setting `x_T(u) = (x(u), 1)` if `u ∈ Ω(T)` and
> `x_T(u) = (x(u), 0)` if `u ∉ Ω(T)`.

`{0,1}` is `Bool`, and `Ω(T)` is the face of Section 12 (`Babai.face`). -/
noncomputable def colorByFace (ϕ : G →* Equiv.Perm Γ) (x : Ω → Λ) (T : Set Γ) :
    Ω → Λ × Bool :=
  fun u => (x u, decide (u ∈ face ϕ T))

/-! ### Procedure Recompute `H(W)` and `Q` -/

section Recompute

variable {ϕ : G →* Equiv.Perm Γ} {x : Ω → Λ} {T : Set Γ}

/-- Eq. (69) translated by `π₀`: the coset `Q_old = H(W_old)π₀` is the union of the cosets
`Nπ` with `π = σπ₀` (lines 04c1, 04d1, 04d2).  In Lean's convention the paper's right
coset `Kπ` is `π • K` (see the header of `Workspace/Luks/Defs.lean`), and the paper's
product `σπ₀` is `π₀ * σ`. -/
theorem smul_eq_69 (s : Stage ϕ x T) (lift : imgOn ϕ T s.le → Equiv.Perm Ω)
    (hlift : ∀ sb, ∃ h : lift sb ∈ s.H, psiOn ϕ T s.le ⟨lift sb, h⟩ = (sb : Equiv.Perm T))
    (π₀ : Equiv.Perm Ω) :
    π₀ • (s.H : Set (Equiv.Perm Ω))
      = ⋃ sb : imgOn ϕ T s.le, (π₀ * lift sb) • (kerN s : Set (Equiv.Perm Ω)) := by
  rw [eq_69 s lift hlift, Set.smul_set_iUnion]
  refine Set.iUnion_congr fun sb => ?_
  rw [smul_smul]

/-- Lines 04b2–04f2 of Procedure Recompute `H(W)` and `Q`: the set `R` collected by the
loop is the set of window isomorphisms in the old coset `Q_old = H(W_old)π₀`, split into
the cosets `Nπ`.

This is the justification of the procedure ("The analysis is analogous with the analysis
of the Recompute `H(W)` routine"): the `for` loop of line 04c1 runs over the `≤ t!`
elements of `H(W_old)^T` and, for each, solves one String Isomorphism problem on the
coset `Nπ`; the union of the answers is the set of isomorphisms in `Q_old`. -/
theorem recomputeQ_eq (s : Stage ϕ x T) (lift : imgOn ϕ T s.le → Equiv.Perm Ω)
    (hlift : ∀ sb, ∃ h : lift sb ∈ s.H, psiOn ϕ T s.le ⟨lift sb, h⟩ = (sb : Equiv.Perm T))
    (π₀ : Equiv.Perm Ω) {A : Type*} (W' : Set Ω) (y y' : Ω → A) :
    wIso W' (π₀ • (s.H : Set (Equiv.Perm Ω))) y y'
      = ⋃ sb : imgOn ϕ T s.le,
          wIso W' ((π₀ * lift sb) • (kerN s : Set (Equiv.Perm Ω))) y y' := by
  rw [smul_eq_69 s lift hlift π₀]
  ext τ
  simp only [mem_wIso, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨sb, hsb⟩, hresp⟩
    exact ⟨sb, hsb, hresp⟩
  · rintro ⟨sb, hsb, hresp⟩
    exact ⟨⟨sb, hsb⟩, hresp⟩

end Recompute

/-! ### Proposition 13.1.11 -/

variable (ϕ : G →* Equiv.Perm Γ) (x x' : Ω → Λ) (T T' : Set Γ)

/-- The set `Q` maintained by the paired procedure, at the stage where both loops have
exited: `Iso_G(x_T^{W(T)}, (x')_{T'}^{W'(T')})`, the object Proposition 13.1.11 computes.

The two truncated and colored strings take their letters in `Option (Λ × Bool)`. -/
noncomputable def compareIso : Set (Equiv.Perm Ω) :=
  strIso (G : Set (Equiv.Perm Ω))
    (truncate (colorByFace ϕ x T) (windowOut ϕ x T))
    (truncate (colorByFace ϕ x' T') (windowOut ϕ x' T'))

/-- The set returned by the paired procedure: the `G`-isomorphisms of the two truncated,
colored strings that lie in the coset `G_Tσ₀` with which line 01 initializes `Q`.  (`Q`
only ever shrinks from its initial value `G_Tσ₀`, by imposing isomorphism conditions on
the windows reached.) -/
noncomputable def pairQOut (σ₀ : Equiv.Perm Ω) : Set (Equiv.Perm Ω) :=
  strIso (σ₀ • (bigGT ϕ T : Set (Equiv.Perm Ω)))
    (truncate (colorByFace ϕ x T) (windowOut ϕ x T))
    (truncate (colorByFace ϕ x' T') (windowOut ϕ x' T'))

/-- What an element `σ` of `Iso_G(x_T^{W(T)}, (x')_{T'}^{W'(T')})` does on the window: it
carries `W(T)` into `W'(T')`, matches the two strings there, and preserves the color bit of
Notation 13.1.10, i.e. `u ∈ Ω(T)` iff `u^σ ∈ Ω(T')`.

This is the first half of the proof of Proposition 13.1.11, isolated because §13.2 uses it
twice more: to see that a morphism of the category `𝓛` really induces a bijection
`T → T'`, and to see that `Aut(T,i) ≤ M_i(T)`. -/
theorem compareIso_window {σ : Equiv.Perm Ω} (hσ : σ ∈ compareIso ϕ x x' T T')
    {u : Ω} (hu : u ∈ windowOut ϕ x T) :
    σ u ∈ windowOut ϕ x' T' ∧ x' (σ u) = x u ∧ (u ∈ face ϕ T ↔ σ u ∈ face ϕ T') := by
  obtain ⟨-, hresp⟩ := hσ
  have h := congrFun hresp (σ u)
  rw [strAct_apply] at h
  rw [truncate_of_mem hu] at h
  by_cases hW' : σ u ∈ windowOut ϕ x' T'
  · rw [truncate_of_mem hW'] at h
    have h2 := Option.some.inj h
    refine ⟨hW', (congrArg Prod.fst h2).symm, ?_⟩
    exact decide_eq_decide.1 (congrArg Prod.snd h2)
  · rw [truncate_of_not_mem hW'] at h
    exact absurd h (by simp)

/-- A `G`-isomorphism of the truncated, `Ω(T)`-colored strings of Notation 13.1.10 carries
the test set `T` to the test set `T'`.

This is the step of the proof of Proposition 13.1.11 that the paper's sketch omits (see
the corrected paper): the color bit forces `Ω(T)^σ = Ω(T')`, Proposition 13.1.8 (i)
(`Babai.face_subset_windowOut`) puts `Ω(T)` inside the window so that the bit is recorded,
`Babai.face_image` gives `Ω(T)^σ = Ω(T^{σ̄})`, and `Babai.face_injective` turns
`Ω(T^{σ̄}) = Ω(T')` into `T^{σ̄} = T'`. -/
theorem compareIso_testImage (hset : LocalCertSetting G ϕ)
    (ht : LargeK T.ncard (Nat.card Ω)) (htm : 10 * T.ncard ≤ Nat.card Γ)
    (hT' : T'.ncard = T.ncard) [Nonempty Ω] {σ : Equiv.Perm Ω}
    (hσ : σ ∈ compareIso ϕ x x' T T') :
    ∃ h : σ ∈ G, (ϕ ⟨σ, h⟩ : Equiv.Perm Γ) '' T = T' := by
  classical
  have h8 : 8 < T.ncard := ht.eight_lt
  have hk : VeryLargeK (Nat.card Γ) (maxOrbitLength G) :=
    veryLargeK_of_setting ϕ hset (by omega)
  have ht2 : LargeK T'.ncard (Nat.card Ω) := by rw [hT']; exact ht
  have htm' : 10 * T'.ncard ≤ Nat.card Γ := by rw [hT']; exact htm
  have hWT : face ϕ T ⊆ windowOut ϕ x T := face_subset_windowOut ϕ x T hset ht htm
  have hWT' : face ϕ T' ⊆ windowOut ϕ x' T' := face_subset_windowOut ϕ x' T' hset ht2 htm'
  obtain ⟨hmemG, hresp⟩ := hσ
  refine ⟨hmemG, ?_⟩
  -- `σ` carries the face of `T` onto the face of `T'`
  have hface : (σ : Equiv.Perm Ω) '' face ϕ T = face ϕ T' := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ((compareIso_window ϕ x x' T T' ⟨hmemG, hresp⟩ (hWT hu)).2.2).1 hu
    · intro hv
      refine ⟨σ⁻¹ v, ?_, by simp⟩
      have hW : σ⁻¹ v ∈ windowOut ϕ x T := by
        by_contra hW
        have h := congrFun hresp v
        rw [show v = σ (σ⁻¹ v) by simp] at h
        rw [strAct_apply, truncate_of_not_mem hW, show σ (σ⁻¹ v) = v by simp,
          truncate_of_mem (hWT' hv)] at h
        exact absurd h.symm (by simp)
      have hbit := (compareIso_window ϕ x x' T T' ⟨hmemG, hresp⟩ hW).2.2
      rw [show σ (σ⁻¹ v) = v by simp] at hbit
      exact hbit.2 hv
  have h1 : (σ : Equiv.Perm Ω) '' face ϕ T = face ϕ ((ϕ ⟨σ, hmemG⟩ : Equiv.Perm Γ) '' T) :=
    face_image ϕ T hset hk ⟨σ, hmemG⟩
  have h2 : face ϕ ((ϕ ⟨σ, hmemG⟩ : Equiv.Perm Γ) '' T) = face ϕ T' := by rw [← h1, hface]
  refine face_injective ϕ T hset hk ht htm ?_ hT' h2
  rw [Set.ncard_image_of_injective _ (ϕ ⟨σ, hmemG⟩ : Equiv.Perm Γ).injective]

/-- `Aut(T) ≤ H(W(T))`, §13.2: a `G`-isomorphism of the truncated, colored string
`x_T^{W(T)}` with itself lies in `H(W(T)) = Aut^{W(T)}_{G_T}(x)`.  Indeed it stabilizes `T`
(`Babai.compareIso_testImage`) and respects `x` on the window
(`Babai.compareIso_window`). -/
theorem compareIso_mem_outStage_H (hset : LocalCertSetting G ϕ)
    (ht : LargeK T.ncard (Nat.card Ω)) (htm : 10 * T.ncard ≤ Nat.card Γ) [Nonempty Ω]
    {σ : Equiv.Perm Ω} (hσ : σ ∈ compareIso ϕ x x T T) : σ ∈ (outStage ϕ x T).H := by
  obtain ⟨hmemG, himg⟩ := compareIso_testImage ϕ x x T T hset ht htm rfl hσ
  have hstab : σ ∈ bigGT ϕ T := mem_stabIn.2 ⟨hmemG, himg⟩
  show σ ∈ ((outStage ϕ x T).H : Set (Equiv.Perm Ω))
  rw [(outStage ϕ x T).isAut]
  exact ⟨hstab, fun u hu => ((compareIso_window ϕ x x T T hσ hu).2.1).symm⟩

/-- The image in `S(T)` of an element of `H(W(T))` lies in `M(T)`. -/
theorem psi_mem_certM {σ : Equiv.Perm Ω} (h : σ ∈ (outStage ϕ x T).H) :
    psi ϕ T ⟨σ, (outStage ϕ x T).le h⟩ ∈ certM ϕ x T :=
  ⟨⟨σ, h⟩, rfl⟩

/-- **Proposition 13.1.11** (Comparing local certificates), §13.1.

> For all test sets `T, T' ⊆ Γ` with `|T| = |T'| = t` and all strings `x, x' : Ω → Σ` we
> can compute `Iso_G(x_T^{W(T)}, (x')_{T'}^{W'(T')})` by making `≤ t!n²` calls to String
> Isomorphism problems on domains of size `≤ n/t` and performing `t! poly(n)` computation.

> Run procedure LocalCertificates simultaneously on `(x, T)` and on `(x', T')`,
> maintaining the variable `W` for `(x, T)` and the variable `W'` for `(x', T')`.  Further
> maintain the set `Q = Iso_G(x_T^W, (x')_{T'}^{W'})`.  On line 01 we shall have
> `Q = G_T σ` for any `σ ∈ G` that takes `T` to `T'`.  Change line 04 to "recompute `H(W)`
> and `Q`."

The mathematical content of the claim is that the procedure's output is the required set
of isomorphisms, i.e. that restricting `Q` to the initial coset `G_Tσ₀` of line 01 loses
no isomorphism of the final truncated strings. The separate-run bounds below do not
count the comparison calls. The paired reduction and its `2 * t! * n²` call bound are
proved in `ComparePaired.lean`. The exact printed constant and the `t! poly(n)` RAM
running time remain open.

The paper's proof sketch states an invariant that is false as printed, and the repaired
invariant is:

> `Q = {σ ∈ Iso_G(x^W, (x')^{W'}) | T^{σ̄} = T'}`

— the *plain* truncated strings together with the condition that `σ` carries the test set
`T` to `T'`.  At line 01 this is `{σ ∈ G | T^{σ̄} = T'} = G_Tσ`, which is what line 01 sets
(the printed invariant, without the condition on `T`, gives all of `G` there, since both
truncated strings are constantly `∗`).  The parallelism of the two runs (`W^σ = W'` for
`σ ∈ Q`), which line 04c0 needs in order to use `Q_old` as a coset of `H(W_old)`, is part
of the induction rather than an assumption: it holds at line 01, and conjugation by
`σ ∈ Q_old` carries `H(W_old) = Aut^{W_old}_{G_T}(x)` to `Aut^{W'_old}_{G_{T'}}(x')`
(using `T^{σ̄} = T'`), hence carries `Aff(H(W_old), ψ_T)` to `Aff(H'(W'_old), ψ_{T'})`.

The statement below is the step *from* that invariant to the set the proposition asks for,
which the sketch omits: the coloring of Notation 13.1.10 encodes the condition
`T^{σ̄} = T'` into the string, so that restricting to the initial coset `G_Tσ₀` loses no
isomorphism of the final colored truncated strings.  Its two ingredients are `Ω(T) ⊆ W(T)`
(Proposition 13.1.8 (i), `Babai.face_subset_windowOut`) and the injectivity of `A ↦ Ω(A)`
on `t`-subsets (`Babai.face_injective`), which comes from the labeling of the standard
blocks by *all* of `(Γ choose t_Δ)` (Theorem 10.5.1 (e)). -/
theorem proposition_13_1_11 (hset : LocalCertSetting G ϕ)
    (ht : LargeK T.ncard (Nat.card Ω)) (htm : 10 * T.ncard ≤ Nat.card Γ)
    (hT' : T'.ncard = T.ncard) [Nonempty Ω]
    (σ₀ : Equiv.Perm Ω) (hσ₀ : σ₀ ∈ G)
    (hmap : (ϕ ⟨σ₀, hσ₀⟩ : Equiv.Perm Γ) '' T = T') :
    pairQOut ϕ x x' T T' σ₀ = compareIso ϕ x x' T T' := by
  classical
  ext σ
  constructor
  · rintro ⟨hmem, hresp⟩
    refine ⟨?_, hresp⟩
    have hκ : σ₀⁻¹ * σ ∈ bigGT ϕ T := mem_perm_smul_set.1 hmem
    have hrw : σ = σ₀ * (σ₀⁻¹ * σ) := by group
    rw [hrw]
    exact G.mul_mem hσ₀ (stabIn_le_top hκ)
  · intro hσ
    refine ⟨?_, hσ.2⟩
    -- `σ^ϕ` carries `T` onto `T'` (`Babai.compareIso_testImage`)
    obtain ⟨hmemG, himg⟩ := compareIso_testImage ϕ x x' T T' hset ht htm hT' hσ
    -- hence `σ₀⁻¹σ ∈ G_T`, i.e. `σ ∈ G_Tσ₀`
    refine mem_perm_smul_set.2 (mem_stabIn.2 ⟨G.mul_mem (G.inv_mem hσ₀) hmemG, ?_⟩)
    have hval : (ϕ ⟨σ₀⁻¹ * σ, G.mul_mem (G.inv_mem hσ₀) hmemG⟩ : Equiv.Perm Γ)
        = (ϕ ⟨σ₀, hσ₀⟩ : Equiv.Perm Γ)⁻¹ * (ϕ ⟨σ, hmemG⟩ : Equiv.Perm Γ) := by
      have he : (⟨σ₀⁻¹ * σ, G.mul_mem (G.inv_mem hσ₀) hmemG⟩ : G)
          = (⟨σ₀, hσ₀⟩ : G)⁻¹ * ⟨σ, hmemG⟩ := Subtype.ext rfl
      rw [he, map_mul, map_inv]
    rw [hval]
    have hsplit : (((ϕ ⟨σ₀, hσ₀⟩ : Equiv.Perm Γ)⁻¹ * (ϕ ⟨σ, hmemG⟩ : Equiv.Perm Γ)) :
        Γ → Γ) '' T
        = ((ϕ ⟨σ₀, hσ₀⟩ : Equiv.Perm Γ)⁻¹ : Equiv.Perm Γ) ''
          (((ϕ ⟨σ, hmemG⟩ : Equiv.Perm Γ) : Γ → Γ) '' T) := by
      rw [← Set.image_comp]; rfl
    rw [hsplit, himg, ← hmap, ← Set.image_comp]
    simp

theorem proposition_13_1_11_calls (h5 : 5 ≤ T.ncard) (h5' : 5 ≤ T'.ncard)
    (lift : ∀ i : ℕ, imgOn ϕ T (stages ϕ x T i).le → Equiv.Perm Ω)
    (hlift : ∀ (i : ℕ) (sb : imgOn ϕ T (stages ϕ x T i).le),
      ∃ h : lift i sb ∈ (stages ϕ x T i).H,
        psiOn ϕ T (stages ϕ x T i).le ⟨lift i sb, h⟩ = (sb : Equiv.Perm T))
    (lift' : ∀ i : ℕ, imgOn ϕ T' (stages ϕ x' T' i).le → Equiv.Perm Ω)
    (hlift' : ∀ (i : ℕ) (sb : imgOn ϕ T' (stages ϕ x' T' i).le),
      ∃ h : lift' i sb ∈ (stages ϕ x' T' i).H,
        psiOn ϕ T' (stages ϕ x' T' i).le ⟨lift' i sb, h⟩ = (sb : Equiv.Perm T')) :
    (allInstances ϕ x T lift hlift).card ≤ Nat.factorial T.ncard * (Nat.card Ω) ^ 2 ∧
      (∀ I ∈ allInstances ϕ x T lift hlift, T.ncard * I.Δ.ncard ≤ Nat.card Ω) ∧
      (allInstances ϕ x' T' lift' hlift').card ≤ Nat.factorial T'.ncard * (Nat.card Ω) ^ 2 ∧
      (∀ I ∈ allInstances ϕ x' T' lift' hlift', T'.ncard * I.Δ.ncard ≤ Nat.card Ω) :=
  ⟨card_allInstances_le lift hlift, fun _ hI => instance_window_le h5 lift hlift hI,
    card_allInstances_le lift' hlift', fun _ hI => instance_window_le h5' lift' hlift' hI⟩

end Babai
