/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, line 4b: the strings as edge-colored `t`-uniform hypergraphs on `Γ`.
-/
import Workspace.Master.Case3
import Workspace.TopAction.Align

/-!
# `H(x)`: the string of the primitive case as an edge-colored hypergraph

> 4b. else (: `t ≥ 2` :) view `x, y` as edge-colored `t`-uniform hypergraphs `H(x)` and
>     `H(y)` on vertex set `Γ`

Line 4 is the **primitive case**, `Ω = Φ`: the standard blocks of line 3 are singletons, so
the window is the set of standard blocks, which Theorem 10.5.1 (e) identifies with the
`t`-subsets of `Γ` — and `G` acts on it through `ϕ`, as `S(Γ)^{(t)}` or `A(Γ)^{(t)}`.

`Babai.PrimitiveCaseId` is that identification, with the equivariance it carries.  Given
it, a string `x : Ω → Σ` **is** an assignment of a color to each `t`-subset of `Γ`, that
is, an edge-colored `t`-uniform hypergraph `H(x)` on the vertex set `Γ`
(`Babai.hyperColoring`), and the identity

> `H(x^σ) = H(x)^{σ^ϕ}`

holds (`Babai.hyperColoring_strAct`).  That identity is `Babai.IsCanonicalColoring` for the
vertex set `Γ^{(t)}` and the representation `t ∘ ϕ`
(`Babai.isCanonicalColoring_hyperColoring`), which is the form lines 4b and 4c need: line 4b
feeds it to Cor. 12.0.10, and line 4c feeds it to the Extended Design Lemma as a `t`-ary
relational structure.

This is piece (i) of Mismatch 2 in `Workspace/Master/DESIGN.md`.  Pieces (ii)
(`FindsAtMultCost → Vers`) and (iii) (the outcome as the list of color classes of
Procedure Align) were closed later (`Babai.exists_canonicalVersions_of_uniform`,
`Babai.alignColor`).
-/

namespace Babai

open MulAction Equiv Equiv.Perm

variable {Ω Γ A : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Equiv.Perm Ω)}

/-- §15, line 4 (*"if `G` primitive (: i.e. `Ω = Φ` :)"*) together with line 3: the window
is the set of standard blocks `Φ = {B_T | T ∈ Γ^{(t)}}`, and `G` acts on it through `ϕ`.

The first two fields are Theorem 10.5.1 (e): the labelling of the standard blocks by the
`t`-subsets of `Γ`, and the fact that `σ ∈ G` permutes the labels as `σ^ϕ` does.

The third field is Theorem 10.5.1 (a) for the same `t`.  Line 3 of Sec. 15 reads *"let
`Φ = {B_T | T ∈ Γ^{(t)}}` be the set of standard blocks (Thm. 10.5.1)"*, so the paper's `t`
is the number `t_Δ = |T(u)|` of Theorem 10.5.1 (c), and item (a) of the same theorem says
`4|T(u)| < k`. The definition `Babai.IsJohnsonCase` carries `1 ≤ t` and `2*t ≤ m`.
The stronger bound `4*t < m` comes from Theorem 10.5.1 for the standard-block labelling,
so it travels with that labelling. Line 4c needs it (`Babai.LargeDefectData.four_t`). -/
structure PrimitiveCaseId (ϕ : G →* Equiv.Perm Γ) (t : ℕ) where
  /-- The labelling `Ω = Φ → Γ^{(t)}` of Theorem 10.5.1 (e). -/
  label : Ω ≃ binom Γ t
  /-- Eq. (54): `T(u^σ) = T(u)^{σ^ϕ}`. -/
  equivariant : ∀ (σ : G) (u : Ω),
    label ((σ : Equiv.Perm Ω) u) = tAction t (ϕ σ) (label u)
  /-- Theorem 10.5.1 (a): `4|T(u)| < k`, for the parameter `t = t_Δ` of the standard
  blocks. -/
  four_t : 4 * t < Fintype.card Γ
  /-- Theorem 10.5.1 (c) and (e): line 4's test *"`G` primitive (: i.e. `Ω = Φ` :)"* says
  that the point `u` **is** the standard block `B_{T(u)}`, so the label of `u` is its own
  `T(u)`.  This is the same reading of the labelling that `four_t` records: the `t` of the
  labelling is the `t_Δ = |T(u)|` of Theorem 10.5.1 (c).  It is what tells the color classes
  of `Ω` (§14.1, line 4) that every label has `t` points. -/
  label_eq : ∀ u : Ω, ((label u : Finset Γ) : Set Γ) = TpointOf ϕ u

variable {ϕ : G →* Equiv.Perm Γ} {t : ℕ}

/-- §15, lines 3 and 4: in the primitive case every label `T(u)` has `t` points, which is
Theorem 10.5.1 (c) for the `t` of the labelling. -/
theorem PrimitiveCaseId.tPointOf_eq {k : ℕ} {ψ : G →* Equiv.Perm (Fin k)}
    (id : PrimitiveCaseId ψ t) (u : Ω) : tPoint ψ u = t := by
  have h : Tpoint ψ u = ((id.label u : Finset (Fin k)) : Set (Fin k)) := (id.label_eq u).symm
  rw [tPoint, h, Set.ncard_coe_finset]
  exact (id.label u).2

/-- §15, line 4b: **`H(x)`**, the string `x` read as an edge coloring of the `t`-uniform
hypergraph on the vertex set `Γ`: the color of the edge `T ∈ Γ^{(t)}` is the letter that
`x` carries at the standard block labelled `T`. -/
def hyperColoring (id : PrimitiveCaseId ϕ t) (x : Ω → A) : binom Γ t → A :=
  fun T => x (id.label.symm T)

/-- The labelling carries the action of `G` on `Ω` to the action on `t`-subsets: the
inverse form of `Babai.PrimitiveCaseId.equivariant`. -/
theorem PrimitiveCaseId.label_symm_tAction (id : PrimitiveCaseId ϕ t) (σ : G)
    (T : binom Γ t) :
    id.label.symm (tAction t (ϕ σ) T) = (σ : Equiv.Perm Ω) (id.label.symm T) := by
  have h := id.equivariant σ (id.label.symm T)
  rw [Equiv.apply_symm_apply] at h
  exact id.label.symm_apply_eq.2 h.symm

/-- §15, line 4b: **`H(x^σ) = H(x)^{σ^ϕ}`**.  The edge coloring moves with the string: the
color of `T^{σ^ϕ}` in `H(x^σ)` is the color of `T` in `H(x)`.

*Proof.*  The label of the block `u^σ` is `T(u)^{σ^ϕ}` (Eq. (54)), and `x^σ(u^σ) = x(u)`
(Eq. (55)). -/
theorem hyperColoring_strAct (id : PrimitiveCaseId ϕ t) (x : Ω → A) (σ : G)
    (T : binom Γ t) :
    hyperColoring id (strAct x (σ : Equiv.Perm Ω)) (tAction t (ϕ σ) T) =
      hyperColoring id x T := by
  rw [hyperColoring, hyperColoring, id.label_symm_tAction σ T, strAct_apply]

/-- §15, line 4b: `x ↦ H(x)` is a **canonical coloring** of the vertex set `Γ^{(t)}` for the
representation `σ ↦ (σ^ϕ)^{(t)}`, in the sense of `Babai.IsCanonicalColoring`.  This is the
hypothesis `hcol` of Cor. 12.0.10, for the top action on the `t`-subsets. -/
theorem isCanonicalColoring_hyperColoring (id : PrimitiveCaseId ϕ t) :
    IsCanonicalColoring ((tAction (Ω := Γ) t).comp ϕ) (hyperColoring (A := A) id) :=
  fun x σ T => hyperColoring_strAct id x σ T

end Babai
