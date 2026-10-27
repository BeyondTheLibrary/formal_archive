/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 10.1 (Simple quotient of subdirect product).
-/
import Workspace.AltQuotients.Defs
import Mathlib.Algebra.Group.Commutator

/-!
# §10.1 Simple quotient of subdirect product

Lemma 10.1.1 with P. P. Pálfy's proof, and the two cited items of the subsection that the
paper never uses (Remark 10.1.2, Lemma 10.1.3).  Lemma 10.1.3 is recorded as a statement
only; the derivation of Lemma 10.1.1 from it in Remark 10.1.2 is proved as an implication
(`Babai.remark_10_1_2_derivation`).

## Pálfy's computation in Lean

The paper writes the proof as a single `m`-fold commutator identity,

> `[G, …, G] = [M₁N, …, M_mN] ≤ N[M₁, …, M_m] ≤ N(⋂ᵢ Mᵢ) = N`, so `[G/N, …, G/N] = 1`.

Lean has no `m`-fold commutator of a family, so the same computation is run as an
induction over a finite set `s` of indices (`Babai.lowerCentralSeries_le_sup_inf_ker`):
the `s.card`-th term of the lower central series of `G` lies in `N ⊔ ⋂_{i ∈ s} Mᵢ`.  Taking
`s = univ` gives `γ_m(G) ≤ N`, i.e. `γ_m(G/N) = 1`, which is the paper's conclusion.  The
two inequalities of the display are the two steps of the induction:
`⁅N ⊔ A, N ⊔ B⁆ ≤ N ⊔ ⁅A, B⁆` and `⁅A, B⁆ ≤ A ⊓ B` for normal `A`, `B`.
-/

universe u

namespace Babai

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

/-! ### Two steps of Pálfy's computation -/

/-- `[M₁N, M₂N] ≤ N[M₁, M₂]`: modulo the normal subgroup `N` the two sups become `A` and
`B`, whose commutator is killed. -/
theorem commutator_sup_le_sup_commutator (N A B : Subgroup G) [N.Normal] [A.Normal]
    [B.Normal] : ⁅N ⊔ A, N ⊔ B⁆ ≤ N ⊔ ⁅A, B⁆ := by
  set T := N ⊔ ⁅A, B⁆ with hTdef
  have hker : (QuotientGroup.mk' T).ker = T := QuotientGroup.ker_mk' T
  rw [← hker, ← Subgroup.map_eq_bot_iff, Subgroup.map_commutator, Subgroup.map_sup,
    Subgroup.map_sup]
  have hN : N.map (QuotientGroup.mk' T) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hker]; exact le_sup_left
  rw [hN, bot_sup_eq, bot_sup_eq, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, hker]
  exact le_sup_right

/-- The intersection of a finite family of normal subgroups is normal. -/
instance finsetInf_normal {ι : Type*} (M : ι → Subgroup G) [∀ i, (M i).Normal]
    (s : Finset ι) : (s.inf M).Normal := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (inferInstance : (⊤ : Subgroup G).Normal)
  | insert a t ha iht =>
      rw [Finset.inf_insert]
      haveI := iht
      infer_instance

/-- The induction that replaces the paper's `m`-fold commutator: for every finite set `s`
of indices, `γ_{|s|}(G) ≤ N ⊔ ⋂_{i ∈ s} Mᵢ`, provided `N ⊔ Mᵢ = ⊤` for each `i`. -/
theorem lowerCentralSeries_le_sup_inf_ker {ι : Type*} [DecidableEq ι] (N : Subgroup G)
    [N.Normal] (M : ι → Subgroup G) [∀ i, (M i).Normal] (hM : ∀ i, N ⊔ M i = ⊤)
    (s : Finset ι) : lowerCentralSeries G s.card ≤ N ⊔ s.inf M := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hcard : (insert a s).card = s.card + 1 := Finset.card_insert_of_notMem ha
      have hinf : (insert a s).inf M = M a ⊓ s.inf M := Finset.inf_insert
      haveI : (s.inf M).Normal := finsetInf_normal M s
      rw [hcard, hinf]
      have hstep : lowerCentralSeries G (s.card + 1) = ⁅lowerCentralSeries G s.card, ⊤⁆ := rfl
      rw [hstep, ← hM a]
      calc ⁅lowerCentralSeries G s.card, N ⊔ M a⁆
          ≤ ⁅N ⊔ s.inf M, N ⊔ M a⁆ := Subgroup.commutator_mono ih le_rfl
        _ ≤ N ⊔ ⁅s.inf M, M a⁆ := commutator_sup_le_sup_commutator _ _ _
        _ ≤ N ⊔ (M a ⊓ s.inf M) :=
            sup_le_sup_left
              (le_inf (Subgroup.commutator_le_right _ _) (Subgroup.commutator_le_left _ _)) N

/-! ### Lemma 10.1.1 -/

/-- **Lemma 10.1.1** (Simple quotient of subdirect product), §10.1.

> Let `G ≤ K₁ × ⋯ × K_m` be a subdirect product; let `Mᵢ` be the kernel of the `G → Kᵢ`
> epimorphism.  Assume there is an epimorphism `ϕ : G → S` where `S` is a nonabelian
> simple group.  Then `(∃i)(Mᵢ ≤ ker ϕ)`.  In particular, one of the `Kᵢ` admits an
> epimorphism onto `S`.

Proof: the simplified proof by P. P. Pálfy given in the paper. -/
theorem lemma_10_1_1 {ι : Type*} [Fintype ι] {K : ι → Type*} [∀ i, Group (K i)]
    {π : ∀ i, G →* K i} (hsub : IsSubdirectProduct π)
    {S : Type*} [Group S] [IsSimpleGroup S] (hSnonab : ¬ ∀ a b : S, a * b = b * a)
    {ϕ : G →* S} (hϕ : Function.Surjective ϕ) :
    ∃ i, (π i).ker ≤ ϕ.ker := by
  classical
  by_contra hcon
  push_neg at hcon
  -- `N = ker ϕ`, `Mᵢ = ker πᵢ`.
  set N := ϕ.ker with hN
  set M : ι → Subgroup G := fun i => (π i).ker with hMdef
  -- "Then `MᵢN = G` (because `N` is a maximal normal subgroup)."
  have hMN : ∀ i, N ⊔ M i = ⊤ := by
    intro i
    have hnormal : ((M i).map ϕ).Normal := Subgroup.Normal.map inferInstance ϕ hϕ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((M i).map ϕ) hnormal with h | h
    · exact absurd ((Subgroup.map_eq_bot_iff _).1 h) (hcon i)
    · have hle : N ≤ N ⊔ M i := le_sup_left
      have hmapsup : (N ⊔ M i).map ϕ = ⊤ := by
        rw [Subgroup.map_sup, h, sup_top_eq]
      have := congrArg (Subgroup.comap ϕ) hmapsup
      rwa [Subgroup.comap_map_eq_self hle, Subgroup.comap_top] at this
  -- "so `[G/N, …, G/N] = 1`"
  have hbot : (⨅ i, M i) = ⊥ := by
    refine le_antisymm (fun g hg => ?_) bot_le
    rw [Subgroup.mem_iInf] at hg
    exact hsub.faithful g (fun i => hg i)
  have hkey := lowerCentralSeries_le_sup_inf_ker N M hMN (Finset.univ : Finset ι)
  rw [Finset.inf_univ_eq_iInf, hbot, sup_bot_eq] at hkey
  -- `γ_m(S) = ϕ(γ_m(G)) ≤ ϕ(N) = 1`
  have hmapγ : ∀ n, (lowerCentralSeries G n).map ϕ = lowerCentralSeries S n := by
    intro n
    induction n with
    | zero => simpa using Subgroup.map_top_of_surjective ϕ hϕ
    | succ n ih =>
        show ((⁅lowerCentralSeries G n, (⊤ : Subgroup G)⁆).map ϕ)
            = ⁅lowerCentralSeries S n, (⊤ : Subgroup S)⁆
        rw [Subgroup.map_commutator, ih, Subgroup.map_top_of_surjective ϕ hϕ]
  -- "a contradiction because `G/N ≅ S` is nonabelian simple"
  have hcomm : commutator S = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) inferInstance with h | h
    · exact absurd (fun a b => by
        have : ⁅a, b⁆ ∈ commutator S :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
        rw [h, Subgroup.mem_bot] at this
        exact (commutatorElement_eq_one_iff_mul_comm.1 this)) hSnonab
    · exact h
  have hγS : ∀ n, lowerCentralSeries S n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        have hs : lowerCentralSeries S (n + 1) = ⁅lowerCentralSeries S n, (⊤ : Subgroup S)⁆ :=
          rfl
        rw [hs, ih, ← _root_.commutator_def]
        exact hcomm
  have htop : (⊤ : Subgroup S) = ⊥ := by
    have h1 : (lowerCentralSeries G (Fintype.card ι)).map ϕ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff _]
      simpa [hN] using hkey
    rw [hmapγ, hγS] at h1
    exact h1
  exact hSnonab (fun a b => by
    have ha : a = 1 := by
      have : a ∈ (⊥ : Subgroup S) := htop ▸ Subgroup.mem_top a
      simpa using this
    have hb : b = 1 := by
      have : b ∈ (⊥ : Subgroup S) := htop ▸ Subgroup.mem_top b
      simpa using this
    simp [ha, hb])

/-- **Lemma 10.1.1**, the concluding sentence, §10.1: "In particular, one of the `Kᵢ`
admits an epimorphism onto `S`." -/
theorem lemma_10_1_1_epi {ι : Type*} [Fintype ι] {K : ι → Type*} [∀ i, Group (K i)]
    {π : ∀ i, G →* K i} (hsub : IsSubdirectProduct π)
    {S : Type*} [Group S] [IsSimpleGroup S] (hSnonab : ¬ ∀ a b : S, a * b = b * a)
    {ϕ : G →* S} (hϕ : Function.Surjective ϕ) :
    ∃ (i : ι) (ψ : K i →* S), Function.Surjective ψ := by
  obtain ⟨i, hi⟩ := lemma_10_1_1 hsub hSnonab hϕ
  refine ⟨i, (QuotientGroup.lift (π i).ker ϕ hi).comp
    (QuotientGroup.quotientKerEquivOfSurjective (π i) (hsub.surjective i)).symm.toMonoidHom, ?_⟩
  intro s
  obtain ⟨g, rfl⟩ := hϕ s
  refine ⟨π i g, ?_⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [show (QuotientGroup.quotientKerEquivOfSurjective (π i) (hsub.surjective i)).symm (π i g)
      = (QuotientGroup.mk g : G ⧸ (π i).ker) from ?_]
  · rfl
  · rw [MulEquiv.symm_apply_eq]
    rfl

/-! ### Remark 10.1.2 and Lemma 10.1.3, cited and unused -/

/-- A *subnormal* subgroup: `R = R₀ ⊴ R₁ ⊴ ⋯ ⊴ R_n = G`.  Needed only to state Lemma
10.1.3. -/
def IsSubnormal (R : Subgroup G) : Prop :=
  ∃ (n : ℕ) (c : ℕ → Subgroup G), c 0 = R ∧ c n = ⊤ ∧
    (∀ i < n, c i ≤ c (i + 1)) ∧ ∀ i < n, ((c i).subgroupOf (c (i + 1))).Normal

/-- **Remark 10.1.2**, §10.1.

> A group `H` is *perfect* if `H' = H` (where `H' = [H, H]` denotes the commutator
> subgroup of `H`).  Pálfy points out that the following result appears as Lemma 2.8 in
> [Me].

This is the definition of a perfect group; the rest of the remark is the pointer to
`[Me]` (Lemma 10.1.3 below). -/
def IsPerfectGroup (H : Type*) [Group H] : Prop := commutator H = ⊤

/-- **Lemma 10.1.3** (Meierfrankenfeld), §10.1.

> Let `G` be a finite group and `N ⊴ G` such that `G/N` is perfect.  Then there exists a
> unique subnormal subgroup `R` of `G` which is minimal with respect to `G = RN`.

Cited by the paper (Remark 10.1.2: "this result appears as Lemma 2.8 in [Me]") as an
alternative route to Lemma 10.1.1, which the paper proves in full.  It is used in **no**
proof of the paper, so it gets no axiom and is recorded as a statement only. -/
-- CITED: Ulrich Meierfrankenfeld, Lemma 2.8 of [Me] (1995); pointed out by P. P. Pálfy.
def Lemma_10_1_3_statement : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (N : Subgroup G) [N.Normal],
    commutator (G ⧸ N) = ⊤ →
      ∃! R : Subgroup G, IsSubnormal R ∧ R ⊔ N = ⊤ ∧
        ∀ R' : Subgroup G, IsSubnormal R' → R' ⊔ N = ⊤ → R' ≤ R → R' = R


/-- A normal subgroup is subnormal (the chain `M ⊴ G`). -/
theorem isSubnormal_of_normal {M : Subgroup G} [M.Normal] : IsSubnormal M := by
  refine ⟨1, fun j => if j = 0 then M else ⊤, by simp, by simp, ?_, ?_⟩
  · intro i hi
    have : i = 0 := by omega
    subst this
    simp
  · intro i hi
    have : i = 0 := by omega
    subst this
    simp only [↓reduceIte, one_ne_zero]
    infer_instance

/-- A nonabelian simple group is perfect, and so is every group isomorphic to it: the
commutator subgroup of `G/ker ϕ` is everything when `ϕ : G → S` is onto a nonabelian simple
group `S`. -/
theorem commutator_quotient_ker_eq_top {S : Type*} [Group S] [IsSimpleGroup S]
    (hSnonab : ¬ ∀ a b : S, a * b = b * a) {ϕ : G →* S} (hϕ : Function.Surjective ϕ) :
    commutator (G ⧸ ϕ.ker) = ⊤ := by
  have hS : commutator S = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) inferInstance with h | h
    · exfalso
      apply hSnonab
      intro a b
      have hc : IsMulCommutative S := (commutator_eq_bot_iff (G := S)).1 h
      exact hc.is_comm.comm a b
    · exact h
  set f : S →* G ⧸ ϕ.ker := (QuotientGroup.quotientKerEquivOfSurjective ϕ hϕ).symm.toMonoidHom
  have hf : Function.Surjective f := (QuotientGroup.quotientKerEquivOfSurjective ϕ hϕ).symm.surjective
  have htop : (⊤ : Subgroup S).map f = ⊤ := Subgroup.map_top_of_surjective f hf
  calc commutator (G ⧸ ϕ.ker) = ⁅(⊤ : Subgroup (G ⧸ ϕ.ker)), ⊤⁆ := rfl
    _ = ⁅(⊤ : Subgroup S).map f, (⊤ : Subgroup S).map f⁆ := by rw [htop]
    _ = (commutator S).map f := (Subgroup.map_commutator _ _ f).symm
    _ = ⊤ := by rw [hS, htop]

/-- **Remark 10.1.2**, §10.1, the derivation:

> Lemma 10.1.1 follows from this result [Lemma 10.1.3].  Indeed, observe that if
> `MᵢN = G` for all `i` then `R ≤ Mᵢ` for all `i` and therefore `R ≤ ⋂ᵢ Mᵢ = 1`,
> contradicting the equation `RN = G`.

Stated as an implication from the statement of Lemma 10.1.3 (which is cited, unused and has
no axiom) to Lemma 10.1.1, for a finite group `G`, as Lemma 10.1.3 requires.  `G/N` is
perfect because it is isomorphic to the nonabelian simple group `S`
(`Babai.commutator_quotient_ker_eq_top`).

The step "`R ≤ Mᵢ`", which the remark leaves to the reader, uses the uniqueness in
Lemma 10.1.3: since `Mᵢ` is normal, hence subnormal, and `MᵢN = G`, a subnormal subgroup
`R'` of least order among those with `R' ≤ Mᵢ` and `R'N = G` exists; it is minimal among
*all* subnormal subgroups with `R'N = G` (any smaller one also lies in `Mᵢ`), so `R' = R`
by uniqueness, and `R = R' ≤ Mᵢ`. -/
theorem remark_10_1_2_derivation (hMe : Lemma_10_1_3_statement.{u}) {G : Type u} [Group G]
    [Finite G] {ι : Type*} [Fintype ι] {K : ι → Type*} [∀ i, Group (K i)]
    {π : ∀ i, G →* K i} (hsub : IsSubdirectProduct π)
    {S : Type*} [Group S] [IsSimpleGroup S] (hSnonab : ¬ ∀ a b : S, a * b = b * a)
    {ϕ : G →* S} (hϕ : Function.Surjective ϕ) :
    ∃ i, (π i).ker ≤ ϕ.ker := by
  classical
  by_contra hcon
  push Not at hcon
  set N := ϕ.ker with hN
  -- "`MᵢN = G`" (as in the proof of Lemma 10.1.1: `N` is a maximal normal subgroup)
  have hMN : ∀ i, (π i).ker ⊔ N = ⊤ := by
    intro i
    have hnormal : ((π i).ker.map ϕ).Normal := Subgroup.Normal.map inferInstance ϕ hϕ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((π i).ker.map ϕ) hnormal with h | h
    · exact absurd ((Subgroup.map_eq_bot_iff _).1 h) (hcon i)
    · have hle : N ≤ (π i).ker ⊔ N := le_sup_right
      have hmapsup : ((π i).ker ⊔ N).map ϕ = ⊤ := by
        rw [Subgroup.map_sup, h, top_sup_eq]
      have := congrArg (Subgroup.comap ϕ) hmapsup
      rwa [Subgroup.comap_map_eq_self hle, Subgroup.comap_top] at this
  obtain ⟨R, ⟨hRsub, hRN, hRmin⟩, hRuniq⟩ :=
    hMe G N (commutator_quotient_ker_eq_top hSnonab hϕ)
  -- "`R ≤ Mᵢ` for all `i`"
  have hRM : ∀ i, R ≤ (π i).ker := by
    intro i
    let P : Subgroup G → Prop := fun H => IsSubnormal H ∧ H ⊔ N = ⊤ ∧ H ≤ (π i).ker
    have hex : ∃ n, ∃ H, P H ∧ Nat.card H = n :=
      ⟨_, (π i).ker, ⟨isSubnormal_of_normal, hMN i, le_rfl⟩, rfl⟩
    obtain ⟨R', hR'P, hR'card⟩ := Nat.find_spec hex
    have hmin : ∀ R'' : Subgroup G, IsSubnormal R'' → R'' ⊔ N = ⊤ → R'' ≤ R' → R'' = R' := by
      intro R'' h1 h2 h3
      have hP : P R'' := ⟨h1, h2, h3.trans hR'P.2.2⟩
      have hle : Nat.find hex ≤ Nat.card R'' := Nat.find_min' hex ⟨R'', hP, rfl⟩
      exact Subgroup.eq_of_le_of_card_ge h3 (by omega)
    have := hRuniq R' ⟨hR'P.1, hR'P.2.1, hmin⟩
    rw [← this]
    exact hR'P.2.2
  -- "`R ≤ ⋂ᵢ Mᵢ = 1`, contradicting the equation `RN = G`"
  have hRbot : R = ⊥ := by
    refine le_antisymm (fun g hg => ?_) bot_le
    exact hsub.faithful g (fun i => hRM i hg)
  rw [hRbot, bot_sup_eq] at hRN
  obtain ⟨s, hs⟩ := exists_ne (1 : S)
  obtain ⟨g, rfl⟩ := hϕ s
  have : g ∈ ϕ.ker := by rw [← hN, hRN]; trivial
  exact hs this

end Babai
