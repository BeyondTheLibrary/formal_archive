import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.Thm75Claim1
import Workspace.ProofLemmas.Thm75Claim2STAnticomplete
import Workspace.ProofLemmas.Thm75Claim2FAvoidsLineGraph
import Workspace.ProofLemmas.Thm75Claim2AttachmentsNotLocal
import Workspace.ProofLemmas.Thm75Claim2NondegenerateH
import Workspace.ProofLemmas.Thm75BranchEnds
import Workspace.ProofLemmas.AppearanceVertexTypeTransport
import Workspace.ProofLemmas.Thm75Claim2Five82

/-!
# 7.5, claim (2): the induction frame

PAPER (proof of 7.5, claim (2), printed p. 36):

*"(2) If `F ⊆ V(G)` is connected and some vertex of `S` has a neighbour in `F`, and so does some
vertex of `T`, and `F ∩ (X₀ ∪ X₁ ∪ Y) = ∅`, then the theorem holds.*

*We shall prove this by induction on `|F|`; so, we assume it holds for all smaller choices of `F`
(even for different choices of `L(H)`)."*

`Workspace.ProofLemmas.Thm75Claim2.thm75Claim2` fixes one appearance `L(H)` and one `F`, which
is the shape the rest of §7.5 consumes but is **not** a shape one can induct in: the parenthesis
*"even for different choices of `L(H)`"* says the inductive hypothesis has to be available for
every smaller `F` **and simultaneously for every other appearance of `J` in `G`**.  This module
is that frame.  Everything except `G`, `hG`, `J`, `hJ` and the size bound `n` is universally
quantified **inside** the statement, so `induction n` gives exactly the printed induction
hypothesis.

## Why `F.ncard ≤ n` with `induction n` is the right frame

Two places in the printed argument consume the inductive hypothesis, and they consume it in
different directions:

* **The `b₁b₂ ≠ c₁c₂` branch**, after the rung replacement: *"Since there is a proper subset `F′`
  of `F` with attachments in `S` and in the new set `T′` in `V(H′)` corresponding to `T` … it
  follows that we may apply the inductive hypothesis."*  Here both `F` and the appearance change
  — `F′ ⊊ F` and `L(H)` becomes `L(H′)` — so an induction that fixed the appearance would be
  useless.  With this frame, `F′.ncard ≤ n - 1` and `H′` is just another value of the inner
  `∀ m H K φ`, so the induction hypothesis applies verbatim.
* **The opening reduction**, before 5.8 is even reached: *"Hence we may assume that `G|F` is a
  path with vertices `f₁,…,fₙ`, where `f₁` is the only vertex of `F` with a neighbour in `S`, and
  `fₙ` the only vertex with a neighbour in `T`"*, and *"From the minimality of `F` it also follows
  that `F` is disjoint from `L(H)`; for any vertex of `F` in `L(H)` would be in `S` or `T`, since
  it is not in `X₁`, and then we could make `F` shorter by omitting this vertex.  Consequently
  `F ∩ X = ∅`."*  Both sentences are appeals to the inductive hypothesis on a **proper subset**
  of `F` with the same appearance — the paper phrases them as "minimality of `F`", which is the
  same thing read contrapositively.  They too are covered by `F.ncard ≤ n` at the smaller value.

`F.ncard ≤ n` (rather than `F.ncard = n`) is what makes both appeals one-liners: any proper
subset of an `F` with `F.ncard ≤ n + 1` has cardinality `≤ n`.

## Relation to the frozen statement

`Workspace.ProofLemmas.Thm75Claim2.thm75Claim2` is stated for `H : SimpleGraph W` with `W` an
arbitrary finite type, whereas this frame uses `H : SimpleGraph (Fin m)` so that the induction
stays in `Type 0` and so that the appearance produced by the rung replacement
(which lands in `Fin m`) is directly
an instance of the quantifier.  `thm75Claim2` follows from this by transporting the appearance
along `SimpleGraph.Iso.map (Fintype.equivFin W) H`, exactly as
`Workspace.ProofLemmas.AppearanceVertexTypeTransport` (namespace `Thm75Claim2Transport`) does for
`five8W` and `enlargementFromNonlocalAttachmentPathW`; instantiate `n := Fintype.card V` to
discharge the size bound.  **`Thm75Claim2.lean` is frozen and is not edited here.**

The seven proof-local sets `X, X₀, X₁, Rset, S, T, F` and the six equations defining the first
six of them are copied from `thm75Claim2`'s own binder list, with `Sym2 W` becoming
`Sym2 (Fin m)`; the conclusion is copied from `thm75Claim2`'s conclusion.  (Its existential
binders `m` and `n` shadow the outer `m` and `n`; that is the frozen text and is left alone.)

**Status: statement only — this module is a work item.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm75Claim2Generalised

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.Thm75Setup

/-- **7.5, claim (2), in the form one can induct on.**  The printed claim, with the size bound
`F.ncard ≤ n` in front and with the appearance, the branch, the maximal anticonnected set `Y`
and the seven proof-local sets all quantified inside, so that `induction n` yields the paper's
*"we assume it holds for all smaller choices of `F` (even for different choices of `L(H)`)"*. -/
theorem thm75Claim2Generalised {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3) (n : ℕ) :
    ∀ (m : ℕ) (H : SimpleGraph (Fin m)) (K : Set V) (φ : H.lineGraph ≃g G.induce K),
      IsAppearance G J H K →
    ∀ (B : List (Fin m)) (c₁ c₂ : Fin m), IsBranch H B → IsTrackFrom H B c₁ c₂ →
      Odd (trackLength B) → 3 ≤ trackLength B →
    ∀ (Y : Set V), Y.Nonempty → AnticonnectedSet G Y →
      (∀ y ∈ Y, IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y) →
      (∀ Y' : Set V, Y ⊆ Y' → AnticonnectedSet G Y' →
        (∀ y ∈ Y', IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y) → Y' = Y) →
    ∀ (X X₀ X₁ Rset S T F : Set V),
      X = {x : V | VertexComplete G x Y} →
      Rset = {x : V | ∃ (e : Sym2 (Fin m)) (he : e ∈ H.edgeSet),
        e ∈ trackEdges B ∧ x = (↑(φ ⟨e, he⟩) : V)} →
      X₀ = X \ K →
      X₁ = X ∩ (NSet G H K φ c₁ ∪ NSet G H K φ c₂) →
      S = Rset \ X₁ →
      T = (K \ Rset) \ X₁ →
      F.ncard ≤ n → ConnectedSet G F → (∀ x ∈ F, x ∉ X₀ ∪ X₁ ∪ Y) →
      (∃ s ∈ S, ∃ f ∈ F, G.Adj s f) → (∃ t ∈ T, ∃ f ∈ F, G.Adj t f) →
      ((∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧
          ∃ (n : ℕ) (H' : SimpleGraph (Fin n)) (K' : Set V),
            IsAppearance G J' H' K' ∧ NondegenerateAppearance J' H') ∨
        AdmitsBalancedSkewPartition G) := by
  classical
  induction n with
  | zero =>
      intro m H K φ happ B c₁ c₂ hbranch hfrom hodd hlen Y hYne hYanti hYdom hYmax
        X X₀ X₁ Rset S T F hX hRset hX₀ hX₁ hS hT hFcard hFconn hFdisj hSF hTF
      have hFzero : F.ncard = 0 := by omega
      have hFempty : F = ∅ := (Set.ncard_eq_zero).mp hFzero
      obtain ⟨s, hsS, f, hfF, hsf⟩ := hSF
      exact (show False by simpa [hFempty] using hfF).elim
  | succ n ih =>
      intro m H K φ happ B c₁ c₂ hbranch hfrom hodd hlen Y hYne hYanti hYdom hYmax
        X X₀ X₁ Rset S T F hX hRset hX₀ hX₁ hS hT hFcard hFconn hFdisj hSF hTF
      by_cases hFsmall : F.ncard ≤ n
      · exact ih m H K φ happ B c₁ c₂ hbranch hfrom hodd hlen Y hYne hYanti hYdom
          hYmax X X₀ X₁ Rset S T F hX hRset hX₀ hX₁ hS hT hFsmall hFconn hFdisj hSF hTF
      by_cases hproper : ∃ F' : Set V,
          F' ⊆ F ∧ F' ≠ F ∧ ConnectedSet G F' ∧
          (∀ x ∈ F', x ∉ X₀ ∪ X₁ ∪ Y) ∧
          (∃ s ∈ S, ∃ f ∈ F', G.Adj s f) ∧
          (∃ t ∈ T, ∃ f ∈ F', G.Adj t f)
      · obtain ⟨F', hF'sub, hF'ne, hF'conn, hF'disj, hSF', hTF'⟩ := hproper
        have hlt : F'.ncard < F.ncard :=
          Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨hF'sub, hF'ne⟩)
        have hF'card : F'.ncard ≤ n := by omega
        exact ih m H K φ happ B c₁ c₂ hbranch hfrom hodd hlen Y hYne hYanti hYdom
          hYmax X X₀ X₁ Rset S T F' hX hRset hX₀ hX₁ hS hT hF'card hF'conn
          hF'disj hSF' hTF'
      · have hmin : ∀ F' : Set V, F' ⊆ F → F' ≠ F → ConnectedSet G F' →
            (∀ x ∈ F', x ∉ X₀ ∪ X₁ ∪ Y) → (∃ s ∈ S, ∃ f ∈ F', G.Adj s f) →
            (∃ t ∈ T, ∃ f ∈ F', G.Adj t f) → False := by
          intro F' hsub hne hconn hdisj hSF' hTF'
          exact hproper ⟨F', hsub, hne, hconn, hdisj, hSF', hTF'⟩
        have hsmall₀ := Workspace.ProofLemmas.Thm75Claim1.thm75Claim1
          G hG J hJ H K φ happ B c₁ c₂ hbranch hfrom hodd hlen Y hYne hYanti hYdom
        have hsmall : (NSet G H K φ c₁ \ X).Subsingleton ∧
            (NSet G H K φ c₂ \ X).Subsingleton := by
          simpa [hX] using hsmall₀
        have hSTanti : Anticomplete G S T :=
          Workspace.ProofLemmas.Thm75Claim2STAnticomplete.thm75Claim2STAnticomplete
            G H K φ B c₁ c₂ hbranch hfrom X X₁ Rset S T hRset hX₁ hS hT hsmall
        have hFK : ∀ x ∈ F, x ∉ K :=
          Workspace.ProofLemmas.Thm75Claim2FAvoidsLineGraph.thm75Claim2FAvoidsLineGraph
            G J H K φ happ B c₁ c₂ hbranch hfrom Y X X₀ X₁ Rset S T hX hRset hX₀
              hX₁ hS hT F hFconn hFdisj hSF hTF hSTanti hmin
        have hnotlocal :=
          Workspace.ProofLemmas.Thm75Claim2AttachmentsNotLocal.thm75Claim2AttachmentsNotLocal
            G J hJ H K φ happ B c₁ c₂ hbranch hfrom hodd hlen Y X X₀ X₁ Rset S T hX
              hRset hX₀ hX₁ hS hT hsmall F hFconn hFdisj hFK hSF hTF
        have hends := Workspace.ProofLemmas.Thm75BranchEnds.branchEnds_mem_branchVertices
          J hJ H happ.1.1 B c₁ c₂ hbranch hfrom (by omega)
        have hnomajor : ∀ x ∈ F, ¬ MajorForLineGraph G H K φ x :=
          Thm75Claim2Transport.no_major_in_F K φ hends.1 hends.2
            Y hYanti hYdom hYmax X X₀ X₁ hX hX₀ F hFdisj
        obtain ⟨P, p₁, p₂, hP, hPF, hcase⟩ :=
          Thm75Claim2Transport.five8W
            G hG J hJ H K happ.1 φ (NSet G H K φ) (fun _ => rfl) F
              (fun x hx => hFK x hx) hFconn hnotlocal hnomajor
        rcases hcase with hcase₁ | hcase₂
        · obtain ⟨d₁, d₂, hnb, hd₁, hd₂, hno⟩ := hcase₁
          left
          exact Thm75Claim2Transport.enlargementFromNonlocalAttachmentPathW
            G hG J hJ H K happ φ (NSet G H K φ) (fun _ => rfl) P p₁ p₂ hP
              (fun x hx => hFK x (hPF x hx)) d₁ d₂ hnb hd₁ hd₂ hno
              (Workspace.ProofLemmas.Thm75Claim2NondegenerateH.thm75Claim2NondegenerateH
                G J hJ H K φ happ B c₁ c₂ hbranch hfrom hodd hlen)
        · obtain ⟨b₁, b₂, q, R, r₁, r₂, hb₁, hb₂, hq, hqf, hR, hRs, hr₁, hr₂,
              hcases⟩ := hcase₂
          exact Workspace.ProofLemmas.Thm75Claim2Five82.thm75Claim2Five82
            G hG J hJ n ih m H K φ happ B c₁ c₂ hbranch hfrom hodd hlen Y hYne hYanti
              hYdom hYmax X X₀ X₁ Rset S T hX hRset hX₀ hX₁ hS hT F hFcard hFconn
              hFdisj hFK hSF hTF hmin P p₁ p₂ hP hPF b₁ b₂ q R r₁ r₂ hb₁ hb₂ hq hqf
              hR hRs hr₁ hr₂ hcases

end Workspace.ProofLemmas.Thm75Claim2Generalised
