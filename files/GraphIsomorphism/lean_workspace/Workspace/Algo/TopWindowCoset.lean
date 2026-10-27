import Workspace.Algo.TopSuppliedUniform
import Workspace.Algo.TopWindowThree

/-! # Full preimages of cosets for the restricted top-action phase

Every child of the top-action phase on the restricted domain must be lifted
as a coset. A lift of its representative and lifts of its subgroup generators,
together with the restriction kernel, give that full preimage (§11.1,
Observation 11.1.11). All returned generators and representatives are normalized.
-/

namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

abbrev TopwCosetInput := (List ℕ × RawGens) × List ℕ × RawCoset

 def topwCosetPreimage (p : TopwCosetInput) : RawCoset :=
  p.2.2.bind fun a =>
    (rawPreimage (p.1, (p.2.1, normPerm (p.2.1, a.2)))).map fun r =>
      (tidyGens (p.1.1, rawLiftGens (p.1, (p.2.1, normGens (p.2.1, a.1)))),
        normPerm (p.1.1, r))

noncomputable def topwPreimageSet {n : ℕ} (Δ : List ℕ) (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) (G : Subgroup (Perm (Fin n)))
    (hinv : IsInvariant G (winSet n Δ)) (A : Set (Perm (Fin Δ.length))) : Set (Perm (Fin n)) :=
  {g | ∃ hg : g ∈ G, winRestrictHom n Δ hnd hlt G hinv ⟨g, hg⟩ ∈ A}

 theorem normPerm_eq_enc {n : ℕ} {dom : List ℕ} (hd : dom.length = n) (r : RawPerm) :
    normPerm (dom, r) = encPerm n (decPerm n r) := by
  rw [← decPerm_normPerm hd r]
  exact (encPerm_decPerm (wf_normPerm hd r)).symm

 theorem normGens_eq_enc {n : ℕ} {dom : List ℕ} (hd : dom.length = n) (g : RawGens) :
    normGens (dom, g) = (g.map (decPerm n)).map (encPerm n) := by
  simp only [normGens, List.map_map]
  exact List.map_congr_left (fun r _ => normPerm_eq_enc hd r)

 theorem topwCoset_parts {H : Type*} [Group H] {K L : Subgroup H} {r : H}
    (h : r • (K : Set H) ⊆ (L : Set H)) : r ∈ L ∧ K ≤ L := by
  have hr : r ∈ L := h ⟨1, K.one_mem, by simp⟩
  refine ⟨hr, fun k hk => ?_⟩
  have hx : r * k ∈ L := h ⟨k, hk, rfl⟩
  simpa using L.mul_mem (L.inv_mem hr) hx

 theorem topwCosetPreimage_spec {n : ℕ} {dom Δ : List ℕ}
    {gens : List (Perm (Fin n))} (hd : dom.length = n) (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) (hinv : IsInvariant (genGroup gens) (winSet n Δ))
    (a : RawCoset)
    (ha : decCoset Δ.length a ⊆
      ((winRestrictHom n Δ hnd hlt (genGroup gens) hinv).range : Set (Perm (Fin Δ.length)))) :
    decCoset n (topwCosetPreimage ((dom, gens.map (encPerm n)), Δ, a)) =
      topwPreimageSet Δ hnd hlt (genGroup gens) hinv (decCoset Δ.length a) := by
  cases a with
  | none =>
    simp [topwCosetPreimage, decCoset, topwPreimageSet]
  | some a =>
    rcases a with ⟨gs, r⟩
    rw [decCoset_some] at ha
    obtain ⟨hr, hg⟩ := topwCoset_parts ha
    obtain ⟨σ, hσ⟩ := hr
    have hn : normPerm (Δ, r) = encPerm Δ.length (decPerm Δ.length r) := normPerm_eq_enc rfl r
    have hgs := normGens_eq_enc (n := Δ.length) (dom := Δ) rfl gs
    cases hp : rawPreimage ((dom, gens.map (encPerm n)), (Δ, encPerm Δ.length (decPerm Δ.length r))) with
    | none =>
      exact False.elim ((rawPreimage_eq_none hd hnd hlt hinv hp) σ σ.2 hσ)
    | some q =>
      obtain ⟨τ, hτ, rfl, he⟩ := rawPreimage_eq_some hd hnd hlt hinv hp
      simp only [topwCosetPreimage, Option.bind_some, hn, hp, Option.map_some,
        decCoset_some, decGroup_tidyGens hd, decPerm_normPerm hd, decPerm_encPerm, hgs]
      rw [decGroup_rawLiftGens hd hnd hlt hinv (gs.map (decPerm Δ.length)) hg]
      exact (winPreimage_smul hnd hlt hinv (decGroup Δ.length gs) hτ he).symm

 theorem size_topwCosetPreimage {n : ℕ} {p : TopwCosetInput} (hd : p.1.1.length = n) :
    Enc.size (topwCosetPreimage p) ≤ chainBound n := by
  have h0 := chainBound_ge n
  unfold topwCosetPreimage
  cases p.2.2 with
  | none => simp only [Option.bind_none, size_none]; omega
  | some a =>
    simp only [Option.bind_some]
    cases rawPreimage (p.1, (p.2.1, normPerm (p.2.1, a.2))) with
    | none => simp only [Option.map_none, size_none]; omega
    | some r =>
      exact size_coset_le' le_rfl (wf_tidyGens hd _) (length_tidyGens hd _) (wf_normPerm hd _)

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

 theorem polyFun_topwCosetPreimage : PolyFun topwCosetPreimage := by
  let X := (RawGens × RawPerm) × TopwCosetInput
  have hp : PolyFun (fun z : X => z.2.1) := pfst polyFun_snd
  have hd := pfst hp
  have hw : PolyFun (fun z : X => z.2.2.1) := pfst (psnd polyFun_snd)
  have hg : PolyFun (fun z : X => z.1.1) := pfst polyFun_fst
  have hr : PolyFun (fun z : X => z.1.2) := psnd polyFun_fst
  have hpre := (hp.pair (hw.pair ((hw.pair hr).comp polyFun_normPerm))).comp polyFun_rawPreimage
  have hgens := (hd.pair ((hp.pair (hw.pair ((hw.pair hg).comp polyFun_normGens))).comp
    polyFun_rawLiftGens)).comp polyFun_tidyGens
  have hsome : PolyFun (fun z : RawPerm × X => some
      (tidyGens (z.2.2.1.1, rawLiftGens (z.2.2.1, (z.2.2.2.1, normGens (z.2.2.2.1, z.2.1.1)))),
        normPerm (z.2.2.1.1, z.1))) :=
    ((polyFun_snd.comp hgens).pair (((polyFun_snd.comp hd).pair polyFun_fst).comp
      polyFun_normPerm)).comp polyFun_some
  have hrun := ((hpre.pair polyFun_id).comp (PolyFun.optionElim (polyFun_const none) hsome))
  exact ((((psnd polyFun_snd).pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const none) hrun))).of_eq (fun p => by
      cases ha : p.2.2 with
      | none => simp only [topwCosetPreimage, ha, Option.bind_none, Option.elim_none]
      | some a =>
        simp only [topwCosetPreimage, ha, Option.bind_some, Option.elim_some, id_eq]
        cases rawPreimage (p.1, (p.2.1, normPerm (p.2.1, a.2))) <;> rfl)

end Algo
