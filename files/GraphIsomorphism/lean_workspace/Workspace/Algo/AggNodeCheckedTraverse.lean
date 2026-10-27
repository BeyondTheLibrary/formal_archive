import Workspace.Algo.AggNodeCheckedRAM

/-! # Bounded traversals for the certificate scan

A scan visits the supplied list. A quasipolynomial map has a quasipolynomial
answer because each mapped entry is bounded in the size of the input list.
The fold lemma below exposes its size obligation; the map discharges it.
-/
namespace Algo
open RAM RAM.Targets

/-- A list fold with a proved quasipolynomial bound on every intermediate accumulator. -/
theorem aggnQuasiFun_foldl {α σ : Type*} [Enc α] [Enc σ] {f : σ × α → σ}
    (hf : QuasiFun f) {p : ℕ → ℕ} (hp : QuasiPolyBound p)
    (hacc : ∀ (x : σ) (r : List α) (j : ℕ),
      Enc.size (r.take j |>.foldl (fun y a => f (y, a)) x) ≤ p (Enc.size (x, r))) :
    QuasiFun (fun s : σ × List α => s.2.foldl (fun y a => f (y, a)) s.1) := by
  have hg : QuasiFun (fun x : σ => (x, ([] : List α))) :=
    (polyFun_id.pair polyFun_nil).quasiFun
  have hh : QuasiFun (fun q : (α × List α) × σ => (f (q.2, q.1.1), q.1.2)) :=
    (((polyFun_snd.pair (polyFun_fst.comp polyFun_fst)).comp_quasiFun hf).pair
      (polyFun_fst.comp polyFun_snd).quasiFun)
  have hstep : QuasiFun (foldlStep f) :=
    (polyFun_swap.comp_quasiFun (QuasiFun.listCases hg hh)).of_eq (fun ⟨x, r⟩ => by cases r <;> rfl)
  have hdec : PolyFun (fun z : ℕ × (σ × List α) => z.1 - 1) :=
    (polyFun_fst.pair (polyFun_const 1)).comp polyFun_sub
  have hsetup : QuasiFun (fun s : σ × List α => (s.2.length, s)) :=
    ((polyFun_snd.comp polyFun_length).pair polyFun_id).quasiFun
  have hbound : ∀ (s : σ × List α) (j : ℕ),
      Enc.size ((foldlStep f)^[j] s) ≤ 2 * p (Enc.size s) + 2 * Enc.size s := by
    rintro ⟨x, r⟩ j
    rw [foldlStep_iterate]
    have h1 := Combine.size_pair_le (List.foldl (fun y a => f (y, a)) x (r.take j)) (r.drop j)
    have h2 := hacc x r j
    have h3 := (size_drop_le j r).trans (size_snd_le' (x, r))
    omega
  have hrun := QuasiFun.iterateSetup hsetup
    (hdec.quasiFun.pair (polyFun_snd.comp_quasiFun hstep)) polyFun_fst.quasiFun
    (q := id) (fun s => (length_le_size s.2).trans (size_snd_le' s)) polyBound_id.quasiPoly
    (p := fun n => 2 * p n + 2 * n) (fun s j _ => hbound s j)
    (((polyBound_const 2).quasiPoly.mul hp).add
      ((polyBound_const 2).mul polyBound_id).quasiPoly)
  exact hrun.of_eq (fun ⟨x, r⟩ => by simp only [foldlStep_iterate, List.take_length])

/-- Mapping a quasipolynomial routine over an explicit list needs no further invariant. -/
theorem aggnQuasiFun_map {α β : Type*} [Enc α] [Enc β] {g : α → β}
    (hg : QuasiFun g) : QuasiFun (fun l : List α => l.map g) := by
  obtain ⟨S, hS, hmono, hs⟩ := hg.size.exists_quasiPolyBound
  have hmap : ∀ l : List α, Enc.size (l.map g) ≤ 1 + Enc.size l * (2 * S (Enc.size l) + 1) := by
    intro l
    have he : ∀ b ∈ l.map g, Enc.size b ≤ S (Enc.size l) := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
      exact (hs a).trans (hmono _ _ (size_mem_le ha))
    have hh := size_list_le_of_entries (l.map g) _ he
    rw [List.length_map] at hh
    exact hh.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (length_le_size l)) 1)
  have hstep : QuasiFun (fun z : List β × α => g z.2 :: z.1) :=
    (((polyFun_snd.comp_quasiFun hg).pair polyFun_fst.quasiFun).comp_poly polyFun_cons)
  have hpoly : QuasiPolyBound (fun n => n + (1 + n * (2 * S n + 1))) :=
    polyBound_id.quasiPoly.add ((polyBound_const 1).quasiPoly.add
      (polyBound_id.quasiPoly.mul (((polyBound_const 2).quasiPoly.mul hS).add
        (polyBound_const 1).quasiPoly)))
  have hfold := aggnQuasiFun_foldl hstep hpoly (fun x r j => by
    have h1 := size_foldl_map_cons_le g (r.take j) x
    have h2 := hmap (r.take j)
    have hx : Enc.size x ≤ Enc.size (x, r) := size_fst_le' (x, r)
    have hr := (size_take_le j r).trans (size_snd_le' (x, r))
    have hb := Nat.mul_le_mul hr (Nat.add_le_add_right
      (Nat.mul_le_mul_left 2 (hmono _ _ hr)) 1)
    dsimp only
    omega)
  exact ((((polyFun_nil.pair polyFun_id).comp_quasiFun hfold).comp_poly polyFun_reverse)).of_eq
    (fun l => by rw [foldl_map_cons_eq]; simp)

/-- Pair the fixed parameter with each list entry before the quasipolynomial map. -/
theorem aggnQuasiFun_mapParam {α β γ : Type*} [Enc α] [Enc β] [Enc γ]
    {f : γ × α → β} (hf : QuasiFun f) :
    QuasiFun (fun p : γ × List α => p.2.map (fun a => f (p.1, a))) :=
  ((PolyFun.mapParam polyFun_id).comp_quasiFun (aggnQuasiFun_map hf)).of_eq
    (fun p => by simp only [List.map_map]; rfl)

end Algo
