import Workspace.Algo.AggregateTests
import Workspace.Algo.LocalCertStepWith
import Workspace.Algo.CosetUnion

/-! # The certificate store and its generated group (§13.2)

Each entry carries a test-set name, the fullness flag, and short generators for both
certificates. Keeping both certificates permits a direct link to lines 08 and 10 of
LocalCertificates. Updating this already materialized table costs polynomial time in
its size. The table itself can be quasipolynomial in the original domain size.
-/
namespace Algo
open RAM RAM.Targets
open Equiv (Perm)

/-- A test-set name, fullness flag, generators of `K(T)`, and generators of `M(T)`. -/
abbrev RawAggCert := List ℕ × Bool × RawGens × RawGens
abbrev RawAggStore := List RawAggCert

/-- Normalize a completed certificate before storing it. -/
def aggPack (p : List ℕ × List ℕ × RawLCOut) : RawAggCert :=
  (p.2.1, p.2.2.2.1, tidyGens (p.1, p.2.2.2.2.1),
    tidyGens (p.2.1, p.2.2.2.2.2))

/-- Add one certificate. Entries are stored in reverse processing order. -/
def aggAdd (q : (List ℕ × List ℕ × RawLCOut) × RawAggStore) : RawAggStore :=
  aggPack q.1 :: q.2

theorem aggPolyFun_pack : PolyFun aggPack := by
  have ht : PolyFun (fun p : List ℕ × List ℕ × RawLCOut => p.2.1) :=
    polyFun_snd.comp polyFun_fst
  have ho : PolyFun (fun p : List ℕ × List ℕ × RawLCOut => p.2.2.2) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_snd
  exact (ht.pair ((ho.comp polyFun_fst).pair
    (((polyFun_fst.pair ((ho.comp polyFun_snd).comp polyFun_fst)).comp polyFun_tidyGens).pair
      ((ht.pair ((ho.comp polyFun_snd).comp polyFun_snd)).comp polyFun_tidyGens)))).of_eq
    (fun _ => rfl)

theorem aggPolyFun_add : PolyFun aggAdd :=
  (((polyFun_fst.comp aggPolyFun_pack).pair polyFun_snd).comp polyFun_cons).of_eq
    (fun _ => rfl)

theorem aggQuasiFun_add : QuasiFun aggAdd := aggPolyFun_add.quasiFun

/-- The two decoders use different domains: `Ω` for `K`, and the named test set for `M`. -/
noncomputable def aggDecode (n : ℕ) (e : RawAggCert) :=
  (e.2.1, decGroup n e.2.2.1, decGroup e.1.length e.2.2.2)

/-- Normalization preserves the flag and both decoded certificates. -/
theorem aggPack_spec {n : ℕ} (dom row : List ℕ) (out : RawLCOut)
    (hd : dom.length = n) :
    aggDecode n (aggPack (dom, row, out)) =
      (out.2.1, decGroup n out.2.2.1, decGroup row.length out.2.2.2) := by
  simp only [aggDecode, aggPack, decGroup_tidyGens hd, decGroup_tidyGens rfl]
  rfl

/-- Physical well-formedness of one stored entry. -/
structure AggCertWF (n m t : ℕ) (e : RawAggCert) : Prop where
  nameNodup : e.1.Nodup
  nameLt : ∀ u ∈ e.1, u < m
  nameLength : e.1.length = t
  wfK : RawGens.WF n e.2.2.1
  shortK : e.2.2.1.length ≤ n * n
  wfM : RawGens.WF e.1.length e.2.2.2
  shortM : e.2.2.2.length ≤ e.1.length * e.1.length

/-- Each key occurs once and all entries are well formed. -/
def AggStoreWF (n m t : ℕ) (store : RawAggStore) : Prop :=
  (store.map Prod.fst).Nodup ∧ ∀ e ∈ store, AggCertWF n m t e

/-- The mathematical content of an entry. This uses `IsFull`, not a proxy for it. -/
structure AggCertFor {n m : ℕ} {G : Subgroup (Perm (Fin n))}
    (ϕ : G →* Perm (Fin m)) (x : Fin n → ℕ) (t : ℕ) (e : RawAggCert) : Prop where
  wf : AggCertWF n m t e
  full : e.2.1 = true ↔ Babai.IsFull ϕ x (winSet m e.1)
  certK : decGroup n e.2.2.1 = Babai.certK ϕ x (winSet m e.1)
  certM : decGroup e.1.length e.2.2.2 =
    (Babai.certM ϕ x (winSet m e.1)).map
      ((tName m e.1 wf.nameNodup wf.nameLt).symm.permCongrHom).toMonoidHom

/-- Correct entries in a partial store. Completeness is stated separately. -/
def AggStoreFor {n m : ℕ} {G : Subgroup (Perm (Fin n))}
    (ϕ : G →* Perm (Fin m)) (x : Fin n → ℕ) (t : ℕ) (store : RawAggStore) : Prop :=
  (store.map Prod.fst).Nodup ∧ ∀ e ∈ store, AggCertFor ϕ x t e

/-- Every test set has an entry. -/
def AggComplete (m t : ℕ) (store : RawAggStore) : Prop :=
  ∀ T : Set (Fin m), T.ncard = t → ∃ e ∈ store, winSet m e.1 = T

theorem aggPack_wf {n m t : ℕ} {dom row : List ℕ} (out : RawLCOut)
    (hd : dom.length = n) (hnd : row.Nodup) (hlt : ∀ u ∈ row, u < m)
    (hl : row.length = t) : AggCertWF n m t (aggPack (dom, row, out)) :=
  ⟨hnd, hlt, hl, wf_tidyGens hd _, length_tidyGens hd _,
    wf_tidyGens rfl _, length_tidyGens rfl _⟩

theorem aggAdd_for {n m t : ℕ} {G : Subgroup (Perm (Fin n))}
    {ϕ : G →* Perm (Fin m)} {x : Fin n → ℕ}
    {p : List ℕ × List ℕ × RawLCOut} {store : RawAggStore}
    (hs : AggStoreFor ϕ x t store) (he : AggCertFor ϕ x t (aggPack p))
    (hfresh : p.2.1 ∉ store.map Prod.fst) : AggStoreFor ϕ x t (aggAdd (p, store)) := by
  refine ⟨List.nodup_cons.2 ⟨hfresh, hs.1⟩, ?_⟩
  intro e h
  rcases List.mem_cons.1 h with rfl | h
  · exact he
  · exact hs.2 e h

/-- One entry is polynomially small in the ambient degree. -/
def aggEntryBound (n : ℕ) : ℕ := 2 * strBound n + 12 + 16 * gensBound n

theorem aggPolyBound_entry : PolyBound aggEntryBound :=
  (((polyBound_const 2).mul polyBound_strBound).add (polyBound_const 12)).add
    ((polyBound_const 16).mul polyBound_gensBound)

theorem aggSize_entry {n m t : ℕ} {e : RawAggCert} (h : AggCertWF n m t e)
    (hm : m ≤ n) (ht : t ≤ n) : Enc.size e ≤ aggEntryBound n := by
  have hn : Enc.size e.1 ≤ strBound n := size_natList_le (h.nameLength.le.trans ht)
    (fun u hu => (h.nameLt u hu).trans_le hm)
  have hk := size_gens_le' (le_refl n) h.wfK h.shortK
  have hi := size_gens_le' (h.nameLength.le.trans ht) h.wfM h.shortM
  have h0 := size_pair_le' e
  have h1 := size_pair_le' e.2
  have h2 := size_pair_le' e.2.2
  have hb := Combine.size_bool_le e.2.1
  unfold aggEntryBound
  omega

/-- The store is polynomial in its number of entries times the ambient size. -/
theorem aggSize_store {n m t : ℕ} {store : RawAggStore}
    (h : ∀ e ∈ store, AggCertWF n m t e) (hm : m ≤ n) (ht : t ≤ n) :
    Enc.size store ≤ 1 + store.length * (2 * aggEntryBound n + 1) :=
  size_list_le_of_entries _ _ (fun e he => aggSize_entry (h e he) hm ht)

/-- A bound by `C(m,t)` entries gives the requested ground-size estimate. -/
theorem aggSize_store_choose {n m t : ℕ} {store : RawAggStore}
    (h : ∀ e ∈ store, AggCertWF n m t e) (hm : m ≤ n) (ht : t ≤ n)
    (hlen : store.length ≤ m.choose t) :
    Enc.size store ≤ 1 + m.choose t * (2 * aggEntryBound n + 1) :=
  (aggSize_store h hm ht).trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hlen) 1)

/-- The fullness generators, before shortening (§13.2). -/
def aggFullGens (store : RawAggStore) : RawGens :=
  (store.filter (fun e => e.2.1)).flatMap (fun e => e.2.2.1)

/-- The group `F` of Theorem 13.2.1, by short generators. -/
def rawF (p : List ℕ × RawAggStore) : RawGens := tidyGens (p.1, aggFullGens p.2)

theorem aggPolyFun_fullGens : PolyFun aggFullGens := by
  have hf : PolyFun (fun e : RawAggCert => e.2.1) := polyFun_snd.comp polyFun_fst
  have hk : PolyFun (fun e : RawAggCert => e.2.2.1) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_fst
  exact (((PolyFun.filter hf).comp (PolyFun.map hk)).comp polyFun_flatten).of_eq
    (fun _ => rfl)

theorem aggPolyFun_F : PolyFun rawF :=
  ((polyFun_fst.pair (polyFun_snd.comp aggPolyFun_fullGens)).comp polyFun_tidyGens).of_eq
    (fun _ => rfl)

theorem aggSize_F (p : List ℕ × RawAggStore) : Enc.size (rawF p) ≤ gensBound p.1.length :=
  size_gens_le' (le_refl _) (wf_tidyGens rfl _) (length_tidyGens rfl _)

section FSpec
open scoped Classical
variable {n m t : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)}
  {x : Fin n → ℕ} {store : RawAggStore} {dom : List ℕ}

/-- Each full entry contributes its entire certificate group. -/
theorem aggCert_le_F {e : RawAggCert} (he : e ∈ store) (hf : e.2.1 = true)
    (hd : dom.length = n) : decGroup n e.2.2.1 ≤ decGroup n (rawF (dom, store)) := by
  rw [rawF, decGroup_tidyGens hd]
  apply Subgroup.closure_mono
  intro g hg
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hg
  apply List.mem_map_of_mem
  exact List.mem_flatMap.2 ⟨e, List.mem_filter.2 ⟨he, hf⟩, hr⟩

/-- §13.2: the raw generators give exactly `Babai.bigF` once all test sets are stored. -/
theorem aggF_spec (hd : dom.length = n) (hs : AggStoreFor ϕ x t store)
    (hall : AggComplete m t store) : decGroup n (rawF (dom, store)) = Babai.bigF ϕ x t := by
  apply le_antisymm
  · rw [rawF, decGroup_tidyGens hd]
    apply (Subgroup.closure_le _).2
    intro g hg
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hg
    obtain ⟨e, he, hr⟩ := List.mem_flatMap.1 hr
    obtain ⟨he, hf⟩ := List.mem_filter.1 he
    have h := hs.2 e he
    have hT : winSet m e.1 ∈ Babai.fullSets ϕ x t :=
      ⟨(ncard_winSet _ h.wf.nameNodup h.wf.nameLt).trans h.wf.nameLength, h.full.1 hf⟩
    apply Babai.certK_le_bigF hT
    rw [← h.certK]
    exact Subgroup.subset_closure (List.mem_map_of_mem hr)
  · apply (Subgroup.closure_le _).2
    intro g hg
    obtain ⟨T, hT, hg⟩ := Set.mem_iUnion₂.1 hg
    obtain ⟨e, he, hname⟩ := hall T hT.1
    have h := hs.2 e he
    have hf : e.2.1 = true := h.full.2 (hname.symm ▸ hT.2)
    apply aggCert_le_F he hf hd
    rw [h.certK, hname]
    exact hg

end FSpec
/-- The count bound follows from using each name in the computed table at most once. -/
theorem aggStore_length {c n t : ℕ} {ks dom : List ℕ} {store : RawAggStore}
    (hg : ks.length ≤ guardBound c dom.length) (hs : AggStoreWF n dom.length t store)
    (hkeys : store.map Prod.fst ⊆ aggTestSets c (ks, dom)) :
    store.length ≤ dom.length.choose ks.length := by
  have h := (List.subperm_of_subset hs.1 hkeys).length_le
  simpa only [List.length_map, aggLength_testSets hg] using h

/-- A uniform bound on the number of test sets under the logarithmic arity guard. -/
theorem aggChoose_le (c : ℕ) {n m t : ℕ} (hm : m ≤ n) (ht : t ≤ guardBound c n) :
    m.choose t ≤ 2 ^ ((Nat.log 2 n + 2) ^ (c + 1)) := by
  calc
    m.choose t ≤ m ^ t := Nat.choose_le_pow _ _
    _ ≤ (2 ^ (Nat.log 2 n + 1)) ^ t :=
      Nat.pow_le_pow_left (hm.trans (le_two_pow_log n)) _
    _ = 2 ^ ((Nat.log 2 n + 1) * t) := by rw [← pow_mul]
    _ ≤ 2 ^ ((Nat.log 2 n + 1) ^ (c + 1)) := by
      apply Nat.pow_le_pow_right (by decide)
      simpa only [guardBound, pow_succ, Nat.mul_comm] using
        Nat.mul_le_mul_left (Nat.log 2 n + 1) ht
    _ ≤ 2 ^ ((Nat.log 2 n + 2) ^ (c + 1)) :=
      Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_left (by omega) _)

def aggStoreBound (c n : ℕ) : ℕ :=
  1 + 2 ^ ((Nat.log 2 n + 2) ^ (c + 1)) * (2 * aggEntryBound n + 1)

theorem aggQuasiPolyBound_store (c : ℕ) : QuasiPolyBound (aggStoreBound c) :=
  (polyBound_const 1).quasiPoly.add ((quasiPolyBound_witness (c + 1)).mul
    (((polyBound_const 2).mul aggPolyBound_entry).add (polyBound_const 1)).quasiPoly)

/-- The constant precedes the ground size, and works for every well-formed partial store. -/
theorem aggSize_store_quasi (c : ℕ) : ∃ d : ℕ, ∀ (n m t : ℕ) (store : RawAggStore),
    (∀ e ∈ store, AggCertWF n m t e) → m ≤ n → t ≤ n →
    t ≤ guardBound c n → store.length ≤ m.choose t →
    Enc.size store ≤ 2 ^ ((Nat.log 2 n + 2) ^ d) := by
  obtain ⟨d, hd⟩ := aggQuasiPolyBound_store c
  refine ⟨d, fun n m t store hw hm ht hg hl => ?_⟩
  apply le_trans (aggSize_store_choose hw hm ht hl)
  exact (Nat.add_le_add_left (Nat.mul_le_mul_right _ (aggChoose_le c hm hg)) 1).trans (hd n)

section Witnesses
open scoped Classical

/-- Every subgroup has a well-formed short raw representation. Used only to check that
our specification has models; this is not the algorithm that finds a certificate. -/
theorem aggExists_gens {n : ℕ} (H : Subgroup (Perm (Fin n))) :
    ∃ gs : RawGens, RawGens.WF n gs ∧ gs.length ≤ n * n ∧ decGroup n gs = H := by
  let gs := ((H : Set (Perm (Fin n))).toFinset.toList).map (encPerm n)
  refine ⟨tidyGens (List.range n, gs), wf_tidyGens (List.length_range) _,
    length_tidyGens (List.length_range) _, ?_⟩
  rw [decGroup_tidyGens (List.length_range), decGroup_map_encPerm]
  change Subgroup.closure {g | g ∈ (H : Set (Perm (Fin n))).toFinset.toList} = H
  have he : {g | g ∈ (H : Set (Perm (Fin n))).toFinset.toList} = (H : Set (Perm (Fin n))) := by
    ext g; simp
  rw [he, Subgroup.closure_eq]

/-- Any properly named test set admits an entry meeting all specification fields. -/
theorem aggExists_entry {n m t : ℕ} {G : Subgroup (Perm (Fin n))}
    (ϕ : G →* Perm (Fin m)) (x : Fin n → ℕ) (row : List ℕ)
    (hnd : row.Nodup) (hlt : ∀ u ∈ row, u < m) (hl : row.length = t) :
    ∃ e : RawAggCert, e.1 = row ∧ AggCertFor ϕ x t e := by
  obtain ⟨kg, hkw, hkl, hk⟩ := aggExists_gens (Babai.certK ϕ x (winSet m row))
  obtain ⟨mg, hmw, hml, hm⟩ := aggExists_gens
    ((Babai.certM ϕ x (winSet m row)).map
      ((tName m row hnd hlt).symm.permCongrHom).toMonoidHom)
  refine ⟨(row, decide (Babai.IsFull ϕ x (winSet m row)), kg, mg), rfl,
    ⟨⟨hnd, hlt, hl, hkw, hkl, hmw, hml⟩, ?_, hk, hm⟩⟩
  simp only [decide_eq_true_eq]

/-- The entry and store hypotheses can hold together, for any list of distinct valid names. -/
theorem aggExists_store {n m t : ℕ} {G : Subgroup (Perm (Fin n))}
    (ϕ : G →* Perm (Fin m)) (x : Fin n → ℕ) (rows : List (List ℕ))
    (hnd : rows.Nodup)
    (hw : ∀ row ∈ rows, row.Nodup ∧ (∀ u ∈ row, u < m) ∧ row.length = t) :
    ∃ store : RawAggStore, store.map Prod.fst = rows ∧ AggStoreFor ϕ x t store := by
  induction rows with
  | nil => exact ⟨[], rfl, by simp [AggStoreFor]⟩
  | cons row rows ih =>
    obtain ⟨hr, hrows⟩ := List.nodup_cons.1 hnd
    obtain ⟨store, hkeys, hs⟩ := ih hrows (fun r h => hw r (List.mem_cons_of_mem _ h))
    obtain ⟨hn, hb, hl⟩ := hw row (List.mem_cons_self)
    obtain ⟨e, he, hcert⟩ := aggExists_entry ϕ x row hn hb hl
    refine ⟨e :: store, by simp [he, hkeys], ?_⟩
    refine ⟨by simpa [he, hkeys] using hnd, ?_⟩
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hcert
    · exact hs.2 a ha

/-- In particular a complete store exists in the computed order. -/
theorem aggExists_complete {c n t : ℕ} {dom ks : List ℕ}
    {G : Subgroup (Perm (Fin n))} (ϕ : G →* Perm (Fin dom.length)) (x : Fin n → ℕ)
    (hg : ks.length ≤ guardBound c dom.length) (ht : ks.length = t) :
    ∃ store : RawAggStore, AggStoreFor ϕ x t store ∧ AggComplete dom.length t store ∧
      store.length = dom.length.choose t := by
  obtain ⟨store, he, hs⟩ := aggExists_store ϕ x (aggTestSets c (ks, dom))
    (aggNodup_testSets c ks dom hg)
    (fun row hr => let h := aggRow_wf hg hr; ⟨h.1, h.2.1, h.2.2.trans ht⟩)
  refine ⟨store, hs, ?_, ?_⟩
  · intro T hT
    have hr := aggTestSets_cover hg T (hT.trans ht.symm)
    rw [← he] at hr
    obtain ⟨e, he', hrow⟩ := List.mem_map.1 hr
    exact ⟨e, he', hrow ▸ aggName_spec T⟩
  · have h := congrArg List.length he
    simpa [aggLength_testSets hg, ht] using h

end Witnesses
end Algo
