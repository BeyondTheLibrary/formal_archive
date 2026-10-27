import Workspace.Algo.CameronSign

/-!
# Recovering point maps from the Cameron table

A point in one coordinate gives a column of the table: mark exactly those tuples
whose subset at that coordinate contains the point. Distinct coordinate-point
pairs have distinct columns. A wreath element permutes these columns. Comparing
them therefore recovers both its coordinate map and its point maps.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

/-- The row at a given point and coordinate. -/
def camRow (p : RawCameron × (ℕ × ℕ)) : List ℕ :=
  (p.1.table.getD p.2.1 []).getD p.2.2 []

/-- A column of the incidence table. -/
def camStar (p : RawCameron × (ℕ × ℕ)) : List ℕ :=
  (camDom p.1).filter (fun x => decide (p.2.2 ∈ camRow (p.1, x, p.2.1)))

/-- Pull a column back by a supplied raw permutation. -/
def camPullStar (p : (RawCameron × RawPerm) × (ℕ × ℕ)) : List ℕ :=
  (camDom p.1.1).filter (fun x =>
    decide (p.2.2 ∈ camRow (p.1.1, rawGet (p.1.2, x), p.2.1)))

/-- Both header scans stop at the end of the supplied table, even on junk. -/
def camCoordDom (c : RawCameron) : List ℕ := rowsBefore (camDom c, c.s)
def camPointDom (c : RawCameron) : List ℕ := rowsBefore (camDom c, c.k)

/-- The coordinate-point pairs to compare. -/
def camStarDom (c : RawCameron) : List (ℕ × ℕ) :=
  ((camCoordDom c).map (fun i => (camPointDom c).map (fun a => (i, a)))).flatten

/-- Test whether a candidate column is the image of the given column. -/
def camStarMatch (p : ((RawCameron × RawPerm) × (ℕ × ℕ)) × (ℕ × ℕ)) : Bool :=
  decide (camStar (p.1.1.1, p.1.2) = camPullStar (p.1.1, p.2))

/-- Recover a coordinate-point image by scanning the incidence columns. -/
def camRecover (p : (RawCameron × RawPerm) × (ℕ × ℕ)) : ℕ × ℕ :=
  ((camStarDom p.1.1).filter (fun q => camStarMatch (p, q))).headD (0, 0)

/-- The recovered point permutation at a source coordinate. -/
def camPointPerm (p : (RawCameron × RawPerm) × ℕ) : RawPerm :=
  (camPointDom p.1.1).map (fun a => (camRecover (p.1, p.2, a)).2)

theorem camPoly_row : PolyFun camRow := by
  have hc : PolyFun (fun p : RawCameron × (ℕ × ℕ) => p.1.table) :=
    polyFun_fst.comp camPoly_table
  have hx : PolyFun (fun p : RawCameron × (ℕ × ℕ) => p.2.1) :=
    polyFun_snd.comp polyFun_fst
  have hi : PolyFun (fun p : RawCameron × (ℕ × ℕ) => p.2.2) :=
    polyFun_snd.comp polyFun_snd
  exact (((((hc.pair hx).pair polyFun_nil).comp polyFun_getD).pair hi).pair
    polyFun_nil).comp polyFun_getD

theorem camPoly_star : PolyFun camStar := by
  have hc : PolyFun (fun p : (RawCameron × (ℕ × ℕ)) × ℕ => p.1.1) :=
    polyFun_fst.comp polyFun_fst
  have hi : PolyFun (fun p : (RawCameron × (ℕ × ℕ)) × ℕ => p.1.2.1) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_fst
  have ha : PolyFun (fun p : (RawCameron × (ℕ × ℕ)) × ℕ => p.1.2.2) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_snd
  exact (polyFun_id.pair (polyFun_fst.comp camPoly_dom)).comp
    (PolyFun.filterParam ((ha.pair ((hc.pair (polyFun_snd.pair hi)).comp
      camPoly_row)).comp polyFun_natListMem))

theorem camPoly_pullStar : PolyFun camPullStar := by
  have hbase : PolyFun (fun p : ((RawCameron × RawPerm) × (ℕ × ℕ)) × ℕ => p.1.1) :=
    polyFun_fst.comp polyFun_fst
  have hc := hbase.comp polyFun_fst
  have hg := hbase.comp polyFun_snd
  have hi : PolyFun (fun p : ((RawCameron × RawPerm) × (ℕ × ℕ)) × ℕ => p.1.2.1) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_fst
  have ha : PolyFun (fun p : ((RawCameron × RawPerm) × (ℕ × ℕ)) × ℕ => p.1.2.2) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_snd
  have hx := (hg.pair polyFun_snd).comp polyFun_rawGet
  exact (polyFun_id.pair ((polyFun_fst.comp polyFun_fst).comp camPoly_dom)).comp
    (PolyFun.filterParam ((ha.pair ((hc.pair (hx.pair hi)).comp camPoly_row)).comp
      polyFun_natListMem))

theorem camPoly_coordDom : PolyFun camCoordDom :=
  (camPoly_dom.pair camPoly_s).comp polyFun_rowsBefore

theorem camPoly_pointDom : PolyFun camPointDom :=
  (camPoly_dom.pair camPoly_k).comp polyFun_rowsBefore

theorem camPoly_starDom : PolyFun camStarDom := by
  have hf : PolyFun (fun p : List ℕ × ℕ => p.1.map (fun a => (p.2, a))) :=
    (polyFun_snd.pair polyFun_fst).comp (PolyFun.mapParam polyFun_id)
  exact ((camPoly_pointDom.pair camPoly_coordDom).comp (PolyFun.mapParam hf)).comp
    polyFun_flatten

theorem camPoly_starMatch : PolyFun camStarMatch := by
  have hbase : PolyFun (fun p : ((RawCameron × RawPerm) × (ℕ × ℕ)) × (ℕ × ℕ) =>
      p.1.1) := polyFun_fst.comp polyFun_fst
  have hs := (((hbase.comp polyFun_fst).pair (polyFun_fst.comp polyFun_snd)).comp
    camPoly_star)
  have ht := (hbase.pair polyFun_snd).comp camPoly_pullStar
  exact (hs.pair ht).comp polyFun_listNatEq

theorem camPoly_recover : PolyFun camRecover := by
  have hh := ((polyFun_id.pair ((polyFun_fst.comp polyFun_fst).comp camPoly_starDom)).comp
    (PolyFun.filterParam camPoly_starMatch)).comp polyFun_headOption
  exact ((hh.pair (polyFun_const (0, 0))).comp polyFun_optionGetD).of_eq
    (fun _ => List.headD_eq_head?_getD.symm)

theorem camPoly_pointPerm : PolyFun camPointPerm := by
  have hf : PolyFun (fun p : ((RawCameron × RawPerm) × ℕ) × ℕ =>
      (camRecover (p.1.1, p.1.2, p.2)).2) :=
    (((polyFun_fst.comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_snd).pair polyFun_snd)).comp camPoly_recover).comp
        polyFun_snd
  exact (polyFun_id.pair ((polyFun_fst.comp polyFun_fst).comp camPoly_pointDom)).comp
    (PolyFun.mapParam hf)

/-- Raw row membership is the decoded subset membership. -/
theorem camRow_mem {n : ℕ} {c : RawCameron} (h : c.WF n)
    (x : Fin n) (i : Fin c.s) (a : Fin c.k) :
    a.val ∈ camRow (c, x.val, i.val) ↔ a ∈ (decCameron c h x i).val := by
  have hx : x.val < c.table.length := by rw [h.table_length]; exact x.isLt
  have hi : i.val < c.table[x.val].length := by
    rw [h.tuple_length _ (List.getElem_mem hx)]; exact i.isLt
  change _ ↔ a ∈ rawJSet c.k c.table[x.val][i.val]
  simp only [mem_rawJSet, camRow, List.getD_eq_getElem _ [] hx,
    List.getD_eq_getElem _ [] hi]

theorem camStar_mem {n : ℕ} {c : RawCameron} (h : c.WF n)
    (x : Fin n) (i : Fin c.s) (a : Fin c.k) :
    x.val ∈ camStar (c, i.val, a.val) ↔ a ∈ (decCameron c h x i).val := by
  simp [camStar, camDom, h.table_length, x.isLt, camRow_mem h x i a]

theorem camPullStar_mem {n : ℕ} {c : RawCameron} (h : c.WF n)
    (g : Perm (Fin n)) (x : Fin n) (i : Fin c.s) (a : Fin c.k) :
    x.val ∈ camPullStar ((c, encPerm n g), i.val, a.val) ↔
      a ∈ (decCameron c h (g x) i).val := by
  have hg : rawGet (encPerm n g, x.val) = (g x).val := by
    rw [rawGet, List.getD_eq_getElem (encPerm n g) 0 (by simpa using x.isLt),
      getElem_encPerm n g x.val x.isLt]
  simp [camPullStar, camDom, h.table_length, x.isLt, hg, camRow_mem h (g x) i a]

/-- Incidence columns distinguish coordinate-point pairs. -/
theorem camStar_injective {k t s : ℕ} (ht : 1 ≤ t) (hk : t < k)
    {i j : Fin s} {a b : Fin k}
    (he : ∀ f : Fin s → Babai.binom (Fin k) t, a ∈ (f i).val ↔ b ∈ (f j).val) :
    i = j ∧ a = b := by
  classical
  have hab : a = b := by
    by_contra hn
    obtain ⟨S, ha, hb⟩ := camSubset_separates ht hk hn
    exact hb ((he (fun _ => S)).1 ha)
  subst b
  refine ⟨?_, rfl⟩
  by_contra hij
  have hk2 : 2 ≤ k := by omega
  haveI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 hk2
  obtain ⟨b, hab⟩ := exists_ne a
  obtain ⟨S, ha, _⟩ := camSubset_separates ht hk hab.symm
  obtain ⟨T, _, hna⟩ := camSubset_separates ht hk hab
  have hv := (he (Function.update (fun _ => T) i S)).1
  simp only [Function.update_self, Function.update_of_ne (Ne.symm hij)] at hv
  exact hna (hv ha)

/-- Pullback by a permutation still distinguishes the incidence columns. -/
theorem camPullStar_injective {n : ℕ} {c : RawCameron} (h : c.WF n)
    (g : Perm (Fin n)) {i j : Fin c.s} {a b : Fin c.k}
    (he : camPullStar ((c, encPerm n g), i.val, a.val) =
      camPullStar ((c, encPerm n g), j.val, b.val)) : i = j ∧ a = b := by
  apply camStar_injective h.t_pos (by have := h.k_gt; omega)
  intro f
  let x := g⁻¹ ((decCameron c h).symm f)
  have hv : x.val ∈ camPullStar ((c, encPerm n g), i.val, a.val) ↔
      x.val ∈ camPullStar ((c, encPerm n g), j.val, b.val) := by rw [he]
  rw [camPullStar_mem h g x i a, camPullStar_mem h g x j b] at hv
  simpa [x] using hv

theorem camCoordDom_eq {n : ℕ} {c : RawCameron} (h : c.WF n) :
    camCoordDom c = List.range c.s := by
  rw [camCoordDom, rowsBefore_eq_take, camDom, List.take_range]
  rw [h.table_length, Nat.min_eq_left h.bounds.1]

theorem camPointDom_eq {n : ℕ} {c : RawCameron} (h : c.WF n) :
    camPointDom c = List.range c.k := by
  rw [camPointDom, rowsBefore_eq_take, camDom, List.take_range]
  rw [h.table_length, Nat.min_eq_left h.bounds.2.2]

theorem camStarDom_mem {n : ℕ} {c : RawCameron} (h : c.WF n) (i a : ℕ) :
    (i, a) ∈ camStarDom c ↔ i < c.s ∧ a < c.k := by
  simp [camStarDom, camCoordDom_eq h, camPointDom_eq h]

/-- The returned bijection transports the action to its wreath representation. -/
theorem camWreath_apply {n : ℕ} {c : RawCameron} (h : c.WF n)
    (g : Perm (Fin n)) (p : Fin c.s → Perm (Fin c.k)) (σ : Perm (Fin c.s))
    (he : (Equiv.permCongrHom (decCameron c h)) g =
      Babai.wreathPerm (fun i => Babai.tAction c.t (p i)) σ) (x : Fin n) (i : Fin c.s) :
    decCameron c h (g x) i = Babai.tAction c.t (p i) (decCameron c h x (σ⁻¹ i)) := by
  have hv := congrArg (fun w : Perm (Fin c.s → Babai.binom (Fin c.k) c.t) =>
    w (decCameron c h x) i) he
  simpa using hv

/-- A source column is the pullback of the column at its point image. -/
theorem camStar_image {n : ℕ} {c : RawCameron} (h : c.WF n)
    (g : Perm (Fin n)) (p : Fin c.s → Perm (Fin c.k)) (σ : Perm (Fin c.s))
    (he : (Equiv.permCongrHom (decCameron c h)) g =
      Babai.wreathPerm (fun i => Babai.tAction c.t (p i)) σ)
    (i : Fin c.s) (a : Fin c.k) :
    camStar (c, i.val, a.val) =
      camPullStar ((c, encPerm n g), (σ i).val, (p (σ i) a).val) := by
  unfold camStar camPullStar
  apply List.filter_congr
  intro x hx
  have hxn : x < n := by simpa [camDom, h.table_length] using hx
  let u : Fin n := ⟨x, hxn⟩
  apply decide_eq_decide.2
  rw [camRow_mem h u i a]
  have hg : rawGet (encPerm n g, x) = (g u).val := by
    rw [rawGet, List.getD_eq_getElem (encPerm n g) 0 (by simpa using hxn),
      getElem_encPerm n g x hxn]
  rw [hg, camRow_mem h (g u) (σ i) (p (σ i) a), camWreath_apply h g p σ he]
  simp [Babai.tAction_apply_coe, Finset.mem_image, (p (σ i)).injective.eq_iff]

/-- The scan recovers the unique point and coordinate image. -/
theorem camRecover_spec {n : ℕ} {c : RawCameron} (h : c.WF n)
    (g : Perm (Fin n)) (p : Fin c.s → Perm (Fin c.k)) (σ : Perm (Fin c.s))
    (he : (Equiv.permCongrHom (decCameron c h)) g =
      Babai.wreathPerm (fun i => Babai.tAction c.t (p i)) σ)
    (i : Fin c.s) (a : Fin c.k) :
    camRecover ((c, encPerm n g), i.val, a.val) = ((σ i).val, (p (σ i) a).val) := by
  let L := (camStarDom c).filter (fun q => camStarMatch (((c, encPerm n g), i.val, a.val), q))
  have hm : ((σ i).val, (p (σ i) a).val) ∈ L := by
    apply List.mem_filter.2
    exact ⟨(camStarDom_mem h _ _).2 ⟨(σ i).isLt, (p (σ i) a).isLt⟩,
      by simp only [camStarMatch, decide_eq_true_eq]; exact camStar_image h g p σ he i a⟩
  have hall : ∀ q ∈ L, q = ((σ i).val, (p (σ i) a).val) := by
    intro q hq
    obtain ⟨hdom, ht⟩ := List.mem_filter.1 hq
    obtain ⟨hi, ha⟩ := (camStarDom_mem h q.1 q.2).1 hdom
    have ht' : camStar (c, i.val, a.val) =
        camPullStar ((c, encPerm n g), q.1, q.2) := of_decide_eq_true ht
    have heq := camPullStar_injective h g
      (i := ⟨q.1, hi⟩) (a := ⟨q.2, ha⟩) (j := σ i) (b := p (σ i) a)
      (ht'.symm.trans (camStar_image h g p σ he i a))
    exact Prod.ext (congrArg Fin.val heq.1) (congrArg Fin.val heq.2)
  change L.headD (0, 0) = _
  cases hL : L with
  | nil => simp [hL] at hm
  | cons q qs => exact hall q (by simp [hL])

/-- The recovered row is the full permutation table on the underlying points. -/
theorem camPointPerm_spec {n : ℕ} {c : RawCameron} (h : c.WF n)
    (g : Perm (Fin n)) (p : Fin c.s → Perm (Fin c.k)) (σ : Perm (Fin c.s))
    (he : (Equiv.permCongrHom (decCameron c h)) g =
      Babai.wreathPerm (fun i => Babai.tAction c.t (p i)) σ) (i : Fin c.s) :
    camPointPerm ((c, encPerm n g), i.val) = encPerm c.k (p (σ i)) := by
  apply List.ext_getElem
  · simp [camPointPerm, camPointDom_eq h]
  · intro a ha hb
    have hak : a < c.k := by simpa using hb
    simp only [camPointPerm, camPointDom_eq h, List.getElem_map, List.getElem_range,
      getElem_encPerm c.k (p (σ i)) a hak]
    exact congrArg Prod.snd (camRecover_spec h g p σ he i ⟨a, hak⟩)

end Algo
