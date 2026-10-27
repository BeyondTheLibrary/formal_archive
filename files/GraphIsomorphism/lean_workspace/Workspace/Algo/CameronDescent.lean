import Workspace.Algo.Cameron
import Workspace.Algo.BlockSystem

/-!
# The coordinate blocks in the Cameron descent

Theorem 11.2.1 uses the fibres of the first coordinate of the returned table.
We group the points by their first subset row. Names of rows are their first
positions in the table, so all scans run over input lists.
-/

namespace Algo

open RAM RAM.Targets

/-- Name a row by its first position in a list of rows. -/
def camRowIndex (p : List (List ℕ) × List ℕ) : ℕ :=
  ((p.1.zipIdx).lookup p.2).getD 0

private theorem camLookup_zipIdx {a : List ℕ} {l : List (List ℕ)} (ha : a ∈ l) (k : ℕ) :
    ∃ i, ∃ hi : i < l.length, l[i] = a ∧ (l.zipIdx k).lookup a = some (i + k) := by
  induction l generalizing k with
  | nil => simp at ha
  | cons b l ih =>
    by_cases hab : a = b
    · subst a
      exact ⟨0, by simp, by simp, by simp⟩
    · have hal : a ∈ l := (List.mem_cons.1 ha).resolve_left hab
      obtain ⟨i, hi, hval, hlook⟩ := ih hal (k + 1)
      refine ⟨i + 1, by simpa using hi, by simpa using hval, ?_⟩
      have hbeq : (a == b) = false := beq_eq_false_iff_ne.2 hab
      simpa [List.zipIdx_cons, List.lookup, hbeq, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hlook

theorem camRowIndex_spec {l : List (List ℕ)} {a : List ℕ} (ha : a ∈ l) :
    camRowIndex (l, a) < l.length ∧ l.getD (camRowIndex (l, a)) [] = a := by
  obtain ⟨i, hi, hval, hlook⟩ := camLookup_zipIdx ha 0
  have heq : camRowIndex (l, a) = i := by simp [camRowIndex, hlook]
  rw [heq]
  exact ⟨hi, (List.getD_eq_getElem _ _ hi).trans hval⟩

theorem camRowIndex_eq_iff {l : List (List ℕ)} {a b : List ℕ}
    (ha : a ∈ l) (hb : b ∈ l) : camRowIndex (l, a) = camRowIndex (l, b) ↔ a = b := by
  constructor
  · intro h
    exact (camRowIndex_spec ha).2.symm.trans
      ((congrArg (fun i => l.getD i []) h).trans (camRowIndex_spec hb).2)
  · rintro rfl
    rfl

/-- The first coordinate at every point. -/
def camFirstRows (c : RawCameron) : List (List ℕ) :=
  c.table.map (fun xs => xs.getD 0 [])

/-- Read the first coordinate of one point, with an empty default. -/
def camFirstRow (p : RawCameron × ℕ) : List ℕ := (camFirstRows p.1).getD p.2 []

/-- Points are labelled by their first subset row. -/
def camLab (c : RawCameron) : RawLab :=
  (camFirstRows c).map (fun row => camRowIndex (camFirstRows c, row))

/-- The table supplies the domain witness for every loop. -/
def camDom (c : RawCameron) : List ℕ := List.range c.table.length

/-- The coordinate blocks of Theorem 11.2.1, as a list of lists. -/
def camBlocks (c : RawCameron) : RawBlocks := labBlocks (camDom c, camLab c)

/-- The Johnson hint: one subset row per coordinate block. -/
def camHint (c : RawCameron) : List (List ℕ) :=
  (camBlocks c).map (fun B => camFirstRow (c, blkPt B))

theorem camPoly_rowIndex : PolyFun camRowIndex :=
  (((((polyFun_fst.comp polyFun_zipIdx).pair polyFun_snd).comp
    (polyFun_listLookup polyFun_listNatEq)).pair (polyFun_const 0)).comp polyFun_optionGetD)

theorem camPoly_firstRows : PolyFun camFirstRows :=
  camPoly_table.comp (PolyFun.map
    (((polyFun_id.pair (polyFun_const 0)).pair polyFun_nil).comp polyFun_getD))

theorem camPoly_firstRow : PolyFun camFirstRow :=
  ((((polyFun_fst.comp camPoly_firstRows).pair polyFun_snd).pair polyFun_nil).comp
    polyFun_getD)

theorem camPoly_lab : PolyFun camLab :=
  (camPoly_firstRows.pair camPoly_firstRows).comp (PolyFun.mapParam camPoly_rowIndex)

theorem camPoly_dom : PolyFun camDom := camPoly_table.comp polyFun_rangeLength

theorem camPoly_blocks : PolyFun camBlocks :=
  (camPoly_dom.pair camPoly_lab).comp polyFun_labBlocks

theorem camPoly_hint : PolyFun camHint :=
  (polyFun_id.pair camPoly_blocks).comp
    (PolyFun.mapParam ((polyFun_fst.pair (polyFun_snd.comp polyFun_blkPt)).comp camPoly_firstRow))

theorem camDom_length {n : ℕ} {c : RawCameron} (h : c.WF n) : (camDom c).length = n := by
  simpa only [camDom, List.length_range] using h.table_length

/-- Coordinate blocks have no empty block or repeated point. -/
theorem camBlocks_wf {n : ℕ} {c : RawCameron} (h : c.WF n) : BlocksWF n (camBlocks c) :=
  blocksWF_labBlocks (camDom_length h) _

theorem camFirstRow_spec {n : ℕ} {c : RawCameron} (h : c.WF n) (i : Fin n) :
    (camFirstRow (c, i.val)).SortedLT ∧ (camFirstRow (c, i.val)).length = c.t ∧
      ∀ a ∈ camFirstRow (c, i.val), a < c.k := by
  have hi : i.val < c.table.length := by rw [h.table_length]; exact i.isLt
  have hx := h.tuple_length _ (List.getElem_mem hi)
  have hz : 0 < c.table[i.val].length := by have := h.s_pos; omega
  have heq : camFirstRow (c, i.val) = c.table[i.val][0] := by
    have hm : i.val < (camFirstRows c).length := by simpa [camFirstRows] using hi
    change (camFirstRows c).getD i.val [] = _
    rw [List.getD_eq_getElem _ [] hm]
    simp only [camFirstRows, List.getElem_map, List.getD_eq_getElem _ [] hz]
  rw [heq]
  exact h.rows _ (List.getElem_mem hi) _ (List.getElem_mem hz)

theorem camFirstRow_decode {n : ℕ} {c : RawCameron} (h : c.WF n) (i : Fin n) :
    rawJSet c.k (camFirstRow (c, i.val)) = (decCameron c h i ⟨0, h.s_pos⟩).val := by
  have hi : i.val < c.table.length := by rw [h.table_length]; exact i.isLt
  have hx := h.tuple_length _ (List.getElem_mem hi)
  have hz : 0 < c.table[i.val].length := by have := h.s_pos; omega
  change rawJSet c.k ((camFirstRows c).getD i.val []) = rawJSet c.k c.table[i.val][0]
  have hm : i.val < (camFirstRows c).length := by simpa [camFirstRows] using hi
  rw [List.getD_eq_getElem _ [] hm]
  simp only [camFirstRows, List.getElem_map, List.getD_eq_getElem _ [] hz]

theorem camFirstRow_mem {n : ℕ} {c : RawCameron} (h : c.WF n) (i : Fin n) :
    camFirstRow (c, i.val) ∈ camFirstRows c := by
  have hi : i.val < (camFirstRows c).length := by
    simpa [camFirstRows, h.table_length] using i.isLt
  change (camFirstRows c).getD i.val [] ∈ _
  rw [List.getD_eq_getElem _ [] hi]
  exact List.getElem_mem hi

theorem camLab_at {n : ℕ} {c : RawCameron} (h : c.WF n) (i : Fin n) :
    labAt (camLab c) i.val = camRowIndex (camFirstRows c, camFirstRow (c, i.val)) := by
  have hi : i.val < (camFirstRows c).length := by
    simpa [camFirstRows, h.table_length] using i.isLt
  have hm : i.val < (camLab c).length := by simpa [camLab] using hi
  change (camLab c).getD i.val 0 = _
  rw [List.getD_eq_getElem _ 0 hm]
  simp only [camLab, List.getElem_map, camFirstRow, List.getD_eq_getElem _ [] hi]

/-- Equality of labels is exactly equality of the first decoded coordinate. -/
theorem camLab_rel {n : ℕ} {c : RawCameron} (h : c.WF n) (i j : Fin n) :
    LabRel (camLab c) i.val j.val ↔
      decCameron c h i ⟨0, h.s_pos⟩ = decCameron c h j ⟨0, h.s_pos⟩ := by
  rw [LabRel, camLab_at h i, camLab_at h j,
    camRowIndex_eq_iff (camFirstRow_mem h i) (camFirstRow_mem h j)]
  constructor
  · intro heq
    apply Subtype.ext
    rw [← camFirstRow_decode h i, ← camFirstRow_decode h j, heq]
  · intro heq
    have hi := camFirstRow_spec h i
    have hj := camFirstRow_spec h j
    apply rawJSet_injOn hi.1 hj.1 hi.2.2 hj.2.2
    rw [camFirstRow_decode h i, camFirstRow_decode h j, heq]

/-- The computed block list decodes to the exact fibres used in Theorem 11.2.1. -/
theorem camBlocks_spec {n : ℕ} {c : RawCameron} (h : c.WF n) :
    blockSets n (camBlocks c) = Babai.coordFibres (decCameron c h) ⟨0, h.s_pos⟩ := by
  ext S
  rw [camBlocks, mem_blockSets_labBlocks (camDom_length h)]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨decCameron c h ⟨u, hu⟩ ⟨0, h.s_pos⟩, ?_⟩
    ext x
    exact (camLab_rel h x ⟨u, hu⟩).symm
  · rintro ⟨a, rfl⟩
    let u := (decCameron c h).symm (fun _ => a)
    refine ⟨u.val, u.isLt, ?_⟩
    ext x
    change (decCameron c h x ⟨0, h.s_pos⟩ = a) ↔ LabRel (camLab c) x.val u.val
    rw [camLab_rel h x u]
    simp only [u, Equiv.apply_symm_apply]

/-- The subgroup chosen in the proof of Theorem 11.2.1. This is a specification
object. A raw generating routine must be proved to decode to it. -/
noncomputable def camNbar {n : ℕ} (c : RawCameron) (h : c.WF n) :
    Subgroup (Equiv.Perm (Fin n)) :=
  (Babai.basePower (Babai.JohnsonA c.k c.t) c.s).comap
    (Equiv.permCongrHom (decCameron c h)).toMonoidHom

/-- Normality follows from the two containments of the recognition witness. -/
theorem camNbar_normal {n : ℕ} {c : RawCameron} (h : c.WF n)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (hlo : Babai.basePower (Babai.JohnsonA c.k c.t) c.s ≤
      G.map (Equiv.permCongrHom (decCameron c h)).toMonoidHom)
    (hhi : G.map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ≤
      Babai.wreathProduct (Babai.JohnsonS c.k c.t) c.s) :
    Babai.IsNormalIn (camNbar c h) G := by
  let e := decCameron c h
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hlo hx
    rwa [← (Equiv.permCongrHom e).injective hxy]
  · intro g hg x hx
    have hgW := hhi (Subgroup.mem_map_of_mem (Equiv.permCongrHom e).toMonoidHom hg)
    change (Equiv.permCongrHom e).toMonoidHom (g * x * g⁻¹) ∈
      Babai.basePower (Babai.JohnsonA c.k c.t) c.s
    rw [map_mul, map_mul, map_inv]
    exact (Babai.basePower_isNormalIn_wreathProduct (Babai.johnsonA_le_johnsonS c.k c.t)
      (Babai.johnsonA_conj_mem c.k c.t) c.s).conj_mem _ hgW _ hx

/-- The computed blocks form a system for the alternating base group. -/
theorem camBlocks_system {n : ℕ} {c : RawCameron} (h : c.WF n) :
    Babai.IsSystemOfImprimitivity (camNbar c h) Set.univ (blockSets n (camBlocks c)) := by
  letI : Nonempty (Babai.binom (Fin c.k) c.t) := Babai.binom_nonempty (by have := h.k_gt; omega)
  rw [camBlocks_spec h]
  apply Babai.coordFibres_isSystemOfImprimitivity
    (decCameron c h) ⟨0, h.s_pos⟩
  · exact Subgroup.map_comap_eq_self_of_surjective
      (Equiv.permCongrHom (decCameron c h)).surjective _
  · exact fun a b => Babai.johnsonA_exists_smul h.t_pos h.k_gt a b

/-- On these blocks the alternating base group acts as exactly `A_k^(t)`. -/
theorem camBlocks_acts {n : ℕ} {c : RawCameron} (h : c.WF n) :
    Babai.ActsAsJohnsonA (camNbar c h) (blockSets n (camBlocks c))
      (camBlocks_system h).permutes c.k c.t := by
  have hmap : (camNbar c h).map
      (Equiv.permCongrHom (decCameron c h)).toMonoidHom =
        Babai.basePower (Babai.JohnsonA c.k c.t) c.s :=
    Subgroup.map_comap_eq_self_of_surjective
      (Equiv.permCongrHom (decCameron c h)).surjective _
  have key : ∀ (B : Set (Set (Fin n))),
      B = Babai.coordFibres (decCameron c h) ⟨0, h.s_pos⟩ →
      ∀ hp : ∀ σ ∈ camNbar c h, ∀ S ∈ B, (σ : Equiv.Perm (Fin n)) '' S ∈ B,
        Babai.ActsAsJohnsonA (camNbar c h) B hp c.k c.t := by
    intro B heq hp
    subst B
    exact Babai.coordFibres_onBlocks (decCameron c h) ⟨0, h.s_pos⟩ hmap hp
  exact key _ (camBlocks_spec h) (camBlocks_system h).permutes

/-- A point in the block at index `i`, read from that block's first entry. -/
def camBlockPoint {n : ℕ} {c : RawCameron} (h : c.WF n)
    (i : Fin (camBlocks c).length) : Fin n :=
  ⟨blkPt (camBlocks c)[i.val], (camBlocks_wf h).lt _
    (mem_flatten_getElem i.isLt (blkPt_mem
      ((camBlocks_wf h).nonempty _ (List.getElem_mem i.isLt))))⟩

/-- The subset attached to a block, read at the chosen point in that block. -/
noncomputable def camHintValue {n : ℕ} {c : RawCameron} (h : c.WF n)
    (i : Fin (camBlocks c).length) : Babai.binom (Fin c.k) c.t :=
  decCameron c h (camBlockPoint h i) ⟨0, h.s_pos⟩

/-- A block is the fibre over its attached subset. -/
theorem camHintValue_fibre {n : ℕ} {c : RawCameron} (h : c.WF n)
    (i : Fin (camBlocks c).length) :
    winSet n (camBlocks c)[i.val] =
      Babai.coordFibre (decCameron c h) ⟨0, h.s_pos⟩ (camHintValue h i) := by
  have hm := mem_blockSets_getElem (n := n) (bl := camBlocks c) i.isLt
  rw [camBlocks_spec h] at hm
  obtain ⟨a, ha⟩ := hm
  have hpt : camBlockPoint h i ∈ winSet n (camBlocks c)[i.val] :=
    blkPt_mem ((camBlocks_wf h).nonempty _ (List.getElem_mem i.isLt))
  rw [← ha] at hpt
  change camHintValue h i = a at hpt
  rw [hpt]
  exact ha.symm

/-- Every subset is the label of exactly one block. -/
theorem camHintValue_bijective {n : ℕ} {c : RawCameron} (h : c.WF n) :
    Function.Bijective (camHintValue h) := by
  constructor
  · intro i j hij
    apply (bijective_blockFun (camBlocks_wf h)).1
    apply Subtype.ext
    change winSet n (camBlocks c)[i.val] = winSet n (camBlocks c)[j.val]
    rw [camHintValue_fibre h i, camHintValue_fibre h j, hij]
  · intro a
    have ha : Babai.coordFibre (decCameron c h) ⟨0, h.s_pos⟩ a ∈
        blockSets n (camBlocks c) := by
      rw [camBlocks_spec h]
      exact ⟨a, rfl⟩
    obtain ⟨i, hi⟩ := (bijective_blockFun (camBlocks_wf h)).2 ⟨_, ha⟩
    refine ⟨i, Babai.coordFibre_injective (decCameron c h) ⟨0, h.s_pos⟩ ?_⟩
    rw [← camHintValue_fibre h i]
    exact congrArg Subtype.val hi

/-- The Johnson identification, with block indices as its domain. -/
noncomputable def camHintEquiv {n : ℕ} {c : RawCameron} (h : c.WF n) :
    Fin (camBlocks c).length ≃ Babai.binom (Fin c.k) c.t :=
  Equiv.ofBijective (camHintValue h) (camHintValue_bijective h)

/-- The raw Johnson hint is the table of this identification. -/
theorem camHint_spec {n : ℕ} {c : RawCameron} (h : c.WF n)
    (i : Fin (camBlocks c).length) :
    rawJSet c.k ((camHint c)[i.val]'(by simpa [camHint] using i.isLt)) =
      (camHintEquiv h i).val := by
  change rawJSet c.k ((camBlocks c).map _)[i.val] = _
  rw [List.getElem_map]
  exact camFirstRow_decode h (camBlockPoint h i)

/-- The group on the minimal blocks is the input to the Cameron routine. -/
def camBlockInput (p : RawGens × List ℕ) : RawGens × List ℕ :=
  (rawBlockImgs (rawMinBlocks p, p.1), blkDom (rawMinBlocks p))

theorem camPoly_blockInput : PolyFun camBlockInput :=
  (((polyFun_rawMinBlocks.pair polyFun_fst).comp polyFun_rawBlockImgs).pair
    (polyFun_rawMinBlocks.comp polyFun_blkDom))

/-- Step 6 of Reduce-to-Johnson calls recognition on the action on minimal blocks. -/
def camRecognizeBlocks (cameron : RawGens × List ℕ → Option RawCameron)
    (p : RawGens × List ℕ) : Option RawCameron := cameron (camBlockInput p)

theorem camPoly_recognizeBlocks
    (cameron : RawGens × List ℕ → Option RawCameron)
    (hpoly : PolyFun cameron) (hspec : CameronSpec cameron) :
    PolyFun (camRecognizeBlocks cameron) := camPoly_blockInput.comp hpoly

/-- The computed action on minimal blocks has well-formed generators. -/
theorem camBlockInput_wf {n : ℕ} {gs : RawGens} {dom : List ℕ}
    (hw : RawGens.WF n gs) (hd : dom.length = n)
    (htr : Babai.IsTransitive (decGroup n gs)) (hn : 2 ≤ n) :
    RawGens.WF (camBlockInput (gs, dom)).2.length (camBlockInput (gs, dom)).1 := by
  have hraw : (gs.map (decPerm n)).map (encPerm n) = gs := map_encPerm_decPerm hw
  have hh := (blockData_rawMinBlocks (gens := gs.map (decPerm n)) hd htr hn).1
  rw [hraw] at hh
  simpa only [camBlockInput, length_blkDom] using hh

/-- The output on the block action gives the typed subgroup and the computed
block system needed in `DescentData`. The raw generators of this subgroup are
still a separate obligation. -/
theorem camRecognizeBlocks_fields
    (cameron : RawGens × List ℕ → Option RawCameron)
    (hpoly : PolyFun cameron) (hspec : CameronSpec cameron)
    {n : ℕ} {gs : RawGens} {dom : List ℕ}
    (hw : RawGens.WF n gs) (hd : dom.length = n)
    (htr : Babai.IsTransitive (decGroup n gs)) (hn : 2 ≤ n)
    (hp : Babai.IsPrimitive
      (decGroup (camBlockInput (gs, dom)).2.length (camBlockInput (gs, dom)).1))
    (hm : 25 ≤ (camBlockInput (gs, dom)).2.length)
    (hb : ((camBlockInput (gs, dom)).2.length : ℝ) ^
        (1 + Real.logb 2 (camBlockInput (gs, dom)).2.length) ≤
      Nat.card (decGroup (camBlockInput (gs, dom)).2.length (camBlockInput (gs, dom)).1)) :
    ∃ (c : RawCameron) (h : c.WF (camBlockInput (gs, dom)).2.length),
      camRecognizeBlocks cameron (gs, dom) = some c ∧
      Babai.IsNormalIn (camNbar c h)
        (decGroup (camBlockInput (gs, dom)).2.length (camBlockInput (gs, dom)).1) ∧
      Babai.IsSystemOfImprimitivity (camNbar c h) Set.univ
        (blockSets (camBlockInput (gs, dom)).2.length (camBlocks c)) ∧
      Babai.ActsAsJohnsonA (camNbar c h)
        (blockSets (camBlockInput (gs, dom)).2.length (camBlocks c))
        (camBlocks_system h).permutes c.k c.t ∧ 1 ≤ c.t ∧ 2 * c.t < c.k := by
  obtain ⟨c, h, heq, hR, hlo, hhi⟩ :=
    hspec _ _ _ rfl (camBlockInput_wf hw hd htr hn) hm hp hb
  exact ⟨c, h, heq, camNbar_normal h _ hlo hhi,
    camBlocks_system h, camBlocks_acts h, h.t_pos, h.k_gt⟩

/-- The index estimate in Theorem 11.2.1 for the subgroup determined by the
returned bijection. The proof is the wreath-product count used in that theorem. -/
theorem camNbar_index_le {n : ℕ} {c : RawCameron} (h : c.WF n)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (hlo : Babai.basePower (Babai.JohnsonA c.k c.t) c.s ≤
      G.map (Equiv.permCongrHom (decCameron c h)).toMonoidHom)
    (hhi : G.map (Equiv.permCongrHom (decCameron c h)).toMonoidHom ≤
      Babai.wreathProduct (Babai.JohnsonS c.k c.t) c.s)
    (hsk : 2 * c.s ≤ c.k) : (camNbar c h).relIndex G ≤ n := by
  classical
  let s := c.s
  let t := c.t
  let k := c.k
  let e := decCameron c h
  letI : Nonempty (Babai.binom (Fin k) t) := Babai.binom_nonempty (by have := h.k_gt; omega)
  have hk5 : 5 ≤ k := (le_max_right _ _).trans h.k_max
  have hmapN : (camNbar c h).map (Equiv.permCongrHom e).toMonoidHom =
      Babai.basePower (Babai.JohnsonA k t) s :=
    Subgroup.map_comap_eq_self_of_surjective (Equiv.permCongrHom e).surjective _
  have hPhi : Function.Injective (Equiv.permCongrHom e).toMonoidHom :=
    (Equiv.permCongrHom e).injective
  have hrel := Subgroup.relIndex_map_map_of_injective (camNbar c h) G hPhi
  rw [hmapN] at hrel
  have hPW := hlo.trans hhi
  have hmul := Subgroup.relIndex_mul_relIndex (Babai.basePower (Babai.JohnsonA k t) s)
    (G.map (Equiv.permCongrHom e).toMonoidHom)
    (Babai.wreathProduct (Babai.JohnsonS k t) s) hlo hhi
  have hlag := Babai.relIndex_mul_card_of_le hPW
  have hcardP : Nat.card (Babai.basePower (Babai.JohnsonA k t) s) =
      Nat.card (Babai.JohnsonA k t) ^ s := Babai.card_basePower _ _
  have hApos : 0 < Nat.card (Babai.JohnsonA k t) ^ s := pow_pos Nat.card_pos s
  have hWle : (Babai.basePower (Babai.JohnsonA k t) s).relIndex
      (Babai.wreathProduct (Babai.JohnsonS k t) s) * Nat.card (Babai.JohnsonA k t) ^ s ≤
      (2 ^ s * Nat.factorial s) * Nat.card (Babai.JohnsonA k t) ^ s := by
    calc (Babai.basePower (Babai.JohnsonA k t) s).relIndex
          (Babai.wreathProduct (Babai.JohnsonS k t) s) * Nat.card (Babai.JohnsonA k t) ^ s
        = Nat.card (Babai.wreathProduct (Babai.JohnsonS k t) s) := by
          rw [← hcardP]; exact hlag
      _ ≤ Nat.card (Babai.JohnsonS k t) ^ s * Nat.factorial s :=
          Babai.card_wreathProduct_le _ _
      _ ≤ (2 * Nat.card (Babai.JohnsonA k t)) ^ s * Nat.factorial s :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left
            (Babai.card_johnsonS_le_two_mul (by omega) t) s)
      _ = (2 ^ s * Nat.factorial s) * Nat.card (Babai.JohnsonA k t) ^ s := by
          rw [mul_pow]; ring
  have hPWle := Nat.le_of_mul_le_mul_right hWle hApos
  have hWne : (Babai.basePower (Babai.JohnsonA k t) s).relIndex
      (Babai.wreathProduct (Babai.JohnsonS k t) s) ≠ 0 := by
    intro h0
    change (Babai.basePower (Babai.JohnsonA k t) s).relIndex
      (Babai.wreathProduct (Babai.JohnsonS k t) s) * _ = _ at hlag
    rw [h0, zero_mul] at hlag
    exact (Nat.ne_of_gt (Nat.card_pos
      (α := Babai.wreathProduct (Babai.JohnsonS k t) s))) hlag.symm
  have hpos : 0 < (G.map (Equiv.permCongrHom e).toMonoidHom).relIndex
      (Babai.wreathProduct (Babai.JohnsonS k t) s) := by
    rcases Nat.eq_zero_or_pos ((G.map (Equiv.permCongrHom e).toMonoidHom).relIndex
        (Babai.wreathProduct (Babai.JohnsonS k t) s)) with h0 | hp
    · exact absurd (by rw [h0, mul_zero] at hmul; exact hmul.symm) hWne
    · exact hp
  have hrelle := Nat.le_mul_of_pos_right
    ((Babai.basePower (Babai.JohnsonA k t) s).relIndex
      (G.map (Equiv.permCongrHom e).toMonoidHom)) hpos
  rw [hmul] at hrelle
  have hfin : 2 ^ s * Nat.factorial s ≤ n := by
    calc 2 ^ s * Nat.factorial s ≤ 2 ^ s * s ^ s :=
          Nat.mul_le_mul_left _ (Nat.factorial_le_pow s)
      _ = (2 * s) ^ s := (mul_pow 2 s s).symm
      _ ≤ k ^ s := Nat.pow_le_pow_left hsk s
      _ ≤ (k.choose t) ^ s :=
          Nat.pow_le_pow_left (Babai.self_le_choose h.t_pos h.k_gt) s
      _ = n := h.card.symm
  rw [← hrel]
  exact (hrelle.trans hPWle).trans hfin

/-- The absolute threshold from Proposition 11.2.5. It does not occur in
`CameronSpec`, whose threshold is exactly the `25` of Theorem 11.2.3. -/
noncomputable def camDescentThreshold : ℕ := Babai.Proposition_11_2_5.{0}.choose

/-- The returned witness also gives the index and parameter bounds of
Theorem 11.2.1, above its absolute threshold. -/
theorem camRecognize_index
    (cameron : RawGens × List ℕ → Option RawCameron)
    (hpoly : PolyFun cameron) (hspec : CameronSpec cameron)
    (n : ℕ) (gs : RawGens) (dom : List ℕ) (hd : dom.length = n)
    (hw : RawGens.WF n gs) (hn : 25 ≤ n) (hn0 : camDescentThreshold ≤ n)
    (hp : Babai.IsPrimitive (decGroup n gs))
    (hb : (n : ℝ) ^ (1 + Real.logb 2 n) ≤ Nat.card (decGroup n gs)) :
    ∃ (c : RawCameron) (h : c.WF n), cameron (gs, dom) = some c ∧
      (camNbar c h).relIndex (decGroup n gs) ≤ n ∧ Real.logb 2 n ≤ (c.k : ℝ) := by
  obtain ⟨c, h, heq, hR, hlo, hhi⟩ := hspec n gs dom hd hw hn hp hb
  have hC : Babai.IsCameronGroup (decGroup n gs) c.s c.t c.k :=
    ⟨h.s_pos, h.t_pos, h.k_max, h.k_gt, by simpa using h.card,
      hR, decCameron c h, hlo, hhi⟩
  have hh := Babai.Proposition_11_2_5.{0}.choose_spec (Fin n) (decGroup n gs)
    c.s c.t c.k (by simpa only [camDescentThreshold, Fintype.card_fin] using hn0) hC (by simpa using hb)
  have hlog : Real.logb 2 n ≤ (c.k : ℝ) := by simpa using hh.1
  have hsk : 2 * c.s ≤ c.k := by
    have hskR : (2 * c.s : ℝ) ≤ (c.k : ℝ) :=
      (Babai.two_mul_le_logb hC).trans hh.1
    exact_mod_cast hskR
  exact ⟨c, h, heq, camNbar_index_le h _ hlo hhi hsk, hlog⟩

/-- Images on the coordinate blocks, from any supplied generating list. -/
def camBlockAction (p : RawCameron × RawGens) : RawGens :=
  rawBlockImgs (camBlocks p.1, p.2)

theorem camPoly_blockAction : PolyFun camBlockAction :=
  (((polyFun_fst.comp camPoly_blocks).pair polyFun_snd).comp polyFun_rawBlockImgs)

/-- Once generators of the alternating base group are available, their computed
block images supply the `ImgsOf` datum for the Johnson action. -/
theorem camBlockAction_spec {n : ℕ} {c : RawCameron} (h : c.WF n)
    (gs : RawGens) (hw : RawGens.WF n gs) (hN : decGroup n gs = camNbar c h) :
    RawGens.WF (camBlocks c).length (camBlockAction (c, gs)) ∧
      ∃ phi : genGroup (gs.map (decPerm n)) →* Equiv.Perm (Fin (camBlocks c).length),
        ImgsOf (gs.map (decPerm n))
          ((camBlockAction (c, gs)).map (decPerm (camBlocks c).length)) phi := by
  have hp : ∀ σ ∈ genGroup (gs.map (decPerm n)), ∀ B ∈ blockSets n (camBlocks c),
      (σ : Equiv.Perm (Fin n)) '' B ∈ blockSets n (camBlocks c) := by
    intro σ hs B hB
    apply (camBlocks_system h).permutes σ _ B hB
    rw [← hN]
    exact hs
  have hh := (blockData_of_permutes (camBlocks_wf h) hp).1
  simpa only [BlockData, blockImgsOf, map_encPerm_decPerm hw, camBlockAction] using hh

end Algo
