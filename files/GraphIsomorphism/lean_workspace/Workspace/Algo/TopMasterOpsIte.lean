import Workspace.Algo.TopMasterRound

/-! # Choosing a carrier by a computed test
Section 15 picks one branch at each node by tests on the node itself. On the
machine this is a single carrier whose five routines first evaluate the test
and then run the chosen branch. The test reads only the node, so the choice
is the same at every step of the node's fold. Hence the chosen branch's
matching carries over unchanged, and the local costs add.
-/
namespace Algo
open RAM RAM.Targets Babai

/-- The carrier that runs `F` at nodes that pass `sel` and `G` at the others. -/
def MasterOps.ite {S : Type} (sel : RawMasterSI → Bool) (F G : MasterOps S) : MasterOps S where
  width p := if sel p then F.width p else G.width p
  child z := if sel z.1 then F.child z else G.child z
  init p := if sel p then F.init p else G.init p
  combine z := if sel z.1 then F.combine z else G.combine z
  finish z := if sel z.1 then F.finish z else G.finish z

/-- The local costs of the two branches add. -/
def MasterOpsCost.ite {S : Type} [Enc S] {a b : ℕ} {sel : RawMasterSI → Bool}
    {F G : MasterOps S} (hsel : PolyFun sel) (CF : MasterOpsCost a b F)
    (CG : MasterOpsCost a b G) : MasterOpsCost a b (MasterOps.ite sel F G) where
  stateBound n := CF.stateBound n + CG.stateBound n
  widthBound n := CF.widthBound n + CG.widthBound n
  quasiPoly_state := CF.quasiPoly_state.add CG.quasiPoly_state
  mono_state := fun _ _ h => Nat.add_le_add (CF.mono_state h) (CG.mono_state h)
  quasiPoly_width := CF.quasiPoly_width.add CG.quasiPoly_width
  quasiFun_width := aggnQuasiFun_ite hsel.quasiFun CF.quasiFun_width CG.quasiFun_width
  quasiFun_child :=
    aggnQuasiFun_ite (polyFun_fst.comp hsel).quasiFun CF.quasiFun_child CG.quasiFun_child
  quasiFun_init := aggnQuasiFun_ite hsel.quasiFun CF.quasiFun_init CG.quasiFun_init
  quasiFun_combine :=
    aggnQuasiFun_ite (polyFun_fst.comp hsel).quasiFun CF.quasiFun_combine CG.quasiFun_combine
  quasiFun_finish :=
    aggnQuasiFun_ite (polyFun_fst.comp hsel).quasiFun CF.quasiFun_finish CG.quasiFun_finish
  init_le p hp := by
    have h1 := CF.init_le p hp
    have h2 := CG.init_le p hp
    change Enc.size (if sel p then F.init p else G.init p) ≤ _
    split <;> omega
  combine_le p j s A hp hA := by
    have h1 := CF.combine_le p j s A hp hA
    have h2 := CG.combine_le p j s A hp hA
    change Enc.size (if sel p then F.combine (p, j, s, A) else G.combine (p, j, s, A)) ≤ _
    split <;> omega
  finish_le p s hp := by
    have h1 := CF.finish_le p s hp
    have h2 := CG.finish_le p s hp
    change Enc.size (if sel p then F.finish (p, s) else G.finish (p, s)) ≤ _
    split <;> assumption
  width_le p hp := by
    have h1 := CF.width_le p hp
    have h2 := CG.width_le p hp
    change (if sel p then F.width p else G.width p) ≤ _
    split <;> omega

section Match
variable {S : Type} {sel : RawMasterSI → Bool} {F G : MasterOps S} {p : RawMasterSI}

theorem MasterOps.ite_width_pos (h : sel p = true) : (MasterOps.ite sel F G).width p = F.width p :=
  if_pos h

theorem MasterOps.ite_init_pos (h : sel p = true) : (MasterOps.ite sel F G).init p = F.init p :=
  if_pos h

theorem MasterOps.ite_width_neg (h : sel p = false) :
    (MasterOps.ite sel F G).width p = G.width p := by
  simp only [MasterOps.ite, h, Bool.false_eq_true, if_false]

theorem MasterOps.ite_init_neg (h : sel p = false) : (MasterOps.ite sel F G).init p = G.init p := by
  simp only [MasterOps.ite, h, Bool.false_eq_true, if_false]

variable {Ω : Type} {A : Type}
    {decI : RawMasterSI → SIInstance Ω A} {decA : RawCoset → Set (Equiv.Perm Ω)}

/-- At a node that passes the test, the combined carrier runs `F` call for call. -/
theorem masterOpsIte_match_pos (a b : ℕ) (h : sel p = true) {w j : ℕ} {s : S}
    {T : SIReduction Ω A (Set (Equiv.Perm Ω))}
    (hm : LoopMatch (masterAdmittedRound a b F) decI decA p w j s T) :
    LoopMatch (masterAdmittedRound a b (MasterOps.ite sel F G)) decI decA p w j s T := by
  have hc : ∀ j s, masterGuardedChild a b (MasterOps.ite sel F G) (p, j, s) =
      masterGuardedChild a b F (p, j, s) := by
    intro j s
    simp only [masterGuardedChild, MasterOps.ite, h, if_true]
  induction hm with
  | done w j s A hch ha =>
    refine .done w j s A ((hc j s).trans hch) ?_
    change decA (if sel p then F.finish (p, s) else G.finish (p, s)) = A
    rw [if_pos h]
    exact ha
  | call w j s J k hch hn ih =>
    refine .call w j s J k ((hc j s).trans hch) (fun B hB => ?_)
    have hu : (masterAdmittedRound a b (MasterOps.ite sel F G)).combine (p, j, s, B) =
        (masterAdmittedRound a b F).combine (p, j, s, B) := if_pos h
    rw [hu]
    exact ih B hB

/-- At a node that fails the test, the combined carrier runs `G` call for call. -/
theorem masterOpsIte_match_neg (a b : ℕ) (h : sel p = false) {w j : ℕ} {s : S}
    {T : SIReduction Ω A (Set (Equiv.Perm Ω))}
    (hm : LoopMatch (masterAdmittedRound a b G) decI decA p w j s T) :
    LoopMatch (masterAdmittedRound a b (MasterOps.ite sel F G)) decI decA p w j s T := by
  have hc : ∀ j s, masterGuardedChild a b (MasterOps.ite sel F G) (p, j, s) =
      masterGuardedChild a b G (p, j, s) := by
    intro j s
    simp only [masterGuardedChild, MasterOps.ite, h, Bool.false_eq_true, if_false]
  induction hm with
  | done w j s A hch ha =>
    refine .done w j s A ((hc j s).trans hch) ?_
    change decA (if sel p then F.finish (p, s) else G.finish (p, s)) = A
    rw [h, if_neg Bool.false_ne_true]
    exact ha
  | call w j s J k hch hn ih =>
    refine .call w j s J k ((hc j s).trans hch) (fun B hB => ?_)
    have hu : (masterAdmittedRound a b (MasterOps.ite sel F G)).combine (p, j, s, B) =
        (masterAdmittedRound a b G).combine (p, j, s, B) := by
      change (if sel p then _ else _) = _
      rw [h, if_neg Bool.false_ne_true]
      rfl
    rw [hu]
    exact ih B hB

/-- The start of the fold at a node that passes the test. -/
theorem masterOpsIte_start_pos (a b : ℕ) (h : sel p = true)
    {T : SIReduction Ω A (Set (Equiv.Perm Ω))}
    (hm : LoopMatch (masterAdmittedRound a b F) decI decA p (F.width p) 0 (F.init p) T) :
    LoopMatch (masterAdmittedRound a b (MasterOps.ite sel F G)) decI decA p
      ((MasterOps.ite sel F G).width p) 0 ((MasterOps.ite sel F G).init p) T := by
  rw [MasterOps.ite_width_pos h, MasterOps.ite_init_pos h]
  exact masterOpsIte_match_pos a b h hm

/-- The start of the fold at a node that fails the test. -/
theorem masterOpsIte_start_neg (a b : ℕ) (h : sel p = false)
    {T : SIReduction Ω A (Set (Equiv.Perm Ω))}
    (hm : LoopMatch (masterAdmittedRound a b G) decI decA p (G.width p) 0 (G.init p) T) :
    LoopMatch (masterAdmittedRound a b (MasterOps.ite sel F G)) decI decA p
      ((MasterOps.ite sel F G).width p) 0 ((MasterOps.ite sel F G).init p) T := by
  rw [MasterOps.ite_width_neg h, MasterOps.ite_init_neg h]
  exact masterOpsIte_match_neg a b h hm
end Match
end Algo

/-! ### Two carriers with different fold states
The state is a pair. The chosen carrier uses its own component, and the other component
stays at a fixed default. -/

namespace Algo
open RAM RAM.Targets Babai

/-- The carrier that runs `F` on the first component at nodes that pass `sel`, and `G` on
the second component at the others. -/
def MasterOps.pairIte {S T : Type} (sel : RawMasterSI → Bool) (F : MasterOps S)
    (G : MasterOps T) (dS : S) (dT : T) : MasterOps (S × T) where
  width p := if sel p then F.width p else G.width p
  child z := if sel z.1 then F.child (z.1, z.2.1, z.2.2.1) else G.child (z.1, z.2.1, z.2.2.2)
  init p := if sel p then (F.init p, dT) else (dS, G.init p)
  combine z := if sel z.1 then (F.combine (z.1, z.2.1, z.2.2.1.1, z.2.2.2), dT)
    else (dS, G.combine (z.1, z.2.1, z.2.2.1.2, z.2.2.2))
  finish z := if sel z.1 then F.finish (z.1, z.2.1) else G.finish (z.1, z.2.2)

/-- The local costs of the two branches add, with the two defaults. The test need only be
quasipolynomial. -/
def MasterOpsCost.pairIteQ {S T : Type} [Enc S] [Enc T] {a b : ℕ} {sel : RawMasterSI → Bool}
    {F : MasterOps S} {G : MasterOps T} {dS : S} {dT : T} (hsel : QuasiFun sel)
    (CF : MasterOpsCost a b F) (CG : MasterOpsCost a b G) :
    MasterOpsCost a b (MasterOps.pairIte sel F G dS dT) where
  stateBound n := 2 * (CF.stateBound n + CG.stateBound n + Enc.size dS + Enc.size dT)
  widthBound n := CF.widthBound n + CG.widthBound n
  quasiPoly_state := (polyBound_const 2).quasiPoly.mul
    (((CF.quasiPoly_state.add CG.quasiPoly_state).add (polyBound_const _).quasiPoly).add
      (polyBound_const _).quasiPoly)
  mono_state := fun _ _ h => Nat.mul_le_mul_left 2 (Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.add_le_add (CF.mono_state h) (CG.mono_state h)) _) _)
  quasiPoly_width := CF.quasiPoly_width.add CG.quasiPoly_width
  quasiFun_width := aggnQuasiFun_ite hsel CF.quasiFun_width CG.quasiFun_width
  quasiFun_child := aggnQuasiFun_ite (polyFun_fst.comp_quasiFun hsel)
    ((polyFun_fst.pair ((polyFun_snd.comp polyFun_fst).pair
      ((polyFun_snd.comp polyFun_snd).comp polyFun_fst))).comp_quasiFun CF.quasiFun_child)
    ((polyFun_fst.pair ((polyFun_snd.comp polyFun_fst).pair
      ((polyFun_snd.comp polyFun_snd).comp polyFun_snd))).comp_quasiFun CG.quasiFun_child)
  quasiFun_init := aggnQuasiFun_ite hsel
    (CF.quasiFun_init.pair (quasiFun_const dT)) ((quasiFun_const dS).pair CG.quasiFun_init)
  quasiFun_combine := aggnQuasiFun_ite (polyFun_fst.comp_quasiFun hsel)
    (((polyFun_fst.pair ((polyFun_snd.comp polyFun_fst).pair
      ((((polyFun_snd.comp polyFun_snd).comp polyFun_fst).comp polyFun_fst).pair
      ((polyFun_snd.comp polyFun_snd).comp polyFun_snd)))).comp_quasiFun
        CF.quasiFun_combine).pair (quasiFun_const dT))
    ((quasiFun_const dS).pair ((polyFun_fst.pair ((polyFun_snd.comp polyFun_fst).pair
      ((((polyFun_snd.comp polyFun_snd).comp polyFun_fst).comp polyFun_snd).pair
      ((polyFun_snd.comp polyFun_snd).comp polyFun_snd)))).comp_quasiFun CG.quasiFun_combine))
  quasiFun_finish := aggnQuasiFun_ite (polyFun_fst.comp_quasiFun hsel)
    ((polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp_quasiFun CF.quasiFun_finish)
    ((polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp_quasiFun CG.quasiFun_finish)
  init_le p hp := by
    have h1 := CF.init_le p hp
    have h2 := CG.init_le p hp
    have h3 := size_pair_le' (F.init p, dT)
    have h4 := size_pair_le' (dS, G.init p)
    change Enc.size (if sel p then (F.init p, dT) else (dS, G.init p)) ≤ _
    split <;> dsimp only at h3 h4 <;> omega
  combine_le p j s A hp hA := by
    have h1 := CF.combine_le p j s.1 A hp hA
    have h2 := CG.combine_le p j s.2 A hp hA
    have h3 := size_pair_le' (F.combine (p, j, s.1, A), dT)
    have h4 := size_pair_le' (dS, G.combine (p, j, s.2, A))
    change Enc.size (if sel p then (F.combine (p, j, s.1, A), dT)
      else (dS, G.combine (p, j, s.2, A))) ≤ _
    split <;> dsimp only at h3 h4 <;> omega
  finish_le p s hp := by
    have h1 := CF.finish_le p s.1 hp
    have h2 := CG.finish_le p s.2 hp
    change Enc.size (if sel p then F.finish (p, s.1) else G.finish (p, s.2)) ≤ _
    split <;> assumption
  width_le p hp := by
    have h1 := CF.width_le p hp
    have h2 := CG.width_le p hp
    change (if sel p then F.width p else G.width p) ≤ _
    split <;> omega

/-- The same, for a polynomial-time test. -/
def MasterOpsCost.pairIte {S T : Type} [Enc S] [Enc T] {a b : ℕ} {sel : RawMasterSI → Bool}
    {F : MasterOps S} {G : MasterOps T} {dS : S} {dT : T} (hsel : PolyFun sel)
    (CF : MasterOpsCost a b F) (CG : MasterOpsCost a b G) :
    MasterOpsCost a b (MasterOps.pairIte sel F G dS dT) :=
  MasterOpsCost.pairIteQ hsel.quasiFun CF CG

section PairMatch
variable {S T : Type} {sel : RawMasterSI → Bool} {F : MasterOps S} {G : MasterOps T}
    {dS : S} {dT : T} {p : RawMasterSI}
variable {Ω : Type} {A : Type}
    {decI : RawMasterSI → SIInstance Ω A} {decA : RawCoset → Set (Equiv.Perm Ω)}

/-- At a node that passes the test, the paired carrier runs `F` call for call. -/
theorem masterPairIte_match_pos (a b : ℕ) (h : sel p = true) {w j : ℕ} {s : S}
    {T' : SIReduction Ω A (Set (Equiv.Perm Ω))}
    (hm : LoopMatch (masterAdmittedRound a b F) decI decA p w j s T') :
    LoopMatch (masterAdmittedRound a b (MasterOps.pairIte sel F G dS dT)) decI decA p w j
      (s, dT) T' := by
  have hc : ∀ j s, masterGuardedChild a b (MasterOps.pairIte sel F G dS dT) (p, j, (s, dT)) =
      masterGuardedChild a b F (p, j, s) := by
    intro j s
    simp only [masterGuardedChild, MasterOps.pairIte, h, if_true]
  induction hm with
  | done w j s A hch ha =>
    refine .done w j (s, dT) A ((hc j s).trans hch) ?_
    change decA (if sel p then F.finish (p, s) else G.finish (p, dT)) = A
    rw [if_pos h]
    exact ha
  | call w j s J k hch hn ih =>
    refine .call w j (s, dT) J k ((hc j s).trans hch) (fun B hB => ?_)
    have hu : (masterAdmittedRound a b (MasterOps.pairIte sel F G dS dT)).combine
        (p, j, (s, dT), B) = ((masterAdmittedRound a b F).combine (p, j, s, B), dT) := if_pos h
    rw [hu]
    exact ih B hB

/-- At a node that fails the test, the paired carrier runs `G` call for call. -/
theorem masterPairIte_match_neg (a b : ℕ) (h : sel p = false) {w j : ℕ} {t : T}
    {T' : SIReduction Ω A (Set (Equiv.Perm Ω))}
    (hm : LoopMatch (masterAdmittedRound a b G) decI decA p w j t T') :
    LoopMatch (masterAdmittedRound a b (MasterOps.pairIte sel F G dS dT)) decI decA p w j
      (dS, t) T' := by
  have hc : ∀ j t, masterGuardedChild a b (MasterOps.pairIte sel F G dS dT) (p, j, (dS, t)) =
      masterGuardedChild a b G (p, j, t) := by
    intro j t
    simp only [masterGuardedChild, MasterOps.pairIte, h, Bool.false_eq_true, if_false]
  induction hm with
  | done w j t A hch ha =>
    refine .done w j (dS, t) A ((hc j t).trans hch) ?_
    change decA (if sel p then F.finish (p, dS) else G.finish (p, t)) = A
    rw [h, if_neg Bool.false_ne_true]
    exact ha
  | call w j t J k hch hn ih =>
    refine .call w j (dS, t) J k ((hc j t).trans hch) (fun B hB => ?_)
    have hu : (masterAdmittedRound a b (MasterOps.pairIte sel F G dS dT)).combine
        (p, j, (dS, t), B) = (dS, (masterAdmittedRound a b G).combine (p, j, t, B)) := by
      change (if sel p then _ else _) = _
      rw [h, if_neg Bool.false_ne_true]
      rfl
    rw [hu]
    exact ih B hB

/-- The start of the fold at a node that passes the test. -/
theorem masterPairIte_start_pos (a b : ℕ) (h : sel p = true)
    {T' : SIReduction Ω A (Set (Equiv.Perm Ω))}
    (hm : LoopMatch (masterAdmittedRound a b F) decI decA p (F.width p) 0 (F.init p) T') :
    LoopMatch (masterAdmittedRound a b (MasterOps.pairIte sel F G dS dT)) decI decA p
      ((MasterOps.pairIte sel F G dS dT).width p) 0
      ((MasterOps.pairIte sel F G dS dT).init p) T' := by
  have hw : (MasterOps.pairIte sel F G dS dT).width p = F.width p := if_pos h
  have hi : (MasterOps.pairIte sel F G dS dT).init p = (F.init p, dT) := if_pos h
  rw [hw, hi]
  exact masterPairIte_match_pos a b h hm

/-- The start of the fold at a node that fails the test. -/
theorem masterPairIte_start_neg (a b : ℕ) (h : sel p = false)
    {T' : SIReduction Ω A (Set (Equiv.Perm Ω))}
    (hm : LoopMatch (masterAdmittedRound a b G) decI decA p (G.width p) 0 (G.init p) T') :
    LoopMatch (masterAdmittedRound a b (MasterOps.pairIte sel F G dS dT)) decI decA p
      ((MasterOps.pairIte sel F G dS dT).width p) 0
      ((MasterOps.pairIte sel F G dS dT).init p) T' := by
  have hw : (MasterOps.pairIte sel F G dS dT).width p = G.width p := by
    change (if sel p then _ else _) = _
    rw [h, if_neg Bool.false_ne_true]
  have hi : (MasterOps.pairIte sel F G dS dT).init p = (dS, G.init p) := by
    change (if sel p then _ else _) = _
    rw [h, if_neg Bool.false_ne_true]
  rw [hw, hi]
  exact masterPairIte_match_neg a b h hm
end PairMatch
end Algo
