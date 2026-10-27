import Workspace.Algo.FamilyEvaluator

/-! A family evaluator moves answers from a child into its parent.
Only initialization creates new entries. Thus a bound on each local
family bounds the total number of entries stored along the run. -/
namespace Algo
open RAM
namespace Round
variable {ι β : Type*} (R : Round ι (List β) (List β))

def FamilyNodes (P : ι → Prop) (x : EvalState ι (List β) (List β)) : Prop :=
  ∀ fr ∈ x.1,P fr.1

def familyMass (x : EvalState ι (List β) (List β)) : ℕ :=
  (x.1.map (fun fr => fr.2.2.length)).sum + (x.2.getD []).length

theorem familyNodes_step (P : ι → Prop)
    (hp : ∀ I j s J,P I → R.child (I,j,s) = some J → P J)
    {x : EvalState ι (List β) (List β)} (hx : FamilyNodes P x) :
    FamilyNodes P (R.stepDFS x) := by
  rcases x with ⟨st,ret⟩
  cases st with
  | nil => exact hx
  | cons fr rest =>
    rcases fr with ⟨I,j,s⟩
    have hI := hx _ (List.mem_cons_self)
    have hrest : ∀ fr ∈ rest,P fr.1 := fun fr hf => hx fr (List.mem_cons_of_mem _ hf)
    cases ret with
    | some a =>
      intro fr hf
      rcases List.mem_cons.1 hf with rfl | hf
      · exact hI
      · exact hrest _ hf
    | none =>
      cases hc : R.child (I,j,s) with
      | none =>
        rw [R.stepDFS_pop rest hc]
        exact hrest
      | some J =>
        rw [R.stepDFS_push rest hc]
        intro fr hf
        rcases List.mem_cons.1 hf with rfl | hf
        · exact hp I j s J hI hc
        · exact hx fr hf

theorem familyNodes_iterate (P : ι → Prop)
    (hp : ∀ I j s J,P I → R.child (I,j,s) = some J → P J)
    {I : ι} (hI : P I) (t : ℕ) :
    FamilyNodes P (R.stepDFS^[t] (R.startState I)) := by
  induction t with
  | zero => intro fr hf; exact (List.mem_singleton.1 hf) ▸ hI
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact R.familyNodes_step P hp ih

theorem familyMass_step_le (P : ι → Prop) (L : ℕ)
    (hinit : ∀ I,P I → (R.init I).length ≤ L)
    (hfinish : ∀ I s,P I → (R.finish (I,s)).length ≤ s.length)
    (hcombine : ∀ I j s a,P I → (R.combine (I,j,s,a)).length ≤ s.length+a.length)
    (hp : ∀ I j s J,P I → R.child (I,j,s) = some J → P J)
    {x : EvalState ι (List β) (List β)} (hx : FamilyNodes P x) :
    familyMass (R.stepDFS x) ≤ familyMass x + L := by
  rcases x with ⟨st,ret⟩
  cases st with
  | nil => simp [familyMass]
  | cons fr rest =>
    rcases fr with ⟨I,j,s⟩
    have hI := hx _ (List.mem_cons_self)
    cases ret with
    | some a =>
      rw [R.stepDFS_some]
      have hh := hcombine I j s a hI
      simp only [familyMass,List.map_cons,List.sum_cons,Option.getD_none,Option.getD_some,List.length_nil]
      omega
    | none =>
      cases hc : R.child (I,j,s) with
      | none =>
        rw [R.stepDFS_pop rest hc]
        have hh := hfinish I s hI
        simp only [familyMass,List.map_cons,List.sum_cons,Option.getD_none,Option.getD_some,List.length_nil]
        omega
      | some J =>
        rw [R.stepDFS_push rest hc]
        have hh := hinit J (hp I j s J hI hc)
        simp only [familyMass,List.map_cons,List.sum_cons,Option.getD_none,List.length_nil]
        omega

theorem familyMass_iterate_le (P : ι → Prop) (L : ℕ)
    (hinit : ∀ I,P I → (R.init I).length ≤ L)
    (hfinish : ∀ I s,P I → (R.finish (I,s)).length ≤ s.length)
    (hcombine : ∀ I j s a,P I → (R.combine (I,j,s,a)).length ≤ s.length+a.length)
    (hp : ∀ I j s J,P I → R.child (I,j,s) = some J → P J)
    {I : ι} (hI : P I) (t : ℕ) :
    familyMass (R.stepDFS^[t] (R.startState I)) ≤ (t+1)*L := by
  induction t with
  | zero => simpa [familyMass,startState] using hinit I hI
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have hh := R.familyMass_step_le P L hinit hfinish hcombine hp
      (R.familyNodes_iterate P hp hI t)
    nlinarith

theorem familyMass_frame_le {x : EvalState ι (List β) (List β)}
    {fr : Frame ι (List β)} (hf : fr ∈ x.1) : fr.2.2.length ≤ familyMass x := by
  have hh := List.single_le_sum (fun _ _ => Nat.zero_le _) fr.2.2.length
    (List.mem_map_of_mem (f := fun fr : Frame ι (List β) => fr.2.2.length) hf)
  unfold familyMass
  omega

theorem familyMass_return_le {x : EvalState ι (List β) (List β)}
    {a : List β} (ha : x.2 = some a) : a.length ≤ familyMass x := by
  simp [familyMass,ha]

def FamilyGood (G : ℕ → β → Prop) (t : ℕ) (x : EvalState ι (List β) (List β)) : Prop :=
  (∀ fr ∈ x.1,∀ a ∈ fr.2.2,G t a) ∧ (∀ A,x.2 = some A → ∀ a ∈ A,G t a)

theorem familyGood_step (P : ι → Prop) (G : ℕ → β → Prop)
    (hmono : ∀ t a,G t a → G (t+1) a)
    (hinit : ∀ I,P I → ∀ t a,a ∈ R.init I → G t a)
    (hfinish : ∀ I s,P I → ∀ t,(∀ a ∈ s,G t a) → ∀ a ∈ R.finish (I,s),G t a)
    (hcombine : ∀ I j s A,P I → ∀ t,(∀ a ∈ s,G t a) → (∀ a ∈ A,G t a) →
      ∀ a ∈ R.combine (I,j,s,A),G (t+1) a)
    (hp : ∀ I j s J,P I → R.child (I,j,s) = some J → P J)
    {t : ℕ} {x : EvalState ι (List β) (List β)}
    (hx : FamilyNodes P x) (hg : FamilyGood G t x) : FamilyGood G (t+1) (R.stepDFS x) := by
  rcases x with ⟨st,ret⟩
  cases st with
  | nil =>
    exact ⟨fun fr hf => by simp at hf,fun A hA a ha => hmono _ _ (hg.2 A hA a ha)⟩
  | cons fr rest =>
    rcases fr with ⟨I,j,s⟩
    have hI := hx _ List.mem_cons_self
    have hs := hg.1 _ List.mem_cons_self
    have hr : ∀ fr ∈ rest,∀ a ∈ fr.2.2,G (t+1) a :=
      fun fr hf a ha => hmono _ _ (hg.1 fr (List.mem_cons_of_mem _ hf) a ha)
    cases ret with
    | some A =>
      rw [R.stepDFS_some]
      refine ⟨?_,fun A hA => by cases hA⟩
      intro fr hf
      rcases List.mem_cons.1 hf with rfl | hf
      · exact hcombine I j s A hI t hs (hg.2 A rfl)
      · exact hr fr hf
    | none =>
      cases hc : R.child (I,j,s) with
      | none =>
        rw [R.stepDFS_pop rest hc]
        refine ⟨hr,?_⟩
        intro A hA
        cases Option.some.inj hA
        exact fun a ha => hmono _ _ (hfinish I s hI t hs a ha)
      | some J =>
        rw [R.stepDFS_push rest hc]
        refine ⟨?_,fun A hA => by cases hA⟩
        intro fr hf
        rcases List.mem_cons.1 hf with rfl | hf
        · exact hinit J (hp I j s J hI hc) (t+1)
        · exact fun a ha => hmono _ _ (hg.1 fr hf a ha)

theorem familyGood_iterate (P : ι → Prop) (G : ℕ → β → Prop)
    (hmono : ∀ t a,G t a → G (t+1) a)
    (hinit : ∀ I,P I → ∀ t a,a ∈ R.init I → G t a)
    (hfinish : ∀ I s,P I → ∀ t,(∀ a ∈ s,G t a) → ∀ a ∈ R.finish (I,s),G t a)
    (hcombine : ∀ I j s A,P I → ∀ t,(∀ a ∈ s,G t a) → (∀ a ∈ A,G t a) →
      ∀ a ∈ R.combine (I,j,s,A),G (t+1) a)
    (hp : ∀ I j s J,P I → R.child (I,j,s) = some J → P J)
    {I : ι} (hI : P I) (t : ℕ) :
    FamilyGood G t (R.stepDFS^[t] (R.startState I)) := by
  induction t with
  | zero =>
    refine ⟨?_,fun A hA => by cases hA⟩
    intro fr hf
    cases List.mem_singleton.1 hf
    exact hinit I hI 0
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact R.familyGood_step P G hmono hinit hfinish hcombine hp
      (R.familyNodes_iterate P hp hI t) ih

theorem family_indices_iterate (I : ι) (t : ℕ) :
    (R.stepDFS^[t] (R.startState I)).1.length ≤ t+1 ∧
    ∀ fr ∈ (R.stepDFS^[t] (R.startState I)).1,fr.2.1 ≤ t := by
  induction t with
  | zero => simp [startState]
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    generalize he : R.stepDFS^[t] (R.startState I) = x at ih ⊢
    rcases x with ⟨st,ret⟩
    cases st with
    | nil => simp [stepDFS]
    | cons fr rest =>
      rcases fr with ⟨J,j,s⟩
      have hj := ih.2 _ List.mem_cons_self
      change j ≤ t at hj
      have hlen : rest.length+1 ≤ t+1 := ih.1
      cases ret with
      | some A =>
        rw [R.stepDFS_some]
        refine ⟨by simp only [List.length_cons]; omega,?_⟩
        intro fr hf
        rcases List.mem_cons.1 hf with rfl | hf
        · exact Nat.add_le_add_right hj 1
        · exact (ih.2 _ (List.mem_cons_of_mem _ hf)).trans (by omega)
      | none =>
        cases hc : R.child (J,j,s) with
        | none =>
          rw [R.stepDFS_pop rest hc]
          exact ⟨show rest.length ≤ t+1+1 by omega,
            fun fr hf => (ih.2 _ (List.mem_cons_of_mem _ hf)).trans (by omega)⟩
        | some K =>
          rw [R.stepDFS_push rest hc]
          refine ⟨by simp only [List.length_cons]; omega,?_⟩
          intro fr hf
          rcases List.mem_cons.1 hf with rfl | hf
          · exact Nat.zero_le _
          · exact (ih.2 _ hf).trans (by omega)

def familyListBound (M B : ℕ) : ℕ := 1+M*(2*B+1)
def familyFrameBound (K t M B : ℕ) : ℕ := 2*K+4*(t+2)+4*familyListBound M B
def familyStateBound (K t M B D : ℕ) : ℕ :=
  2*(1+D*(2*familyFrameBound K t M B+1))+2*(familyListBound M B+2)

theorem size_familyState_le [Enc ι] [Enc β] {x : EvalState ι (List β) (List β)}
    {K t M B D : ℕ} (hnode : ∀ fr ∈ x.1,Enc.size fr.1 ≤ K)
    (hindex : ∀ fr ∈ x.1,fr.2.1 ≤ t)
    (hgood : FamilyGood (fun _ a => Enc.size a ≤ B) 0 x)
    (hmass : familyMass x ≤ M) (hdepth : x.1.length ≤ D) :
    Enc.size x ≤ familyStateBound K t M B D := by
  have hlist (A : List β) (hA : A.length ≤ M) (hB : ∀ a ∈ A,Enc.size a ≤ B) :
      Enc.size A ≤ familyListBound M B :=
    (size_list_le_of_entries A B hB).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ hA) 1)
  have hframe : ∀ fr ∈ x.1,Enc.size fr ≤ familyFrameBound K t M B := by
    intro fr hf
    have hs := hlist fr.2.2 ((familyMass_frame_le hf).trans hmass) (hgood.1 fr hf)
    have hi := (size_le_self fr.2.1).trans (hindex fr hf)
    have hI := hnode fr hf
    have hp := Combine.size_pair_le fr.2.1 fr.2.2
    have hq := Combine.size_pair_le fr.1 fr.2
    change Enc.size fr.2 ≤ _ at hp
    change Enc.size fr ≤ _ at hq
    rw [Small.size_nat] at hp
    unfold familyFrameBound
    omega
  have hstack := size_list_le_of_entries x.1 (familyFrameBound K t M B) hframe
  have hd := Nat.mul_le_mul_right (2*familyFrameBound K t M B+1) hdepth
  have hret : Enc.size x.2 ≤ familyListBound M B+2 := by
    cases he : x.2 with
    | none => rw [size_none_eq]; omega
    | some A =>
      rw [size_some_eq]
      exact Nat.add_le_add_right
        (hlist A ((familyMass_return_le he).trans hmass) (hgood.2 A he)) 2
  have hp := Combine.size_pair_le x.1 x.2
  change Enc.size x ≤ _ at hp
  unfold familyStateBound
  omega

theorem quasiPolyBound_familyStateBound {K T M B D : ℕ → ℕ}
    (hK : QuasiPolyBound K) (hT : QuasiPolyBound T) (hM : QuasiPolyBound M)
    (hB : QuasiPolyBound B) (hD : QuasiPolyBound D) :
    QuasiPolyBound (fun n => familyStateBound (K n) (T n) (M n) (B n) (D n)) := by
  have hc (c : ℕ) := (polyBound_const c).quasiPoly
  have hL : QuasiPolyBound (fun n => familyListBound (M n) (B n)) :=
    (hc 1).add (hM.mul (((hc 2).mul hB).add (hc 1)))
  have hF : QuasiPolyBound (fun n => familyFrameBound (K n) (T n) (M n) (B n)) :=
    (((hc 2).mul hK).add ((hc 4).mul (hT.add (hc 2)))).add ((hc 4).mul hL)
  exact ((hc 2).mul ((hc 1).add (hD.mul (((hc 2).mul hF).add (hc 1))))).add
    ((hc 2).mul (hL.add (hc 2)))

end Round
end Algo
