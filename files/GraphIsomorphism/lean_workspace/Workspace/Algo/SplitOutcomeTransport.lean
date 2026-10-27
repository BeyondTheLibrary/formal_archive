import Workspace.Algo.SplitFullLift
import Workspace.Algo.SplitBipTurnOutcomeIso

/-! The isomorphism of an answer must use the original point map. This
relation records that map, including on a proper Johnson carrier. Extending
a partition by its complement preserves the same map. -/
namespace Algo
open Babai RAM
open scoped Classical

def SplitOutcomeIso {Γ : Type} (π : Equiv.Perm Γ)
    (Z Z' : Pt (SplitOutcomes Γ)) : Prop :=
  ∃ e : ↥Z.car ≃ ↥Z'.car, (∀ x, (e x).val = π x.val) ∧
    e ∈ (SplitOutcomes Γ).IsoP Z Z'

namespace SplitOutcomeIso
variable {Γ : Type} {π : Equiv.Perm Γ} {Z Z' : Pt (SplitOutcomes Γ)}

theorem car (h : SplitOutcomeIso π Z Z') : Z'.car = π '' Z.car := by
  obtain ⟨e,he,_⟩ := h
  ext y
  constructor
  · intro hy
    refine ⟨(e.symm ⟨y,hy⟩).val,(e.symm ⟨y,hy⟩).property,?_⟩
    rw [← he,Equiv.apply_symm_apply]
  · rintro ⟨x,hx,rfl⟩
    rw [← he ⟨x,hx⟩]
    exact (e ⟨x,hx⟩).property

theorem permHom_mem (h : SplitOutcomeIso π Z Z') :
    permHom π Z Z' h.car ∈ (SplitOutcomes Γ).IsoP Z Z' := by
  obtain ⟨e,he,hi⟩ := h
  have hh : e = permHom π Z Z' (car ⟨e,he,hi⟩) :=
    Equiv.ext fun x => Subtype.ext (he x)
  rwa [← hh]

theorem eq_smul [MulAction (Equiv.Perm Γ) (Pt (SplitOutcomes Γ))]
    (hK : IsCatAction (SplitOutcomes Γ)) (h : SplitOutcomeIso π Z Z') :
    Z' = π • Z := hK.eq_smul h.car h.permHom_mem

theorem of_eq_smul [MulAction (Equiv.Perm Γ) (Pt (SplitOutcomes Γ))]
    (hK : IsCatAction (SplitOutcomes Γ)) (h : Z' = π • Z) :
    SplitOutcomeIso π Z Z' := by
  subst Z'
  exact ⟨permHom π Z (π • Z) (hK.car_smul π Z),fun _ => rfl,hK.iso_smul π Z⟩

theorem extend (h : SplitOutcomeIso π Z Z') :
    SplitOutcomeIso π (extendOutcome Z) (extendOutcome Z') := by
  obtain ⟨inst,hK⟩ := exists_isCatAction_splitOutcomes (Γ := Γ)
  letI := inst
  apply of_eq_smul hK
  rw [h.eq_smul hK,extendOutcome_smul hK]

end SplitOutcomeIso

def RawSplitOutcomeIso (m : ℕ) (π : Equiv.Perm (Fin m))
    (o o' : RawAlignOutcome) : Prop :=
  ∃ Z Z',decAlignOutcome m o = some Z ∧ decAlignOutcome m o' = some Z' ∧
    SplitOutcomeIso π Z Z'

theorem decAlignOutcome_cases {m : ℕ} {o : RawAlignOutcome}
    {Z : Pt (SplitOutcomes (Fin m))} (h : decAlignOutcome m o = some Z) :
    (∃ P,o = rawAlignPartition P ∧ Z = decAlignPartition m P) ∨
      ∃ J,∃ hJ : J.WF m (rawJDeg J) J.2.1,
        o = rawAlignJohnson J ∧ Z = decAlignJohnson J hJ := by
  rcases o with ⟨p,j⟩
  cases p with
  | some p =>
    cases j with
    | some j => cases h
    | none => exact Or.inl ⟨p,rfl,(Option.some.inj h).symm⟩
  | none =>
    cases j with
    | none => cases h
    | some j =>
      change (if hj : j.WF m (rawJDeg j) j.2.1 then
        some (decAlignJohnson j hj) else none) = some Z at h
      split at h
      next hj => exact Or.inr ⟨j,hj,rfl,(Option.some.inj h).symm⟩
      next hj => cases h

theorem splitOutcomeIso_partition_iff {m : ℕ} (π : Equiv.Perm (Fin m))
    (P Q : RawColPart) :
    SplitOutcomeIso π (decAlignPartition m P) (decAlignPartition m Q) ↔
      ColPartIso m P Q π := by
  constructor
  · rintro ⟨e,he,hc,hp⟩
    refine ⟨fun i => ?_,fun i j => ?_⟩
    · have h := hc ⟨i,Set.mem_univ i⟩
      change labAt Q.1 (e ⟨i,Set.mem_univ i⟩).val.val = labAt P.1 i.val at h
      rwa [he] at h
    · have h := hp ⟨i,Set.mem_univ i⟩ ⟨j,Set.mem_univ j⟩
      change (cellOf P i.val = cellOf P j.val) ↔
        cellOf Q (e ⟨i,Set.mem_univ i⟩).val.val =
          cellOf Q (e ⟨j,Set.mem_univ j⟩).val.val at h
      rwa [he,he] at h
  · intro h
    let e := (Equiv.Set.univ (Fin m)).trans (π.trans (Equiv.Set.univ (Fin m)).symm)
    exact ⟨e,fun _ => rfl,fun i => h.1 i.val,fun i j => h.2 i.val j.val⟩

theorem splitFullLift_iso {m : ℕ} {π : Equiv.Perm (Fin m)}
    (dom dom' L L' : List ℕ) (hd : dom.length = m) (hd' : dom'.length = m)
    (hn : L.Nodup) (hb : ∀ a ∈ L,a < m)
    (hn' : L'.Nodup) (hb' : ∀ a ∈ L',a < m)
    {o o' : RawAlignOutcome} {Z Z' : Pt (SplitOutcomes (Fin m))}
    (h : sbipDecodeNamed m L o = some Z) (h' : sbipDecodeNamed m L' o' = some Z')
    (hi : SplitOutcomeIso π Z Z') :
    RawSplitOutcomeIso m π (splitFullLift ((dom,L),o)) (splitFullLift ((dom',L'),o')) :=
  ⟨_,_,splitFullLift_decode dom L hd hn hb h,
    splitFullLift_decode dom' L' hd' hn' hb' h',hi.extend⟩

theorem SbipNamedOutcomeIso.along {m : ℕ} {I J : RawSbipNode}
    {X Y : Pt (BipBlockInputs (Fin m))} {φ : ↥X.car ≃ ↥Y.car}
    {π : Equiv.Perm (Fin m)} (hφ : ∀ x,(φ x).val = π x.val)
    {o o' : RawAlignOutcome} (h : SbipNamedOutcomeIso I J X Y φ o o') :
    ∃ Z Z',sbipDecodeNamed m I.1.2.1.1.1.1 o = some Z ∧
      sbipDecodeNamed m J.1.2.1.1.1.1 o' = some Z' ∧ SplitOutcomeIso π Z Z' := by
  obtain ⟨Z,Z',hd,hd',hZ,hZ',e,he,hi⟩ := h
  exact ⟨Z,Z',hd,hd',e,fun x => (he x).trans (hφ ⟨x.val,hZ x.property⟩),hi⟩

end Algo
