import Workspace.Algo.SplitUpccRun
import Workspace.Algo.DesignReadFamilyValidity
import Workspace.Algo.AggNodeRestoreRaw

/-! Theorem 9.2.3 uses the Design Lemma's actual returning family. A
partition is already an answer. A dominant UPCC is solved at threshold
alpha times the original degree divided by the dominant degree, and its
answers are restored through the retained original-name dictionary. -/
namespace Algo
open Babai RAM

abbrev RawExtendedBranch := AmbientGIn × RawDesignReadOut

def extendedUpccInput (z : RawExtendedBranch × RawConfig) : RawUpcc :=
  (z.2,(z.1.1.2.1*z.1.1.1.1.2.2.length,z.1.1.2.2*z.1.2.2.1.length))

def extendedUpccAnswers (c t d : ℕ) (z : RawConfig × RawExtendedBranch) :
    List RawAlignOutcome :=
  (upccSplitFamily c t d (extendedUpccInput (z.2,z.1))).map
    (fun o => aggnRestoreOutcome ((z.2.1.1.1.2.2,z.2.2.2.1),o))

def extendedSplitBranch (c t d : ℕ) (z : RawExtendedBranch) : List RawAlignOutcome :=
  z.2.1.elim
    (z.2.2.2.elim [] (fun q => extendedUpccAnswers c t d (q,z)))
    (fun P => [rawAlignPartition P])

def extendedSplitFamily (a c t d : ℕ) (g : AmbientGIn) : List RawAlignOutcome :=
  (ambientDesignReadFamily a g).flatMap (fun o => extendedSplitBranch c t d (g,o.2))

theorem polyFun_extendedUpccInput : PolyFun extendedUpccInput := by
  have hg : PolyFun (fun z : RawExtendedBranch × RawConfig => z.1.1) :=
    polyFun_fst.comp polyFun_fst
  have ho : PolyFun (fun z : RawExtendedBranch × RawConfig => z.1.2) :=
    polyFun_fst.comp polyFun_snd
  have hn := ((((hg.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp polyFun_length
  have hl := ((ho.comp polyFun_snd).comp polyFun_fst).comp polyFun_length
  exact polyFun_snd.pair ((((hg.comp polyFun_snd).comp polyFun_fst).mul hn).pair
    (((hg.comp polyFun_snd).comp polyFun_snd).mul hl))

theorem quasiFun_extendedUpccAnswers (c t d : ℕ) : QuasiFun (extendedUpccAnswers c t d) := by
  have ha := (polyFun_swap.comp polyFun_extendedUpccInput).comp_quasiFun
    (quasiFun_upccSplitFamily c t d)
  have hd : PolyFun (fun z : RawConfig × RawExtendedBranch => (z.2.1.1.1.2.2,z.2.2.2.1)) := by
    have hg : PolyFun (fun z : RawConfig × RawExtendedBranch => z.2.1) :=
      polyFun_snd.comp polyFun_fst
    have ho : PolyFun (fun z : RawConfig × RawExtendedBranch => z.2.2) :=
      polyFun_snd.comp polyFun_snd
    exact ((((hg.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).pair
      ((ho.comp polyFun_snd).comp polyFun_fst)
  exact (hd.quasiFun.pair ha).comp_poly aggnPolyFun_restoreFamily

theorem quasiFun_extendedSplitBranch (c t d : ℕ) : QuasiFun (extendedSplitBranch c t d) := by
  have hnone : QuasiFun (fun z : RawExtendedBranch =>
      z.2.2.2.elim [] (fun q => extendedUpccAnswers c t d (q,z))) :=
    ((((polyFun_snd.comp polyFun_snd).comp polyFun_snd).pair polyFun_id).comp_quasiFun
      (QuasiFun.optionElim (polyFun_const []).quasiFun (quasiFun_extendedUpccAnswers c t d)))
  have hsome : PolyFun (fun z : RawColPart × RawExtendedBranch => [rawAlignPartition z.1]) :=
    (polyFun_fst.comp polyFun_rawAlignPartition).comp polyFun_singleton
  exact (((polyFun_snd.comp polyFun_fst).pair polyFun_id).comp_quasiFun
    (QuasiFun.optionElim hnone hsome.quasiFun))

theorem quasiFun_extendedSplitFamily (a c t d : ℕ) : QuasiFun (extendedSplitFamily a c t d) := by
  have hf : QuasiFun (fun z : AmbientGIn × (List ℕ × RawDesignReadOut) =>
      extendedSplitBranch c t d (z.1,z.2.2)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_snd)).comp_quasiFun
      (quasiFun_extendedSplitBranch c t d)
  exact ((polyFun_id.quasiFun.pair (quasiFun_ambientDesignReadFamily a)).comp
    (aggnQuasiFun_mapParam hf)).comp_poly polyFun_flatten

end Algo
