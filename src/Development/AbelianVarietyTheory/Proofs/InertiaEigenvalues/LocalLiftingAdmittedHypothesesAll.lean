module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ArchimedeanSignatureMatchingOfLiftingTheory
public import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneSurjectiveWittTiltStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionCorestrictionH1fStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllOfTateDualityEulerCharStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StrictAdm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineRestrictFiniteExtensionJumpsStatement

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.AdmAllRecords

theorem localLifting_admittedHypotheses_all_alt : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      ElementDenominator.Adm2 D HW F := by
  intro hBK hTD hEC D HW F _
  exact ⟨GlobalTheory.T.restriction_corestriction_H1f D HW F, GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar hBK hTD hEC D, GlobalTheory.Per.FontaineAdm.fontaine_bounds D,
    GlobalTheory.Per.StrictAdm.strict_adm D, GlobalTheory.T.crystalline_restrict_finite_extension_jumps D, GlobalTheory.T.frobenius_sub_one_surjective_witt_tilt⟩

end GlobalTheory.AdmAllRecords
