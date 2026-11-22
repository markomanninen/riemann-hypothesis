module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapDcrisEqDdRCrystallineUnramified

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Per.DdREqDcris

theorem record_caseA : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K LL : FinExt l), CaseA K LL →
    Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris ((D.loc l).PD K) ↥LL.1 := by
  intro D l _ K LL _ hb V _ _ _ _ _ ρ _ _ _ hc
  exact map_Dcris_eq_DdR l (D.loc l) (D.locA l) (D.locT l) K LL hb V ρ hc

end GlobalTheory.Per.DdREqDcris
