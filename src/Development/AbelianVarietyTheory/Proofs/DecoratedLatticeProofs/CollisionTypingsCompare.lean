module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
public import Formalism.LocalRingCardinality.DataTies
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NcardPrimesOverOfSplitsCompl
public import Formalism.SharpRestriction.CuspSpanNormBounds.UniformConstantsAndStatements
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
public import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra

@[expose] public section

noncomputable section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2

namespace GlobalTheory.CollCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Core.Deg

theorem splits_level (D : D7) (w : D.what₂.Word) : SplitsE D (D.mem w).A.T :=
  S.splitsCompl_of_ncard _ _ (D.mem w).A.T_prime
    (Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion.split_clause _ Formalism.L2.SG.ResidEvFree.cycSplit_holds _ (D.mem w).A.T_prime (S.level_norm_one_mod_conductor _ w)).2

end GlobalTheory.CollCompare
