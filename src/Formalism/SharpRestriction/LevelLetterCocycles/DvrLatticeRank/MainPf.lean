module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoremOfLeafLemmas
public import Formalism.SharpRestriction.LevelLetterCocycles.NormAHolds
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniformiserRingOfHypotheses
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.QuotPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LiftPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ExtPfMultVEqZero
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.NinLamPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.OneGenPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GamPiPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrobPiNPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ClassMapPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.KapPiPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.InvLiftPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrobeniusSpanDecomposition
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.RankLinkProof
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UnivLinkPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ExponentRecursionHolds
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.WLocal
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3uplinkPfOf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DescentValuation
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.RankBounds
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3mixlinkPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U2ringPfZetaO

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem lifting_theorem_of_uniform_link (hU1L : FirstFrameOfModels) :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
      (CA CB CK C : ℝ), 160 ≤ C → FontExAll D HW F → DdRFull D → DiRank D HW F Cm →
        IntegralityFromMetric D HW F Cm CA CB CK C :=
  local_theorem_of_leaf_lemmas generator_bound_of_hypotheses lift_bound_of_hypotheses DvdPf.dvdCondition quotient_jumps_subset normR_holds
    uniformiser_ring_of_hypotheses ExtPf.ext_pf w_pf kerlam2_pf ninlam_pf gradNCondition frobPiNCondition gamPiCondition
    OneGenPf.onegen_pf univlink_pf invLiftCondition ClassMapPf.classmap_pf frame_pf modelflink_pf
    exponent_recursion_holds modell_pf modelqlink_pf hU1L kappi_pf RankLink.rank_link_holds
    (RankBounds.u2rank_of_ring u2ring_pf) DescentValuation.down_of_models (u3uplink_pf_of w_pf) u3mixlink_pf

end Formalism.MainNotions.N.Ln34

end
