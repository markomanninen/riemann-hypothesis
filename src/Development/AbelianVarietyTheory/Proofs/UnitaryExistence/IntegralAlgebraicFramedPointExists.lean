module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
public import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
public import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Formalism.LocalToGlobal.ProjectiveLattices.CoreProofs
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AlgebraicPointsModuliEveryPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntFrExtOfGoodLevelStatement

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem integralAlgebraicFramedPoint_exists : PartI → N1ab → N1c → Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → IntFrNe Xo c (Formalism.L2.PjFree.algCls Xo c) :=
  fun hP hab hc hB hT E _ _ _ H Dw l Xo c hpq hg =>
    intFrNe_of (GlobalTheory.T.algebraicPoints_moduli_every_place hc E H Dw l Xo c hpq) (GlobalTheory.T.intFrExt_of_good_level hP hab hB hT E H Dw l Xo c hpq hg)

end GlobalTheory
