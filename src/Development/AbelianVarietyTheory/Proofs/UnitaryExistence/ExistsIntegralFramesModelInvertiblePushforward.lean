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
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointFieldFromTestRingStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.IntFrames
public import Formalism.LocalToGlobal.ProjectiveLattices.LieFreePf
public import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
theorem _root_.GlobalTheory.intFrames_of_laws : _root_.ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt → _root_.ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H)
      (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l), _root_.Formalism.L2.Pj.IntFramesSt Xo c :=
  fun hBase hTwist E _ _ _ H Dw l Xo c =>
    _root_.Formalism.L2.Pj.intFrames Xo c _root_.ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (_root_.Formalism.L2.Pj.lieFree Xo c) (_root_.Formalism.L2.Pj.thetaFrame_of Xo c hTwist)
      (_root_.GlobalTheory.Frames.framedPoint_field_fromTest hBase E H Dw l Xo c)

end GlobalTheory
