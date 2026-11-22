module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamPtClauses
public import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamObj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedSectionCorrespondenceExistsUniqueNonva
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRankOneCuspLatticeDataOfPrincipal
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmLieStatementsIffLibrary
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.abelian₂ Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.FD (Data DataX Frame LamBasis fdeg)
open GlobalTheory.SecTransport GlobalTheory.SecTieEx

namespace GlobalTheory.FramedCMPointCompare

section Bundles

variable {X X' Y : Scheme.{0}}

end Bundles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} {c : Coeff l}

section Letters

variable [StarRing (𝓞 E)] {nΨ n' : ℕ}

variable {o : LamObj c nΨ n'}

end Letters

section Data

variable {Dw : Datum H} {Xo : Moduli Dw l}

end Data

variable {D : D7}

theorem fdeg_host (D : D7) : fdeg D.host.E = D.R.f := by
  unfold fdeg
  rw [hostSize_finrank]
  omega

end GlobalTheory.FramedCMPointCompare
