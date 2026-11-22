module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIsoOfGenericIsoNormalLocalBaseStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdjointEndomorphismsCubeLBOfDenseFibres
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section

open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.UnifLamFibre

open GlobalTheory.CechPic

theorem isSquare_unique {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {φ : G'.left ⟶ G.left}
    {a b : (G' ⊗ G').left ⟶ (G ⊗ G).left} (ha : IsSquare φ a) (hb : IsSquare φ b) : a = b :=
  (IsPullback.of_hasPullback G.hom G.hom).hom_ext (ha.1.trans hb.1.symm) (ha.2.trans hb.2.symm)


end GlobalTheory.UnifLamFibre
