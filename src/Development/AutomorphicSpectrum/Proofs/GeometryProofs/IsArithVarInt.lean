module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem isArithVar_int : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ)
    (D : ℕ), IsArithVar p D → IsArithVar t D := by
  intro k _ X p t D hp
  obtain ⟨hdom, hfin, hint, hproj, hflat, hdim⟩ := hp
  have hZ : ∀ f g : X ⟶ Sp ℤ, f = g := fun f g => specZIsTerminal.hom_ext f g
  refine ⟨inferInstance, inferInstance, hint, ?_, ?_, hdim⟩
  · rw [hZ t (GlobalTheory.ShFam.Pad.toSpZ X)]
    exact GlobalTheory.ShFam.Pad.isProjOver_toSpZ hproj
  · rw [hZ (t ≫ spMap (Int.castRingHom ℤ)) (p ≫ spMap (Int.castRingHom k))]
    exact hflat

end GlobalTheory.CompanionTheory.Ar.BaseZ
