module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContDiffSheetIffStatement

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem wZ_isCInf : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (L : HermLB p) (τ : ℤ →+* ℂ), (wZ L t τ).IsCInf := by
  intro k _ _ X p t L τ i y hy
  have hy' : unsheet p y ∈ ptsIn p (emb p y) (L.B.U i) := mem_ptsIn.2 (mem_ptsIn.1 hy)
  refine (GlobalTheory.T.contDiff_sheet_iff k X p t τ (emb p y) ((wZ L t τ).φ i) (unsheet p y)).2 ?_
  refine (L.cInf (emb p y) i _ hy').congr ?_
  filter_upwards [(isOpen_ptsIn _).mem_nhds hy'] with z hz
  exact wOver_wZ L t τ _ i z hz

end GlobalTheory.CompanionTheory.Ar.BaseZ
