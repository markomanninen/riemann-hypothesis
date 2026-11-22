module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogCanonicalCutAngehrnSiuInductionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsolatedLcCentreOfZeroLcThresholdStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

namespace GlobalTheory

theorem isolatedNonKltDivisor_of_principalisation :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.IsolatedNonKltDivisor := by
  intro hP X _ _ _ p n hproj hdim hn Δ r N₀ x c hΔ hklt hr hnef hbig hx hc hvol hsum
  letI := algebraΓOfHom p
  have hLB : N₀.IsLB := hnef.isLB
  obtain ⟨A, hA, hj⟩ := GlobalTheory.T.exists_logCanonical_cut_angehrnSiu_induction hP X p n hproj hdim hn Δ r N₀ x c hΔ hklt hr hLB hnef hbig hx hc hvol
  obtain ⟨j', lam, μ, m', D₀, hj', hm', hD₀, hμ, hlam, hnum, hcut⟩ := hj 0 (by omega)
  obtain rfl : j' = 0 := Nat.le_zero.mp hj'
  exact GlobalTheory.T.exists_isolated_lcCentre_of_zero_lcThreshold hP X p n hproj hdim hn Δ r N₀ x c hΔ hklt hr hLB hnef hbig hx hc hvol hsum
    A lam μ m' D₀ hA hm' hD₀ hμ (by simpa using hlam) hnum hcut

end GlobalTheory
