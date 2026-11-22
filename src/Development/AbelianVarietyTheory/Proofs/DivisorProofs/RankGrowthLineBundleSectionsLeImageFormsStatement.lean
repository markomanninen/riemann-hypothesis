module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLineBundleSectionsLeImageForms
public import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal

@[expose] public section

open NumberField MvPolynomial GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.CompHt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankGrowth_lineBundle_sections_le_image_forms : ∀ (k : Type) [Field k] [CharZero k] (S : LinSys k), S.IsVariety → S.BasePointFree → S.Birational → growth S.D (fun m => (lbH0 k (lbPow S.L m) : ℕ∞)) ≤ growth S.D (fun m => (Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) : ℕ∞)) := by
  first | exact @GlobalTheory.SecGrowth.rankGrowth_lineBundleSections_le_image_forms | exact GlobalTheory.SecGrowth.rankGrowth_lineBundleSections_le_image_forms | (intros; apply GlobalTheory.SecGrowth.rankGrowth_lineBundleSections_le_image_forms <;> assumption)
