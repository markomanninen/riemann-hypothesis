module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToroidalFlagSmoothProjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidal_flag_smooth_projective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (T : GlobalTheory.CompHS.TorFlag Xo c), ∃ d : ℕ, SmoothOfRelativeDimension d (GlobalTheory.CompHS.flagStr T.X) ∧ IsProjOver (GlobalTheory.CompHS.flagStr T.X) := by
  intro E _ _ _ H D l Xo c T
  obtain ⟨p⟩ := GlobalTheory.FlagMod.LowRank.nonempty_proj_id (E := E) (c := c)
  obtain ⟨A⟩ := GlobalTheory.CompanionTheory.FlagSmooth.nonempty_atlas_of_cover T.Y p
    (GlobalTheory.CompanionTheory.FlagSmooth.exists_gChart_of_flagCover T.X)
  obtain ⟨M, g, κ, hκ, hZ⟩ := GlobalTheory.CompanionTheory.FlagSmooth.exists_cellModel T.Y p A
  obtain ⟨d, hsm, hpr⟩ := GlobalTheory.T.flag_atlas_projective_embedding E H D l Xo c T.Y p A M.YY M.π g κ hκ hZ T.smooth
  obtain ⟨h, hh, hπ⟩ := GlobalTheory.T.exists_flagModel_isIso_of_open_cells E H D l Xo c T.Y p A M g κ hκ hZ T.smooth T.flag
  have e : flagStr T.X = h ≫ M.π ≫ T.Y.s := by
    rw [← Category.assoc, hπ]
  refine ⟨d, ?_, ?_⟩
  · rw [e]; exact GlobalTheory.VarFlag.smooth_iso h _ hsm
  · rw [e]
    obtain ⟨N, i, hi, hs⟩ := hpr
    exact ⟨N, h ≫ i, inferInstance, by rw [Category.assoc, hs]⟩
