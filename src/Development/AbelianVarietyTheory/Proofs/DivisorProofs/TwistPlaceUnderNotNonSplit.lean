module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitTwistPlaces

theorem not_nonSplitAt : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → ∀ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v → ¬ GlobalTheory.WeilParts.NonSplitAt D v e := by
  intro D T Lc sc G μ₀ hμ t v e he PP hPP hv hns
  obtain ⟨f, hf⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt ((hμ.Q_pl t PP hPP).2 PP hPP)
  exact GlobalTheory.AdTh.RecPair.under_ne hf hns hv

end GlobalTheory.SplitTwistPlaces
