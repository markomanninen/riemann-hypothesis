module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultisetSeparation

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.msetSep :
    ∀ m m' : Multiset ℂ, (∀ u : ℂ, (m.map (u + ·)).prod = (m'.map (u + ·)).prod) → m = m' :=
  _root_.UpperTheory.Reformulated.B.MultisetSeparation.msetSep
