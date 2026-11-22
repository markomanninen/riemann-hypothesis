module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum

@[expose] public section

namespace GlobalTheory.AdicNatCastNorm

theorem norm_natCast_adicCompletion_le_one {F : Type} [inst : Field F] [inst_1 : NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (n : ℕ) :
    ‖(↑n : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)‖ ≤ (1 : ℝ) :=
  IsUltrametricDist.norm_natCast_le_one _ n

end GlobalTheory.AdicNatCastNorm
