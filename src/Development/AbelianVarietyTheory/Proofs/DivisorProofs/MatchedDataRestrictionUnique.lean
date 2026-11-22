module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanInvolutionSystemsConjArchimedeanUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianCartanInvolutionSystemsConjugateArcStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapsRelevantSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductMemSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzWeylFourier
public import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvFinMkPt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenProportionalLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeInvariantVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFunctionFactorizableSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralArchimedeanInvariant

@[expose] public section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKRealConj

theorem soLoc_reG' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (G : Geo σ a a') (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (ψ : AddChar (AF F) ℂ) {v : Pl (F := F)}
    (t : E →ₐ[F] Fv F v) : (reG G V V' W).M'.SoLoc ψ t = G.M'.SoLoc ψ t := by
  ext φ
  simp only [Model.SoLoc, Model.IsLinBar, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, ι, ⟨a, b, c⟩, h2⟩; exact ⟨h1, ι, ⟨a, b, c⟩, h2⟩
  · rintro ⟨h1, ι, ⟨a, b, c⟩, h2⟩; exact ⟨h1, ι, ⟨a, b, c⟩, h2⟩

theorem so_reG' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (G : Geo σ a a') (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (ψ : AddChar (AF F) ℂ) {v : Pl (F := F)}
    (t : E →ₐ[F] Fv F v) : (reG G V V' W).M'.So ψ t = G.M'.So ψ t := by
  unfold Model.So
  rw [soLoc_reG']
  rfl

end GlobalTheory.ThKRealConj
