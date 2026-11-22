module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeSpacesOrthogonalOfClassSumInner
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjSPV
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceEqConjugatePlaceAndEmbeddingStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceUnitaryLocEqTransposeInvStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceUnitsCharacterEqOfAgreeOnFieldStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoPreservesValuationStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagUniformiserConjTransposeInvMemUpperParahoricStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockCharacterEqInvAtTransposeInvLowerBlockDetStatement

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypeBlockConj

theorem trivOutside_mul {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x y : GA L n}
    (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro w hw
  have : ((x * y).1 : Matrix (Fin n) (Fin n) (AL L)) =
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl
  rw [this, Matrix.map_mul, hx w hw, hy w hw, mul_one]

theorem trivOutside_inv {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x : GA L n}
    (hx : TrivOutside T x) : TrivOutside T x⁻¹ := by
  intro w hw
  have h1 : (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have h2 := congrArg (fun M => M.map (compAt L w)) h1
  simp only [Matrix.map_mul, hx w hw, mul_one] at h2
  rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]

theorem rt_rt {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (a b : GAf L n) (f : GAf L n → W) (g : GAf L n) : NG.rt L n a (NG.rt L n b f) g = f (g * a * b) := rfl

end GlobalTheory.TypeBlockConj

namespace GlobalTheory.TypeBlockConj


end GlobalTheory.TypeBlockConj
