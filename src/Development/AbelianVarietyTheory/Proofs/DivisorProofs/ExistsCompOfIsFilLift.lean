module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeCommRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerValueEndomorphismLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveGeomFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingMorphismUniqueness
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomIdPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeLiftAlongNilpotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.AbDual GlobalTheory.AbLaw
  GlobalTheory.CechPic GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSBijection

open TrivSqZeroExt

section Crystal

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {g : ℕ}

theorem fst_surj : Function.Surjective (fstHom R R R).toRingHom := fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩

variable {d d' : Crys (epsDP R) (DeRham.epsRed R) A} {f f' k k' : HdR A}

variable [IsCommMonObj A] {O : Type} [CommRing O] {a : OAct O A} (hL : LieExact A)

variable (κ : Fil A →ₗ[R] Serre.Lie a)

end Crystal

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {𝔠 : FracId F} {R : Type} [CommRing R]
  {X : Obj F 𝔠 (Sp R)}

end GlobalTheory.KSBijection
