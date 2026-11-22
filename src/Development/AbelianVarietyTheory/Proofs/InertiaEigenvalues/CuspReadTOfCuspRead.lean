module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTExistsIff
public import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Nontrivial
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GlobalTheory.CuspRep GlobalTheory.HeightCounting

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RecT

abbrev RecFam : Type 1 :=
  ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w), IrrGL (k := w.adicCompletion E) → WD h

set_option synthInstance.maxHeartbeats 400000

variable {R : Ranks} {H : Formalism.BasicNotions.Host R}

variable {Ω : Type} [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω]

end GlobalTheory.RecT

namespace GlobalTheory.RecT

open GlobalTheory.RowTie

section Read

open Formalism.MainNotions Formalism.MainNotions.N ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC

end Read

end GlobalTheory.RecT

namespace GlobalTheory.RecT

open GlobalTheory.RowTie

end GlobalTheory.RecT

end
