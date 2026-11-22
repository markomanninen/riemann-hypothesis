module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportInnerLattices
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData

@[expose] public section

noncomputable section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.NonGenericCompare

section Place
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [StarRing E]
variable (o : Type) [CommRing o] [Algebra o F] [Algebra o E]

variable {o}

end Place

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] [StarRing E]
variable {o : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [Algebra o F]
  [IsFractionRing o F] [Algebra o E] [IsScalarTower o F E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

namespace Match
variable {P : LocNG.FPair H r} {S : Frames M.L r k}
variable (c : Coord P S)

end Match

end GlobalTheory.NonGenericCompare
