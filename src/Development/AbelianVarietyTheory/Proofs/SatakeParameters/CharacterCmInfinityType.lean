module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MtType
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DeterminantCharacterUnitaryApply
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem

@[expose] public section

noncomputable section

namespace GlobalTheory.KerJ.RatPts

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Host NumberField IsDedekindDomain Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.Mem.Chr (finPartI)

theorem isFin_finPart {L : Type} [Field L] [NumberField L] (a : Ideles L) : IsFinIdele (finPartI L a) := fun _ => rfl

end GlobalTheory.KerJ.RatPts

namespace GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.Host NumberField Classical Formalism.FrobeniusOrbits GlobalTheory.KerJ.RatPts

end GlobalTheory.KerJ
