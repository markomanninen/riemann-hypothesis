module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdeleMapInfDiagMaxRealSubfieldCm
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GaloisRepOfPolarizedPair
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfWeightOfIntegerExpo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyIdeleMapInfIdeleNegOne

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleMap_infDiag_maxRealSubfield_cm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (x : (maximalRealSubfield E)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infDiag x) = infDiag (Units.map (algebraMap (maximalRealSubfield E) E).toMonoidHom x) := by
  first | exact @GlobalTheory.InfDiagExt.ideleMap_infDiag | exact GlobalTheory.InfDiagExt.ideleMap_infDiag | (intros; apply GlobalTheory.InfDiagExt.ideleMap_infDiag <;> assumption)
