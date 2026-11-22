module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeParametersUnique
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspRep_satakeParameters_unique : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (a : ℕ) (π : CG K a) (w : HeightOneSpectrum (𝓞 K)) (B B' : Multiset ℂˣ), π.HasSat w B → π.HasSat w B' → B = B' := by
  first | exact @GlobalTheory.AboveL.cg_hasSat_unique | exact GlobalTheory.AboveL.cg_hasSat_unique | (intros; apply GlobalTheory.AboveL.cg_hasSat_unique <;> assumption)
