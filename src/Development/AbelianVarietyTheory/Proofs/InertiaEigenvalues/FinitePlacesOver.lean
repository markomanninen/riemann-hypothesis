module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDiscreteUOfIsDiscrete
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InfinitesimalCharacterInduced
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentsThetaPull
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfIsLocCompGL
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeSplitCm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatake
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BrauerDegreeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetEqOfProdAddEq

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.UG Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.BCWords GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IsobaricOfPublished

theorem multiset_eq_of_prod_map_add {m m' : Multiset ℂ}
    (h : ∀ u : ℂ, (m.map (u + ·)).prod = (m'.map (u + ·)).prod) : m = m' := by
  first
  | exact @_root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq
  | exact _root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq
  | (apply _root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq ..)

end GlobalTheory.IsobaricOfPublished

namespace GlobalTheory.IsobaricOfPublished

end GlobalTheory.IsobaricOfPublished
