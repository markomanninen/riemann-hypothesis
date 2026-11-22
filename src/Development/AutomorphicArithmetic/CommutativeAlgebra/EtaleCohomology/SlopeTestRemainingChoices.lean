module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeHomSectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSecStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeZeroSectionClassPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupEqClassOfIsAWStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionPairingSpecAndCupUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistUnitClassRootClassSpecStatement

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Et

structure SlopeTestRemainingChoices : Prop where
  sheaf : type_of% @GlobalTheory.T.etaleSheafSections_ext_and_glue
  resol : type_of% @GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness
  freeS : type_of% @GlobalTheory.T.free_sections_ext_res_map
  evs : type_of% @GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties
  rep : type_of% @GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff
  sec : type_of% @GlobalTheory.T.degreeZeroSectionClass_properties
  aw : type_of% @GlobalTheory.T.cup_eq_class_of_isAW
  twist : type_of% @GlobalTheory.T.tateTwist_sections_locally_generated
  pair : type_of% @GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique
  unit : type_of% @GlobalTheory.T.tateTwistUnitClass_rootClass_spec

section Site
variable {C : Type 1} [Category.{0} C] {S : Type 1} [CommRing S]

abbrev PM (C : Type 1) [Category.{0} C] (S : Type 1) [CommRing S] : Type 2 := Cᵒᵖ ⥤ ModuleCat.{1} S

structure Dat (C : Type 1) [Category.{0} C] (S : Type 1) [CommRing S] (ι : Type) where
  P : ι → ℤ → PM C S
  dP : ∀ b s t, P b s ⟶ P b t
  Q : ℤ → PM C S
  dQ : ∀ s t, Q s ⟶ Q t
  e : ι → ℤ
  φ : ∀ b s, P b (s - e b) ⟶ Q s
  ddP : ∀ b s t u, dP b s t ≫ dP b t u = 0
  ddQ : ∀ s t u, dQ s t ≫ dQ t u = 0
  comm : ∀ b s t, s + 1 = t → φ b s ≫ dQ s t = dP b (s - e b) (t - e b) ≫ φ b t

variable {ι : Type} [Fintype ι] (D : Dat C S ι)

end Site

section Rep
variable {R : Type} [CommRing R]

def Rep {I : Cx R} {U : Scheme.{0}} {n : ℤ} (z : Sec (I.X n) U) (c : CohomologyClass ((chains R).obj (sch.obj U)) I n) : Prop :=
  ∃ α : Cocycle ((chains R).obj (sch.obj U)) I n, CohomologyClass.mk α = c ∧ ev α.1 0 n (by simp) U (𝟙 U) = z

variable {S Y : Scheme.{0}} (p' : Y ⟶ S)

end Rep

section Classes
variable (q : ℕ) {S Y : Scheme.{0}} (p' : Y ⟶ S) {ι : Type} [Fintype ι] {e : ι → ℤ} {j : ℤ} (w : ∀ b, Ht q (sch.obj Y) (e b) j)

end Classes

end UpperTheory.Et

end
