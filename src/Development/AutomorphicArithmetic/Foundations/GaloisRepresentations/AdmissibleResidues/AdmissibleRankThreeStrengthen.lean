module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsAutomorphicOverImagQuad
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Wold
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.SafeUGap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.UnderCPl

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

namespace UpperTheory.GalN.V

section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

structure AdmKN [IsCMField F] (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  irr : IsIrr r
  aut : IsAutCsdN ι r
  level : Level l M m r
  odd : Keep.OddU l r

end

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

variable {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsScalarTower ℚ K Ω]


omit [IsAlgClosure ℚ Ω] [Algebra ℚ Ω] [IsScalarTower ℚ K Ω] in
structure Adm3N [IsCMField K] (ι : Qbar l ≃+* ℂ) (e N : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) : Prop where
  irr : IsIrr ρ
  aut : IsAutCsdN ι (tw ρ (cycBar K Ω l)⁻¹)
  level : Level l N ![(e : ℤ), 0, -(e : ℤ)] ρ
  unl : Keep.OddU l ρ


omit [IsAlgClosure ℚ Ω] in
def Adm2N (ι : Qbar l ≃+* ℂ) (e M : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) : Prop :=
  ∃ W : G ℚ Ω →* GL (Fin 2) (Qbar l), IsIrr W ∧
    ((∃ f : Newform (2 * e + 1), f.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ WitQ ι W) ∧
    Level l M ![(e : ℤ), -(e : ℤ)] W ∧ IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) ∧
    ∃ g : GL (Fin 3) (Qbar l), ∀ s : G K Ω, ((g * ρ s * g⁻¹ : GL (Fin 3) (Qbar l)) : Matrix (Fin 3) (Fin 3) (Qbar l)) =
      !![W (s.restrictScalars ℚ) 0 0, 0, W (s.restrictScalars ℚ) 0 1; 0, 1, 0;
         W (s.restrictScalars ℚ) 1 0, 0, W (s.restrictScalars ℚ) 1 1]

end

end UpperTheory.GalN.V
