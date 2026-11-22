module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import CompanionTheory.EightfoldTheory.VariationTheory.PublishedTheorems.ImportsAlt
public import CompanionTheory.EightfoldTheory.VariationTheory.SelfDualForms.SelfDualWeylChambers.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FoundBridge
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolCap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExistsIdele
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolLin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExpInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExpUnique
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.KLocal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.DirChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CharVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.ArchBd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftSm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftLie
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftCent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.OrthCases
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftCT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCrit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftExp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.HkCoef
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.InfGLScalar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatComp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatHol
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatOfVec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import GroundTheory.AutomorphicForms.AffineBruhat

@[expose] public section

open ValuativeRel Matrix

namespace GlobalTheory.IwEq

theorem iwahori_eq_glnLocal_iwahori : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a : ℕ),
    GlobalTheory.SmGL.iwahori k (Fin a) = GroundTheory.Automorphic.GLnLocal.iwahori k a := by
  intro k _ _ _ _ a
  ext g
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, GlobalTheory.SmGL.mem_borel] at hu
    refine ⟨u, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, GroundTheory.Automorphic.mem_borel_iff]
      intro i j hij
      rw [GroundTheory.Automorphic.GLnLocal.residueReduction_apply]
      exact hu i j hij
    · ext i j
      rfl
  · rintro ⟨u, hu, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, GroundTheory.Automorphic.mem_borel_iff] at hu
    refine ⟨u, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, GlobalTheory.SmGL.mem_borel]
      intro i j hij
      have h := hu i j hij
      rw [GroundTheory.Automorphic.GLnLocal.residueReduction_apply] at h
      exact h
    · ext i j
      rfl

end GlobalTheory.IwEq
