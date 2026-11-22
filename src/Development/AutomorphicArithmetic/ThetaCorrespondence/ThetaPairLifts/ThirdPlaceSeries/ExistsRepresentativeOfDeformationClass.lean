module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupRepresentationTwist
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerDatumAndHalfLevels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActCCoe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreePointHalfLevelLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfLevelSubmodulePermutation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPermutedDirectSumComplexificationStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FreeHalfOfDeformationSpace
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointRead

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.DefRead
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
end GlobalTheory.DefRead
namespace GlobalTheory.DefRead
set_option maxHeartbeats 1000000 in
theorem exists_representative_of_deformation_class_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V) (π : Γ →* G0g (Fm.D x ι).nd) (s : G0g (Fm.D x ι).nd →* Γ) (ρ : Representation ℂ Γ V) (Pb : Subgroup (G0g (Fm.D x ι).nd)) (lam : Pb →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, (Fm.D x ι).nd.PlG k), AddChar (ZMod ((Fm.D x ι).host.g kv.1)) ℂ) (lamb : Pb.comap π →* ℂˣ) (H : Fin 2 → Subgroup (G0g (Fm.D x ι).nd)), IsSplit π s ∧ IsWhit (Fm.D x ι) Pb lam ψ ∧ (∀ γ : Pb.comap π, lamb γ = lam ⟨π γ, γ.2⟩) ∧ (∀ k, IsHalf (Fm.D x ι) k (H k)) ∧ (∀ k, ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction ((H k).comap π) X) (A : X → Submodule ℂ V), (∀ (h : (H k).comap π) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧ ∀ (h : (H k).comap π) (y : X), ∀ v ∈ A y, ρ (h : Γ) v ∈ A (h • y)) ∧ Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb) ∧ Formalism.HN.rkK (latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ (G0g (Fm.D x ι).nd) V) (Fm.D x ι).ntypes.e0) : Submodule ℂ V) := by
  intro hP hG
  have h1 := _root_.GlobalTheory.T.halfH_free_action_and_isInternal_repAt_mem hP hG
  have h2 := hG
  unfold _root_.GlobalTheory.CovTop.GramCondition at h2
  unfold _root_.GlobalTheory.CovTop.LiftsCondition at h1 h2 ⊢
  refine (h1.and h2).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, -, e1⟩, ⟨C2, -, e2⟩⟩ := h
  obtain ⟨x0, e⟩ := e1.and e2
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi => ?_⟩
  obtain ⟨a1, a2⟩ := e x hx hle ι p hp
  exact _root_.GlobalTheory.DefRead.point_read_alt p i hp (a2 i) (a1 i hi)
end GlobalTheory.DefRead
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deformation_class_has_representative_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V) (π : Γ →* G0g (Fm.D x ι).nd) (s : G0g (Fm.D x ι).nd →* Γ) (ρ : Representation ℂ Γ V) (Pb : Subgroup (G0g (Fm.D x ι).nd)) (lam : Pb →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, (Fm.D x ι).nd.PlG k), AddChar (ZMod ((Fm.D x ι).host.g kv.1)) ℂ) (lamb : Pb.comap π →* ℂˣ) (H : Fin 2 → Subgroup (G0g (Fm.D x ι).nd)), IsSplit π s ∧ IsWhit (Fm.D x ι) Pb lam ψ ∧ (∀ γ : Pb.comap π, lamb γ = lam ⟨π γ, γ.2⟩) ∧ (∀ k, IsHalf (Fm.D x ι) k (H k)) ∧ (∀ k, ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction ((H k).comap π) X) (A : X → Submodule ℂ V), (∀ (h : (H k).comap π) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧ ∀ (h : (H k).comap π) (y : X), ∀ v ∈ A y, ρ (h : Γ) v ∈ A (h • y)) ∧ Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb) ∧ Formalism.HN.rkK (latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ (G0g (Fm.D x ι).nd) V) (Fm.D x ι).ntypes.e0) : Submodule ℂ V) := by
  first | exact @_root_.GlobalTheory.DefRead.exists_representative_of_deformation_class_alt | exact _root_.GlobalTheory.DefRead.exists_representative_of_deformation_class_alt | (intros; apply _root_.GlobalTheory.DefRead.exists_representative_of_deformation_class_alt <;> assumption)
end
end
