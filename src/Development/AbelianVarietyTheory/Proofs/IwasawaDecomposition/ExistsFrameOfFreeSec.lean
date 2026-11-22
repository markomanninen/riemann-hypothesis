module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointExtendsPowerSeries
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionFramesMoveToCoverAndRingExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfFrames
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericSectionExtendsNormal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecMapFromSpecOfRangeSubset
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemiAbelianModelDeterminedByGenericFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PulledSectionsFormBasisIdOfPulledSectionsFormBas
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsoUniqueOfRig
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam
open scoped CategoryTheory.Obj Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

open GlobalTheory.FramePull GlobalTheory.ConstFam

section Move

variable {S Z : Scheme.{0}} {G₀ : Over S} {G : Over Z} {L₀ : LB G₀.left} {L : LB G.left} {F : G.left ⟶ G₀.left}
  {π : Z ⟶ S} {N : ℕ} {w : LB.Iso L (L₀.pull F)}

end Move

theorem exists_pt {S : Scheme.{0}} {G : Over S} (T : Over S) {Y : Scheme.{0}} (a : Y ⟶ T.left) (b : Y ⟶ G.left)
    (h : a ≫ T.hom = b ≫ G.hom) : ∃ ρ : Y ⟶ (T ⊗ G).left, ρ ≫ (fst T G).left = a ∧ ρ ≫ (snd T G).left = b :=
  ⟨pullback.lift a b h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

end Frames

end GlobalTheory.TorRef
