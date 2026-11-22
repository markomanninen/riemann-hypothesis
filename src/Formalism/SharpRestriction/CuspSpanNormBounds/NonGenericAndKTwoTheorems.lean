module

public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Formalism.HermitianLattices.StatementMass

@[expose] public section

noncomputable section

open ValuativeRel NumberField MeasureTheory
open scoped ENNReal

namespace Formalism.MainNotions.NonGenericAndKTwoTheorems

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NonGenericLocalBound (k r : ℕ) (C : ℝ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V),
      Module.finrank E V = k + 2 * r + 1 →
      ∀ P : LocNG.FPair H r, P.RelG (LocNG.theta M) → LocNG.NGAt k P C

def Conclusion1 (D : D7) (C : ℝ) : Prop := 4 * D.R.rS + 7 ≤ D.R.k → NonGenericLocalBound D.R.k D.R.rS C

section Hyps

variable (D : D7) (large₂ : SizeData₂ D)

def KTwoParameterConditions (Cl Cg CT : ℝ) : Prop :=
  Cl * (D.R.m : ℝ) ^ 6 * large₂.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k ∧
  (∀ i : Fin 2, ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (D.host.g i : ℝ) ∧ (D.host.g i : ℝ) ≤ large₂.sc.b ^ Cg) ∧
  (∀ (τ : D.what₂.Tau) (a c : Fin D.R.r), a ≠ c →
    Cl * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 < |lamS D.R (D.hc τ) a - lamS D.R (D.hc τ) c|) ∧
  Cl * Real.log D.host.rdE ≤ large₂.sc.L ∧
  Real.log (D.R.f : ℝ) ≤ (D.R.rS : ℝ) ^ 2 ∧
  (∀ u : D.what₂.Word, ((D.mem u).A.T : ℝ) ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ)) ∧
    Nat.Coprime (D.mem u).A.T (D.host.g 0 * D.host.g 1)) ∧
  Formalism.HermitianLatticesTheory.IsCMUnram D.host.E

def KTwoHypotheses (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ KTwoParameterConditions D large₂ Cl Cg CT

end Hyps

section Terms

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D)

end Terms

def adm7 : Prop :=
  ∀ (k : ℕ) (u u' : Fin k → ℝ) (H H' : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (ρ : Matrix (Fin k) (Fin k) ℂ → (H' →L[ℂ] H')),
    IsHCTypeU k u π → IsHCTypeU k u' ρ → u ≠ u' →
    ∀ P : H' →L[ℂ] H, (∀ h ∈ UJset (allPos k), P.comp (ρ h) = (π h).comp P) → P = 0

section Size

variable (D : D7) (large₂ : SizeData₂ D)

end Size

section Mass

end Mass

section L3

variable (D : D7)

end L3

section Packet

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (Gv : GaugeVol D)

def NonGenericLocalBoundOfLargeRank (CN : ℝ) : Prop := Conclusion1 D CN

end Packet

section Family

variable {eps : ℝ} (Fm : FamP eps) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Gv : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, GaugeVol (Fm.D x i))

def Conclusion1Family (CN : ℝ) : Prop := ∀ x (i : Fm.Ix x), Conclusion1 (Fm.D x i) CN

def FamilyNonGenericLocalBound (CN : ℝ) : Prop := Conclusion1Family Fm CN

end Family

end Formalism.MainNotions.NonGenericAndKTwoTheorems

end
