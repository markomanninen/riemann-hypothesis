module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
public import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfGeometricCovers
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SignatureEmbeddingCoverComp
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NotIsOfFinOrderUnitQuot
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralTmulOneMulMemAdelicCompletion
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
public import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CramerMemAdelicCompletionOfElementSet
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RationalPointsAdelicUnitaryEqUnitary
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SecBCAndCuspBC
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.UnimodularStandardLattice

@[expose] public section

set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

noncomputable section

namespace GlobalTheory.ClassTieCompare

open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot GlobalTheory.IndefiniteRowSideFullHecke.HalfGeometricCovers
open GlobalTheory.XiDetCompare (Reads TrivRat TrivFix XiValC XiValAtC embOf Reaches)
open Formalism.L2.PjFree (Unf.ofPj)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Scalar

variable {D : D7} (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {n : ℕ}

def IsDetOf (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (𝔠 : Ideal (𝓞 D.host.E)) : Prop :=
  𝔠 ⊔ barI H 𝔠 = ⊤ ∧ Submodule.span (𝓞 D.host.E) (detSet L) * idlE (barI H 𝔠) = idlE 𝔠

def GenOff (bad : ℕ) (𝔠 : Ideal (𝓞 D.host.E)) (x : (AE D)ˣ) : Prop :=
  infPart D (x : AE D) = 1 ∧ Generates ((finU D x : IdF D) : AdE D.host.F D.host.E) 𝔠 ∧
    ((finU D x : IdF D) : AdE D.host.F D.host.E) - 1 ∈ idHat D.host.F (Ideal.span {(bad : 𝓞 D.host.E)})

def ReadsId {K : IntermediateField ℚ ℂ} (χ : (AE D)ˣ →* Circle) (bad : ℕ) (B : Ideal (𝓞 D.host.E) → K) : Prop :=
  ∀ 𝔠 x, GenOff bad 𝔠 x → ((B 𝔠 : K) : ℂ) = ((χ x : Circle) : ℂ) * ((Real.sqrt (Ideal.absNorm 𝔠 : ℝ) : ℝ) : ℂ)

def SquareLaw (n bad r : ℕ) : Prop :=
  ∀ (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (𝔠 : Ideal (𝓞 D.host.E)), GlobalTheory.ClassScalarCompare.Guard H bad L →
    IsDetOf H L 𝔠 → ∃ q : ℚ, 0 < q ∧
      q ^ 2 * (((L ⊓ stdLat D.host.E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ r = (Ideal.absNorm 𝔠 : ℚ)

variable {H} {Dw : Datum H} {l : Level H} {c : Coeff l}

theorem isDetOf_unique {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {a b : Ideal (𝓞 D.host.E)} (ha : IsDetOf H L a)
    (hb : IsDetOf H L b) : a = b := by
  have e : idlE (a * barI H b) = idlE (b * barI H a) := by
    have m : ∀ I J : Ideal (𝓞 D.host.E), idlE (I * J) = idlE I * idlE J := fun I J =>
      Submodule.map_mul I J (Algebra.ofId (𝓞 D.host.E) D.host.E)
    rw [m, m, ← ha.2]
    conv_rhs => rw [← hb.2]
    ring
  have e' : a * barI H b = b * barI H a :=
    Submodule.map_injective_of_injective (f := Algebra.linearMap (𝓞 D.host.E) D.host.E)
      (FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E) e
  exact le_antisymm
    (Ideal.le_of_dvd ((Ideal.isCoprime_iff_sup_eq.2 hb.1).dvd_of_dvd_mul_right ⟨_, e'⟩))
    (Ideal.le_of_dvd ((Ideal.isCoprime_iff_sup_eq.2 ha.1).dvd_of_dvd_mul_right ⟨_, e'.symm⟩))

theorem exists_epIs_iff (bad : ℕ) (B : Ideal (𝓞 D.host.E) → c.F) :
    (∃ epF : Submodule (𝓞 D.host.E) (Fin n → D.host.E) → c.F, EpIs (Dw := Dw) c bad B epF) ↔
      SquareLaw H n bad (Dw.p + Dw.q) := by
  classical
  constructor
  · rintro ⟨epF, h⟩ L 𝔠 g h1
    obtain ⟨q, q0, q1, -⟩ := h L 𝔠 g.1 g.2.1 g.2.2 h1.1 h1.2
    exact ⟨q, q0, q1⟩
  · intro h
    have key : ∀ L : Submodule (𝓞 D.host.E) (Fin n → D.host.E), ∃ v : c.F, ∀ 𝔠, GlobalTheory.ClassScalarCompare.Guard H bad L →
        IsDetOf H L 𝔠 → ∃ q : ℚ, 0 < q ∧
          q ^ 2 * (((L ⊓ stdLat D.host.E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ (Dw.p + Dw.q) =
            (Ideal.absNorm 𝔠 : ℚ) ∧ v = (B 𝔠)⁻¹ * (q : c.F) := by
      intro L
      by_cases hL : ∃ 𝔠, GlobalTheory.ClassScalarCompare.Guard H bad L ∧ IsDetOf H L 𝔠
      · obtain ⟨𝔠, g, h1⟩ := hL
        obtain ⟨q, q0, q1⟩ := h L 𝔠 g h1
        refine ⟨(B 𝔠)⁻¹ * (q : c.F), fun 𝔠' _ h2 => ?_⟩
        obtain rfl := isDetOf_unique h1 h2
        exact ⟨q, q0, q1, rfl⟩
      · exact ⟨0, fun 𝔠 g h1 => absurd ⟨𝔠, g, h1⟩ hL⟩
    choose epF hepF using key
    exact ⟨epF, fun L 𝔠 g1 g2 g3 h1 h2 => hepF L 𝔠 ⟨g1, g2, g3⟩ ⟨h1, h2⟩⟩

end Scalar

section Value

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {n r : ℕ}
variable (V : HSp D) (hr : V.rank = r)

section One

variable {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)
  (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)

variable {V hr U dict ι x₀} {c0 : ℂ} {xi : (AdE D.host.F D.host.E)ˣ →* ℂˣ} {ξ : IdF D →* Circle} {f : Rul Xo c}

end One

section Diag

variable {V} {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ V.rank} {dict : GA D V → Σ k, Frame (U.X k).Ψ V.rank}
  {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} {x₀ : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ}
  {g : ℕ}

end Diag

section Compare

variable {V hr} {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ r} {dict : GA D V → Σ k, Frame (U.X k).Ψ r}
  {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)} {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
  {c0 : ℂ} {xi : (AdE D.host.F D.host.E)ˣ →* ℂˣ} {ξ : IdF D →* Circle} {f : Rul Xo c}

end Compare

end Value

section Record

variable {D : D7} {T : CoreJ D} {X : ThetaX D} (Tt : ThetaTied D X) (j : ℕ) {c' : Coeff T.Q.l} (h : T.Q.c.F ≤ c'.F)
  (ka : WeightFamilies.Wt D j) (lam : D.what₂.Tau → DomWeight D.R.nV)
  (PQ : D.what₂.Tup → Ideal (𝓞 D.host.E)) (β : Fin D.R.r → (T.Q.Dw j).La)
  (Cl : D.what₂.Tup → Type) [∀ t, Fintype (Cl t)]
  (Lh : ∀ t, Cl t → Submodule (𝓞 D.host.E) (Fin D.R.nV → D.host.E)) (gam : ∀ t, Cl t → ℕ) (vol : D.what₂.Tup → c'.F)
  (thAd : ∀ t, (Cl t → VVc c' lam) → AutQ (T.V j (sig0 T.Q.c)) → ℂ) (Pl : ∀ t, (Cl t → VVc c' lam) → Prop) (ph : ℂ)
  (ξ : D.what₂.Tup → IdF D →* Circle) (bad : D.what₂.Tup → ℕ)
  (d : D.what₂.Tup → DeltaDat (T.Q.Xo j) c' D.R.nV)
  (φ : ∀ t, (Fin D.R.nV → LevQc (T.Q.Dw j) (d t).l₂) → c'.F)
  (w : ∀ t, Cl t → (Fin D.R.nV → LevQ (T.Q.Dw j) (d t).l₂) → c'.F)
  (La : ∀ t, Cl t → GenLat D.host.E D.R.nV) (Nc : ∀ t, Cl t → ℕ) (ep : ∀ t, Cl t → c'.F)
  (io : VVc c' lam →ₗ[c'.F] MvPolynomial (LtN (T.Q.Dw j) D.R.nV) c'.F)
  (hr : (T.V j (sig0 T.Q.c)).rank = D.R.r) (B : D.what₂.Tup → Ideal (𝓞 D.host.E) → c'.F)
  (epF : D.what₂.Tup → Submodule (𝓞 D.host.E) (Fin D.R.nV → D.host.E) → c'.F) (cond : ℕ) (hw : VVc c' lam)
  (U₂ : ∀ t, Unf (d t).Xo₂ (d t).c₂ ((sig0 c').comp ((d t).eF.symm : (d t).c₂.F →+* c'.F)) D.R.r)
  (dict₂ : ∀ t, GA D (T.V j (sig0 T.Q.c)) → Σ k, Frame ((U₂ t).X k).Ψ D.R.r)
  (xi : D.what₂.Tup → (AdE D.host.F D.host.E)ˣ →* ℂˣ)

variable {Tt j h ka lam PQ β Cl Lh gam vol thAd Pl ph ξ bad d φ w La Nc ep io hr B epF cond hw U₂ dict₂ xi}

variable (Tt j h ka lam PQ β Cl Lh gam vol thAd Pl ph ξ bad d φ w La Nc ep io hr B epF cond hw U₂ dict₂ xi)

end Record

end GlobalTheory.ClassTieCompare
