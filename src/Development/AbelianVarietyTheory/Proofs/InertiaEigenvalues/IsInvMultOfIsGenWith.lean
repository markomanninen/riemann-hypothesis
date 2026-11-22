module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DiagonalQuotientEigen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantCoboundaries

@[expose] public section

noncomputable section

namespace GlobalTheory.SenCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc TensorProduct GlobalTheory.IndefiniteRowSideFullHecke

section Operators

variable {O A D : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup D] [Module A D] [Module O D]
  [IsScalarTower O A D]

variable {π : A} {g : D →ₗ[O] D} {P Q : Submodule O D}

end Operators

section Residue

variable {O : Type} [CommRing O]

end Residue

section Sen

variable {O A D : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup D] [Module A D] [Module O D]
  [IsScalarTower O A D] [IsDomain O] [IsDiscreteValuationRing O]

end Sen

section Wach

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

section RankOne

variable {r : ℕ} (hr : r = 1) (β : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (hβ : ∀ k, (β k : W.DD T) ∈ W.NΔ T)
include hr hβ

end RankOne

end Wach

section Prime

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P)

variable {K LL : FinExt l} (hA : CaseA K LL)

theorem standing_iff {hg : Good K 1 LL} (lam : ↥(OL LL)) :
    Standing P K LL (H.W K 1 LL hg).emb lam ↔ 5 ≤ l ∧ CaseA K LL ∧ Irreducible lam :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2.2.2.2⟩, fun h => ⟨h.1, h.2.1, by rw [show K0 K = K.1 from inf_eq_left.2 h.2.1.1],
    (H.W K 1 LL hg).emb_bij, (H.W K 1 LL hg).emb_σ, h.2.2⟩⟩

end Prime

end GlobalTheory.SenCompare
