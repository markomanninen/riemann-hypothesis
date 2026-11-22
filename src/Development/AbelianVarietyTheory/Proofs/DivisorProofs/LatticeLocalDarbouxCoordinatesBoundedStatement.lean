module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLocalDarbouxCoordinatesBounded
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeLocalDarbouxCoordinates_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v : Pl (F := F), ∃ c : Fv F v, c ≠ 0 ∧ ∀ γ ∈ latAtV G.V G.W v, ∀ k,
      c * (GlobalTheory.LatVac.locCo G.M.co v γ).1 k ∈ HeightOneSpectrum.adicCompletionIntegers F v ∧
      c * (GlobalTheory.LatVac.locCo G.M.co v γ).2 k ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
  first | exact @GlobalTheory.LatVacBdd.locCo_bounded | exact GlobalTheory.LatVacBdd.locCo_bounded | (intros; apply GlobalTheory.LatVacBdd.locCo_bounded <;> assumption)
