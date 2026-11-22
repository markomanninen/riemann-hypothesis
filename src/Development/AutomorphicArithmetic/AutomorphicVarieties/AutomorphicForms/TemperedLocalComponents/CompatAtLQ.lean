module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.UntwistS
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.RecMove
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SelfDualQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExQuad
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExtReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.SignFix
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.CsdTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterTwistPotentiallySemistableStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamCharacterTwistIffLocalEmbedding
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParameterTensorOneDimInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumSegmentsLanglands
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExPlaceIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.PstRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.WdRelRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.EmbPadic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.RecTransport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

private theorem isIrr_comp {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k} {φ : Γ' →* Γ}
    (h : ∀ g, ∃ g', r g = r (φ g')) (hr : IsIrr r) : IsIrr (r.comp φ) :=
  ⟨hr.1, fun _ _ _ => trivial, fun W hW hi => hr.2.2 W hW fun g v hv => by
    obtain ⟨g', e⟩ := h g
    rw [e]
    exact hi g' v hv⟩

private theorem range_of_sign {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
    [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (hK : Module.finrank ℚ K = 2) {H : Type} [Group H] {r : G ℚ Ω →* H} {s : G ℚ Ω}
    (hs : s ∉ (Bc.res ℚ Ω K).range) (h1 : r s = 1) (g : G ℚ Ω) : ∃ g', r g = r (Bc.res ℚ Ω K g') := by
  obtain ⟨δ, -, -, ⟨ha, hb⟩, -⟩ := UpperTheory.exists_quadratic_sign_character ℚ K Ω l hK
  by_cases hg : δ g = 1
  · obtain ⟨g', rfl⟩ := (ha g).1 hg
    exact ⟨g', rfl⟩
  · have e : δ (g * s) = 1 := by
      rw [map_mul, (hb g).resolve_left hg, (hb s).resolve_left (mt (ha s).1 hs)]
      simp
    obtain ⟨g', e'⟩ := (ha _).1 e
    exact ⟨g', by rw [e', map_mul, h1, mul_one]⟩

private theorem regAlg_twist {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {m : (K →+* ℂ) → ℤ} (hκ : κ.IsAlg m) : (CG.mk (P.twist κ)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 m hκ τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + m τ, by push_cast; ring⟩

end UpperTheory.V.Af

end
