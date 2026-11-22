module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatGlueLatIffDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGLOfIsVecBasisAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSpacesIsometricOfRankSignatureStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianStdIsometryOfRationalIsometryStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLineDecompositionsOfBaseSpaceProofStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCHyperbolicExtensionLatticeConjStableStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjStableInverseDifferentAndNormIdealStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimitiveLatticeGluedFromIntersectionStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsAdelicGlueVectorOfGlueBaseDataStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGlueBaseDataOfIsAdelicGlueVectorStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedHermitianLatticeUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalLatticeEqIffIdempotentComponentsOverStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeImageAdelicUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorrectionOfTransportStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIsometryTransportUniqueModStabilizerStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAdelicGlueVectorOfSelfDualPrimitiveStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedLatticeSelfDualPrimitiveMeetStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedLatticePrescribedLocalComponentsStatement

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Links
open Formalism.IndefR.Datum (IsSelfDualC)
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.AdIsom

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents
open GlobalTheory.StdFrames hiding OA
open GlobalTheory.IdemSupport (cP cO)
open GlobalTheory.NormSum.AdLattice (lat)

variable {D : D7}

theorem transportSt (D : D7) : TransportSt D := by
  intro W Y hr L Λ hL hΛ S hS n be be' h h'
  refine ⟨exists_transport W Y hr L Λ hL hΛ S hS n be be' h h', fun x hx x' => ?_⟩
  first
  | exact GlobalTheory.T.adelicIsometry_transport_unique_mod_stabilizer D W Y L Λ S hS n be be' (selfDual_isFullLattice hL) h x hx x'
  | exact GlobalTheory.T.adelicIsometry_transport_unique_mod_stabilizer D W Y L Λ S hS n be be' hL.1 h x hx x'

private theorem fullLattice_of_glueVec {X : HSp D} {u : D.what₂.Word} {L₀ : Lat X}
    {f : Fin X.rank → EAf D} (hL : L₀.FG) (hf : IsGlueVec X u L₀ f) :
    Submodule.IsFullLattice D.host.E L₀ := by
  let β₀ : GL (Fin X.rank) (EAf D) := 1
  have hstd := GlobalTheory.NormSum.AdLattice.lat_isLattice β₀
  have hfull : Submodule.IsFullLattice D.host.E (L₀ ⊔ lat β₀) :=
    Submodule.IsFullLattice.of_le_of_fg _ le_sup_right (hL.sup hstd.fg)
  obtain ⟨β, hβ⟩ := exists_eq_lat hfull
  obtain ⟨β', hβ', -⟩ := exists_dual_frame X β
  have hle : L₀ ≤ lat β := hβ ▸ le_sup_left
  have := GlobalTheory.NormSum.AdLattice.lat_isLattice β'
  have := Submodule.IsLattice.of_fg D.host.E hL
  let t : D.host.Eˣ := Units.mk0 (Tu D u) (Tu_ne_zero u)
  refine Submodule.IsFullLattice.of_le D.host.E (M := t • lat β') ?_
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
  apply GlobalTheory.GlueUnique.mem_of_inc_mem_hat hL
  let xA : Fin X.rank → EAf D := fun i => inc D (x i)
  have hxA : ∀ z ∈ hat L₀, hA X z xA ∈ OA D :=
    fun z hz => (dual_hat_lat hβ' xA).2 (inc_mem_hat hx) z (hat_mono hle hz)
  obtain ⟨a, ha, hxa⟩ := hf.dual xA hxA
  have htx := add_mem_hat (smul_mem_hat (inc_Tu_mem u) hxa) (smul_mem_hat ha hf.mul_mem)
  rw [smul_sub, smul_comm (inc D (Tu D u)) a, sub_add_cancel] at htx
  convert htx using 1
  funext i
  change inc D (Tu D u * x i) = inc D (Tu D u) * inc D (x i)
  exact map_mul _ _ _

theorem gluedSt (D : D7) : GluedSt D := by
  intro u π hπ Y X ι z hz L₀ f₀ hb
  obtain ⟨f, hf, hff⟩ := GlobalTheory.T.exists_isAdelicGlueVector_of_glueBaseData D u π hπ X L₀ f₀ hb
  have hL₀ := fullLattice_of_glueVec hb.1.fg hf
  obtain ⟨x, hx⟩ := exists_sub_inc_mem_hat (D := D) (Λ := L₀) hL₀.span_eq_top f
  obtain ⟨x₀, hx₀⟩ := vA_surj X x
  rw [← hx₀] at hx
  have hg : IsGlueVec X u L₀ (vA X x₀) := hf.congr hx
  have hgl : IsGlued Y X ι z u π L₀ f₀ (glueLat Y X ι z u L₀ x₀) := by
    refine GlobalTheory.T.gluedLattice_prescribed_localComponents D u π Y X ι z hz L₀ x₀ f₀ hL₀.toIsLattice hg (fun w hw => ⟨?_, ?_⟩)
    · rw [← hff w hw, smul_smul, idem_mul_self]
    · rw [← hff w hw, ← smul_sub]
      exact smul_mem_hat (idem_mem w) hx
  have huniq : ∀ L, IsGlued Y X ι z u π L₀ f₀ L → L = glueLat Y X ι z u L₀ x₀ :=
    fun L hL => GlobalTheory.T.gluedHermitianLattice_unique D u π hπ Y X ι z L₀ f₀ L _ hL hgl
  refine ⟨⟨_, hgl, huniq⟩, fun L hL => ?_⟩
  rw [huniq L hL]
  exact GlobalTheory.T.gluedLattice_selfDual_primitive_meet D u Y X ι z hz L₀ x₀ hL₀ hg

theorem ungluedSt (D : D7) : UngluedSt D := by
  intro u π hπ Y X ι z hz L hSD hP
  obtain ⟨hlat, x₀, hL⟩ := GlobalTheory.T.primitive_lattice_glued_from_intersection D u Y X ι z hz L hSD hP

  have hg : IsGlueVec X u (capX Y X ι L) (vA X x₀) := by
    have key := GlobalTheory.T.isAdelicGlueVector_of_selfDual_primitive D u Y X ι z hz (capX Y X ι L) x₀ hlat
    rw [← hL] at key
    exact key hSD hP
  have := hlat
  refine ⟨fun w => idem w • vA X x₀,
    GlobalTheory.T.isGlueBaseData_of_isAdelicGlueVector D u π hπ X _ _ (by infer_instance) hg, ?_⟩
  have key := GlobalTheory.T.gluedLattice_prescribed_localComponents D u π Y X ι z hz (capX Y X ι L) x₀ (fun w => idem w • vA X x₀) hlat.toIsLattice hg
    (fun w _ => ⟨by simp only [smul_smul, idem_mul_self], by simp only [sub_self]; exact zero_mem_hat⟩)
  rwa [← hL] at key

theorem adelicIsometries (D : D7) : AdelicIsometries D := by
  unfold AdelicIsometries LamNSt
  exact ⟨plIdemSt D, transportSt D, GlobalTheory.T.correctionSt_of_transportSt D (transportSt D),
    splitGlueSt_of D (fun n Λ Λ' hΛ hΛ' v => GlobalTheory.T.localLattice_eq_iff_idempotent_components_over D n Λ Λ' hΛ hΛ' v),
    GlobalTheory.T.selfDualLattice_image_adelicUnitary D, GlobalTheory.T.hermitianSpaces_isometric_of_rank_signature D, GlobalTheory.T.hermitianStdIsometry_of_rationalIsometry D (GlobalTheory.T.hermitianSpaces_isometric_of_rank_signature D), GlobalTheory.T.normLineDecompositionsOfBaseSpace_proof D,
    gluedSt D, ungluedSt D,
    ⟨fun u Y X ι z ρ e f h L hL nn hn => GlobalTheory.T.isSelfDualC_hyperbolicExtensionLattice_conjStable D u Y X ι z ρ e f h L hL nn hn,
      (GlobalTheory.T.conjStable_inverseDifferent_and_normIdeal D).1, (GlobalTheory.T.conjStable_inverseDifferent_and_normIdeal D).2⟩,
    frameSt D⟩

end GlobalTheory.AdIsom

end
