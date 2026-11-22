module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAdelicGlueVectorOfSelfDualPrimitive
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatGlueLatIffDual

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdelicGlueVector_of_selfDual_primitive : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V), Submodule.IsFullLattice D.host.E L₀ → IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) → IsPrim Y z (glueLat Y X ι z u L₀ x₀) → IsGlueVec X u L₀ (vA X x₀) := by
  intro D u Y X ι z h L₀ x₀ hlat hSD hP
  letI := hlat
  exact GlobalTheory.AdIsom.SelfDualGlue.isGlueVec_of_isSDIn D u Y X ι z h L₀ x₀
    (by first | exact hlat | infer_instance) hSD hP
