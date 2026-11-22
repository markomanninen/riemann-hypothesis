module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.EvTieP
public import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2

@[expose] public section

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
open Formalism.IndefR.CxPass
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem cxFacts_of_prims : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (n : ℕ), A3.fam3.Ok3 n → A3.fam3.TypesSep3 → R.WeakCharacterisation F → PrimRows3 R F → CxFacts (R.toCx3 F) F.cr (F.eV (R.toCx3 F).zs) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F n hOk hSep hC hP
  let X := R.toCx3 F
  have hKR : X.KFormR := RealDat3.kFormR_of (F := F) hC.base.models
  have hKL : X.KFormL := RealDat3.kFormL_of (F := F) hC.base.models
  have hJR : X.JIsoR F.cv := RealDat3.jIsoR_of (F := F) hC.base.models
  have hJL : X.JIsoL F.cv := RealDat3.jIsoL_of (F := F) hC.base.models
  have hStable : X.zs.Stable :=
    CxData.cutStable X hKR hKL
      (definite_kernel_stable hKR hP.gEquiv.1 hP.hecke.1.choose_spec)
      (lift_kernel_stable hKL hP.gEquiv.2 hP.hecke.2.choose_spec)
      (definite_adjoint_closed hOk hP.heckeR hKR hJR)
      (lift_adjoint_closed hOk hP.heckeL hKL hJL)
  have hWF : (F.fc X.zs).Df1.WF :=
    A3.side_well_formed hOk F.P1 F.ψ1 X.zs hStable hP.block hSep
  have hPos : X.H4pos := ⟨fun _ => hP.posScal.1, hP.posScal.2, RealDat.nP_pos⟩
  have hRatZ : X.RatZ :=
    Formalism.IndefR.Rat.ratZOfTests X F.cv hKR hKL hJR hJL hP.rowTest hP.liftTest
  have hRat : X.RatLev F.cr F.cv true :=
    rationality_at_level_of_equivariance hOk hKR hJR hRatZ hP.gUnit.1 hP.gEquiv.1 true
  have hDn : X.DnLev F.cv true :=
    descent_of_types hOk hKR hJR hRatZ hP.gUnit.1 hP.gEquiv.1 hP.h2P hP.levE.1 hP.levE.2 true
  have hUp : X.UpLev F.cv true :=
    upper_level_of_types hOk hKR hJR hP.gUnit.1 hP.gEquiv.1 hP.levE.1 hP.levE.2 true
  have hGood : X.CoordinatesInGoodPart F.cr F.cv true := definite_coordinates_in_good_part X true
  have hIso : X.IsoR F.cr true := definite_isometry_of_norms hOk hJR ⟨rfl, rfl⟩ true
  have hSubspaces : X.CrdZ F.cr true := definite_coordinates_in_subspaces X true
  have hRows : X.H2 F.cr true ∧ X.H4 F.cr true :=
    cutRows (X := X) F.cr F.cv true hWF hPos hIso hSubspaces hGood hRat hDn hUp
      (RealDat3.thmBop_of (F := F) hP.thmB true) (hP.sumE true)
  exact
    { wf := hWF
      h2 := hRows.1
      pos := hPos
      theta := X.theta_eV F.cr F.cv (F.eV X.zs) hJR hRat hDn hUp hGood (EvTie.evTie_of_ok hOk F X) _ }

end GlobalTheory.Mem.SJ
