module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDegenerationDataAlgebraicPointModel
public import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
public import Formalism.LocalToGlobal.ProjectiveLattices.LatPAddRight
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.DepLaws
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degeneration_data_algebraic_point_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : ℕ) (C : SCF p) (P : PointsOfFlagModel.PtC Y C), p.Prime → ∀ (T : CDVR) (g : T.V →+* intO ↥C.S) (ιT : Sp T.V ⟶ Y.X), T.FinRes → Function.Injective g → (∀ a ∈ maximalIdeal T.V, ‖((g a : intO ↥C.S) : ↥C.S)‖ < 1) → spMap g ≫ ιT = P.yt → ∃ A : DatAt Y P, (∃ _ : IsDiscreteValuationRing A.R, Finite (ResidueField A.R)) ∧ Function.Injective A.f ∧ ∃ φ : T.V →+* A.R, A.f.comp φ = g ∧ A.ι = spMap φ ≫ ιT ∧ φ.Finite := by
  first | exact @GlobalTheory.DatAtPoint.exists_datAt | exact GlobalTheory.DatAtPoint.exists_datAt | (intros; apply GlobalTheory.DatAtPoint.exists_datAt <;> assumption)
