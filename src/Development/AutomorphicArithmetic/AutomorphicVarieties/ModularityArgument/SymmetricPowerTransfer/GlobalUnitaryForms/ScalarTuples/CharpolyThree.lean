module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CubicCharpolyDiscriminant

@[expose] public section

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open Matrix Polynomial Loc

private theorem charpoly_three {R : Type} [CommRing R] (N : Matrix (Fin 3) (Fin 3) R) :
    N.charpoly = X ^ 3 - C N.trace * X ^ 2 + C N.adjugate.trace * X - C N.det := by
  simp only [Matrix.charpoly, Matrix.det_fin_three, Matrix.charmatrix_apply, Matrix.adjugate_fin_three,
    Matrix.trace_fin_three]
  simp [Matrix.diagonal_apply, Matrix.det_fin_three]
  ring

end UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Glob.tauEx :
    UpperTheory.V.Z.Sym.Glob.TauEx :=
  _root_.UpperTheory.Reformulated.B.CubicCharpolyDiscriminant.tauEx
