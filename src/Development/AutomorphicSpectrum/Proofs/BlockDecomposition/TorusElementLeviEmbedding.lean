module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.CasimirOnParabolicInduction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOneLMemZalg
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStableBdSub

@[expose] public section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc.LevAt

theorem aT_eq_lev (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (t : ℝ) :
    aT E (r + s) r t = GlobalTheory.CompanionTheory.CTFin.lev (Ad E) r s (aT E r r t, 1) := by
  apply Units.ext
  have val_emb (g : GL (Fin r) (Ad E) × GL (Fin s) (Ad E)) :
      (GlobalTheory.CompanionTheory.CTFin.lev (Ad E) r s g : Matrix (Fin (r + s)) (Fin (r + s)) (Ad E)) =
        Matrix.reindex (GlobalTheory.SmGL.stdSum rfl) (GlobalTheory.SmGL.stdSum rfl)
          (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    obtain ⟨i, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
    obtain ⟨j, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    all_goals simp [GlobalTheory.CompanionTheory.CTFin.lev, GlobalTheory.SmGL.emb₂,
      GlobalTheory.SmGL.leviEmb, GlobalTheory.SmGL.leviTwo, GlobalTheory.SmGL.two,
      Matrix.blockDiagonal'_apply]
  rw [PositivityTheory.Rg.Rs.JFinTr.aT_val, val_emb]
  ext i j
  obtain ⟨i, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr, PositivityTheory.Rg.Rs.JFinTr.aT_val, Matrix.diagonal_apply]
  have h1 : (fun _ : InfinitePlace E => (1 : ℂ)) = (1 : Cinf E) := rfl
  rw [h1, sub_add_cancel, Matrix.one_apply]

end GlobalTheory.CompanionTheory.Conc.LevAt
