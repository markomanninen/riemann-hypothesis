module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BrPairFApply
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.PieriBlockIdeals.StatementLA
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem isLattice_comap_gl {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : Type} [Fintype n] [DecidableEq n]
    (g : GL n K) (M : Submodule R (n → K)) (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K (M.comap (g.1.mulVecLin.restrictScalars R)) := by
  let e : (n → K) ≃ₗ[K] (n → K) := LinearEquiv.ofLinear g.1.mulVecLin (g⁻¹).1.mulVecLin
    (by rw [← Matrix.mulVecLin_mul, Units.mul_inv, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, Units.inv_mul, Matrix.mulVecLin_one])
  have h : M.comap (g.1.mulVecLin.restrictScalars R) = M.map ((e.symm : (n → K) →ₗ[K] (n → K)).restrictScalars R) := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      have : e (e.symm y) ∈ M := by rw [e.apply_symm_apply]; exact hy
      exact this
  rw [h]
  refine ⟨hM.fg.map _, ?_⟩
  have h2 : ((M.map ((e.symm : (n → K) →ₗ[K] (n → K)).restrictScalars R) : Submodule R (n → K)) : Set (n → K)) =
      (e.symm : (n → K) →ₗ[K] (n → K)) '' (M : Set (n → K)) := rfl
  intro s hs hi
  rw [h2] at hs
  have hs' : e '' s ⊆ (M : Set (n → K)) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hs hx
    simpa [← hyx] using hy
  have hi' : LinearIndepOn R id (e '' s) :=
    (linearIndepOn_id_imageₛ_iff (f := (e : (n → K) →ₗ[K] (n → K)).restrictScalars R)
      (show Function.Injective ((e : (n → K) →ₗ[K] (n → K)).restrictScalars R) from e.injective).injOn).2 hi
  have hk := hM.linearIndepOn (e '' s) hs' hi'
  have hk' := (linearIndepOn_id_imageₛ_iff (f := (e.symm : (n → K) →ₗ[K] (n → K)))
    (show Function.Injective (e.symm : (n → K) →ₗ[K] (n → K)) from e.symm.injective).injOn).2 hk
  change LinearIndepOn K id (e.symm '' (e '' s)) at hk'
  simpa [Set.image_image] using hk' 

theorem _root_.GlobalTheory.T.isLattice_vertexLattice_gridCorner : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ)
    (y : FinPt G (.grid D.R.m D.R.m)), Submodule.IsLattice D.host.E (GlobalTheory.SumSize.latAt S (.grid D.R.m D.R.m) y) := by
  intro D T L sc G W S y
  have hm := D.R.two_le_m
  have hΛ : Submodule.IsLattice D.host.E (G.Λ (.grid D.R.m D.R.m)) :=
    (G.isV (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ fun j e => by
      have : D.R.m = 0 := (Node.grid.inj e).1
      omega).sd.1
  apply isLattice_comap_gl _ _
  apply Submodule.IsLattice.of_fg
  obtain ⟨c, hc, hu⟩ := Formalism.UG.P.adelstabL_upper (F := D.host.F) _ (Module.Finite.iff_fg.2 hΛ.fg)
  obtain ⟨d, hd, c', hc', hcg, hcgi⟩ := Formalism.UG.P.levelaf_exists_denom (E := D.host.E) (finG (G.V (.grid D.R.m D.R.m)) y)
  have hG := Formalism.UG.P.adelstab_entries (finG (G.V (.grid D.R.m D.R.m)) y) d c' hc' hcg
  exact Module.Finite.iff_fg.mp (Formalism.UG.P.adelstab_finite (finG (G.V (.grid D.R.m D.R.m)) y) _ c d hc hd hu hG)
