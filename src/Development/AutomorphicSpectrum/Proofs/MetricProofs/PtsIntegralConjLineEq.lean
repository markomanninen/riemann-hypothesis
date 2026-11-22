module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArIntConj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

namespace GlobalTheory.CompanionTheory.Ar.Tw

theorem ptsIntegral_conjLine : PtsIndepStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι), IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn Q A s → ptsIntegral Q (pot fun j => conjLine (L j)) (logNorm (conjLine A) s) = ptsIntegral Q (pot L) (logNorm A s) := by
  intro hI K _ ι _ Q e L A s hQ hL hA hs
  exact GlobalTheory.CompanionTheory.Ar.Cmp.arInt_conj
    (fun K _ ι _ P e Ψ L A s hP hΨ hL hA hs => sheetIndep K ι P e Ψ L A s hP hΨ hL hA hs) hI
    (fun K _ ι _ P e hP => goodProjExists K ι P e hP) K ι Q e L A s hQ hL hA hs

end GlobalTheory.CompanionTheory.Ar.Tw
