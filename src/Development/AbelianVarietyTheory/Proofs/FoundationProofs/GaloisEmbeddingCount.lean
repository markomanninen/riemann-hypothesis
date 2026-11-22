module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.GaloisCohomology.Statement
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction

namespace GlobalTheory.Proof.GaloisEmbeddingCount

theorem card_ringHom_of_isGalois (E F : Type) [Field E] [NumberField E] [IsGalois ℚ E] [Field F]
    (φ : E →+* F) : Nat.card (E →+* F) = Module.finrank ℚ E := by
  haveI : CharZero F := (RingHom.charZero_iff φ.injective).1 inferInstance
  letI : Algebra E F := φ.toAlgebra
  haveI : IsScalarTower ℚ E F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  rw [Nat.card_congr (RingHom.equivRatAlgHom E F), Nat.card_congr (Normal.algHomEquivAut ℚ F E),
    IsGalois.card_aut_eq_finrank]

end GlobalTheory.Proof.GaloisEmbeddingCount
