module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionZeroIntegralIffComponentsAbove
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
public import Formalism.LocalToGlobal.Columns.UnfoldingNonvanishingDoubleCosetHolds
public import Formalism.LocalToGlobal.Columns.ChainLawXiQF
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerHypAll
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertAtLeCongN
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
public import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases

@[expose] public section

noncomputable section

namespace GlobalTheory.TwU.WildChar

open _root_.Formalism.L2.Col _root_.Formalism.L2.DIV _root_.Formalism.L2.Ker _root_.Formalism.UG _root_.Formalism.L2.Forms
open NumberField IsDedekindDomain _root_.Formalism.BasicNotions _root_.Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct

section Idele

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)

end Idele

section Central

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} (t : KerEntTied ex) {u : D.what₂.Word} (μ : D.what₂.Tup)

variable {t μ} {St : ChainCharts D u μ} {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E}


end Central

section Twist

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

end Twist

section Charts

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {i : ℕ} {hi : i ≤ D.R.m} {cl : Type}
  {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}


end Charts

section True

open GlobalTheory.TwU.AtTrue

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar



end True

end GlobalTheory.TwU.WildChar

end

noncomputable section

namespace GlobalTheory.TwU.Rigid

open _root_.Formalism.UG _root_.Formalism.L2.Col _root_.Formalism.L2.PairingIndexBounds.F _root_.Formalism.MainNotions.G.KAat _root_.Formalism.L2.Forms _root_.Formalism.L2.Ker _root_.Formalism.L2.DIV
open NumberField IsDedekindDomain Matrix _root_.Formalism.BasicNotions _root_.Formalism.MainNotions _root_.Formalism.MainNotions.G
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E}


end GlobalTheory.TwU.Rigid

end

noncomputable section

namespace GlobalTheory.TwU.Model

open NumberField IsDedekindDomain Matrix _root_.Formalism.BasicNotions _root_.Formalism.MainNotions _root_.Formalism.L2.Col _root_.Formalism.L2.Ker _root_.Formalism.L2.DIV _root_.Formalism.L2.Forms _root_.Formalism.UG
open scoped TensorProduct

section CongBasic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem intAtA_add {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a + b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  have hi : ∀ x : 𝓞 E, iA F E (algebraMap (𝓞 E) E x) ∈ Formalism.L2.Herm.intAf F E := fun x => (toRInt F E x).2
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a + b) =
      iA F E (algebraMap (𝓞 E) E r) * (iA F E (algebraMap (𝓞 E) E s) * a) +
        iA F E (algebraMap (𝓞 E) E s) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact add_mem (mul_mem (hi r) h1) (mul_mem (hi s) h2)

theorem intAtA_mul {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a * b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a * b) =
      (iA F E (algebraMap (𝓞 E) E s) * a) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact mul_mem h1 h2

theorem intAtA_int (x : 𝓞 E) : IntAtA (F := F) P (iA F E (algebraMap (𝓞 E) E x)) :=
  ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [map_one, map_one, one_mul]; exact (toRInt F E x).2⟩

theorem intAtA_sum {ι : Type} (s : Finset ι) (f : ι → E ⊗[F] FiniteAdeleRing (𝓞 F) F) (h : ∀ i ∈ s, IntAtA (F := F) P (f i)) :
    IntAtA (F := F) P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using intAtA_int (F := F) (P := P) 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact intAtA_add (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end CongBasic

theorem sameCoset_equiv {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ} (P : rowSG Pr sel mu) :
    Equivalence (fun y y' : Sp X.E n => SameCoset sel mu cst P y y') := by
  constructor
  · intro y l
    rw [sub_self, Pi.zero_apply, mul_zero]
    exact ciIntAt_zero
  · intro y y' h l
    have h1 := ciIntAt_neg (h l)
    rwa [← mul_neg, ← Pi.neg_apply, neg_sub] at h1
  · intro x y z h h' l
    have h1 := (h l).add (h' l)
    rwa [← mul_add, ← Pi.add_apply, sub_add_sub_cancel] at h1

end GlobalTheory.TwU.Model

end
