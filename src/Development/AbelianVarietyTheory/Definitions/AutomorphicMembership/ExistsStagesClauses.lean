module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsMuIsRamified
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordMapBasisFun
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalDivX
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsParametersOver
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulMemOfSpan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FourMulRootLt

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Top.V4.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem ev_imp {p q : Ctx → Prop} (hp : Ev p) (h : ∀ K, p K → q K) : Ev q := by
  obtain ⟨ε0, h0, H⟩ := hp
  refine ⟨ε0, h0, fun eps C8 a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, H⟩ := H eps C8 a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, H⟩ := H C b1 b2 b3
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, H⟩ := H cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, H⟩ := H ch hch
  exact ⟨x0, fun K d1 d2 d3 d4 d5 => h K (H K d1 d2 d3 d4 d5)⟩

theorem mem_iff {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} {Wt : Set X.B.places.Pl} {xi : X.C.Tup → HChar X.B.host.E}
    (h : MuIsW X f T Wt xi) (w : X.B.places.Pl) : w ∈ Wt ↔ X.W.muAt w ≠ X.C.mu0 := by
  refine ⟨fun hw he => ?_, fun hw => by_contra fun hn => hw (h.off w hn)⟩
  have h1 := h.tw w
  rw [← h.on w hw, he, h.mu0] at h1
  exact (TwFin.tw_fin X.B f T).2.1 w h1.symm

variable (hH : DC.HostExQ) (hLP : LevelPrime) (hSP : SmallPrimeOne) (h2b : StandardLattice.SiegelMassRatioCM)






end GlobalTheory.Mem.Top.V4.Model

end
