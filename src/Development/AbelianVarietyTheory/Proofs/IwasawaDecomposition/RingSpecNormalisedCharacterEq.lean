module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HeightCounting.SideCopy

structure CopyAll (D D' : D7) (ι : D.what₂.LL →+* D'.what₂.LL) (e : ↥D'.LL0 ≃+* ↥D.LL0) : Prop where
  cp : CopyTw D D' ι e
  jL : HEq D.ntw.jL D'.ntw.jL
  s2 : HEq D.ntw.s2 D'.ntw.s2
  lamG : HEq D.ntw.lamG D'.ntw.lamG
  Xv : HEq D.ntw.Xv D'.ntw.Xv
  qs : HEq D.ntw.qs D'.ntw.qs
  pl : HEq D.naut.plGw D'.naut.plGw

structure SameFrame {D D' : D7} (cf : CharFrame D) (cf' : CharFrame D') : Prop where
  mu0 : HEq cf.mu0 cf'.mu0
  eta : HEq cf.eta cf'.eta
  del : HEq cf.del cf'.del
  del' : HEq cf.del' cf'.del'

structure RingPart (D : D7) (cf : CharFrame D) (low : Finset ℕ) where
  twF : TwFrameC D
  tw : TwistFrameLowIndexCompatibility D twF low
  chiD : NC.NChiData D
  chi : NC.NormalizedCharacterCompatibility D chiD
  eta_eq : ∀ x, chiD.etaT.χ x = cf.eta.1 x
  ringSpec_normalisedCharacter_eq : ∀ (j : Fin D.R.m) x, (chiD.mu0 (j.1 + 1)).χ x = (cf.mu0 j).1 x
  del_eq : ∀ s x, (chiD.del s).χ x = (cf.delAt (D.ntw.l s)).1 x
  iCq_embO : ∀ s (x : ↥D.LL0), twF.iCq s (chiD.embO s true x) = D.what₂.embLL (x : D.what₂.LL)
  embO_star : ∀ s (x y : ↥D.LL0), (y : D.what₂.LL) = star (x : D.what₂.LL) → chiD.embO s false x = chiD.embO s true y
  deltaRead : DeltaRead D cf

def RingPart.of {D : D7} {cf : CharFrame D} {Rw low Pq S hL eig θ} (B : SideB D cf Rw low Pq S hL eig θ) : RingPart D cf low :=
  ⟨B.twF, B.tw, B.chiD, B.chi, B.eta_eq, B.ringSpec_normalisedCharacter_eq, B.del_eq, B.iCq_embO, B.embO_star, B.deltaRead⟩

def PsiStd (D : D7) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) : Prop :=
  ∀ u : Formalism.IndefR.NX.U D.nd, embLL0 D ((psiUOf D.nd (NX.xiRed D) θ u : (↥D.LL0)ˣ) : ↥D.LL0) =
    ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (Complex.exp (2 * Real.pi * Complex.I / (D.host.g kv.1 : ℂ)) ^ (NX.xiRed D kv * NX.supSum D.R.r
      (((u : G0g D.nd) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))).val)⁻¹

def PsiLaw (D : D7) (S : RatDat D.ntw) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) : Prop :=
  ∀ i b (u : G0g D.nd) (hu : u ∈ D.nexp.U) (hu' : u ∈ Formalism.IndefR.NX.U D.nd),
    ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      readLL0 S i b ((psiUOf D.nd (NX.xiRed D) θ ⟨u, hu'⟩ : (↥D.LL0)ˣ) : ↥D.LL0)

def SameUnits {D D' : D7} (c : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ)
    (c' : ∀ (i : D'.ntw.Tw) (_b : Bool) (_P : PlE D'.host), (D'.ntw.O i)ˣ) : Prop :=
  ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw) (b : Bool) (P : PlE D.host) (P' : PlE D'.host), HEq i i' → HEq P P' → HEq (c' i' b P') (c i b P)

def RowEig (D : D7) (S : RatDat D.ntw) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (c : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ) (rowS : ∀ i, D.ntw.Sig i → D.what₂.FT) : Prop :=
  ∀ i (s : D.ntw.Sig i) k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ D.ntw.S0 i →
    algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (D.ntw.hEig i s k P) =
      algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (c i (D.ntw.side i s) P) ^ k *
        (show FractionRing (D.ntw.O i) from readLL0 S i (D.ntw.side i s) (eig (D.ntw.jS i s) (rowS i s) k P))



set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem sigSpan_copy {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyAll D D' ι e)
    (hs : D.ntw.SigSpan) : D'.ntw.SigSpan := by
  have transfer {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
      {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
      (g : GlobalTheory.TwistChoice.SameGalois N N')
      (t : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients X X')
      (b : HEq X.B X'.B) (ab : HEq X.acgB X'.acgB)
      (mb : HEq X.modB X'.modB) (hk : HEq X.hk X'.hk)
      (s : X.SigSpan) : X'.SigSpan := by
    obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := g
    obtain ⟨xcc, xTw, xl, xO0, xcrO0, xalgO0, xtopO0, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, xS0, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := t
    cases D; cases D'
    dsimp only at a1 a2 a3
    subst a1; subst a2; subst a3
    cases N; cases N'
    dsimp only at nOm ninstOm nalgOm nplOm nPlG
    subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
    cases X; cases X'
    dsimp only at xcc xTw xl xO0 xcrO0 xalgO0 xtopO0 xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS xS0 xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth b ab mb hk
    subst xcc; subst xTw; subst xl; subst xO0; subst xcrO0; subst xalgO0; subst xtopO0; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst xS0; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
    subst b; subst ab; subst mb; subst hk
    exact s
  exact transfer h.cp.gal h.cp.set h.cp.B h.cp.acgB h.cp.modB h.cp.hk hs

end GlobalTheory.HeightCounting.SideCopy

end
