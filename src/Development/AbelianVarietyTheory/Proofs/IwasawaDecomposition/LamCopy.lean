module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
open Formalism.L2.DIV Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HeightCounting.SideCopy.LamCopy
open GlobalTheory.Mem.R3.Tr


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem lam_copy : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}, CopyAll D D' ι e → ∀ {cf : CharFrame D} {cf' : CharFrame D'}, SameFrame cf cf' → (∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw Z) → ∃ Z : GlobalTheory.LamTie.LamDat D', Z.Ok ∧ Z.Teich ∧ Z.C = cf' ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D' ∧ GlobalTheory.LamTie.IsLamTieFull D'.ntw Z := by
  rintro D D' ι e h cf cf' ⟨f1, f2, f3, f4⟩ ⟨⟨C, q, w0, c, chi⟩, hOk, hT, rfl, hq, hF⟩
  have he : ∀ x : ↥D'.LL0, D'.what₂.embLL (x : D'.what₂.LL) = D.what₂.embLL (e x : D.what₂.LL) := fun x => (h.cp.embLL0_eq x).symm
  have nOm := h.cp.gal.Om
  have ninstOm := h.cp.gal.instOm
  have nalgOm := h.cp.gal.algOm
  have nplOm := h.cp.gal.plOm
  have nPlG := h.cp.gal.PlG
  have hR := h.cp.gal.R
  have hhost := h.cp.gal.host
  have hTau := h.cp.Tau
  have heTau := h.cp.eTau
  have hhc := h.cp.hc
  have hinW1 := h.cp.inW1
  have hemb0 := h.cp.emb0
  have hTw := h.cp.set.Tw
  obtain ⟨xcc, _, _, _, _, xalgO0, xtopO0, _, _, _, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, _, xhEig, _, _, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h.cp.set
  have hjL := h.jL
  have hs2 := h.s2
  have hlamG := h.lamG
  have hXv := h.Xv
  have hqs := h.qs
  have hl := h.cp.set.l
  have hO0 := h.cp.set.O0
  have hcrO0 := h.cp.set.crO0
  have hab := h.cp.set.abelian₂
  have hsideL := h.cp.set.sideL
  have hO := h.cp.set.O
  have hcrO := h.cp.set.crO
  have halgO := h.cp.set.algO
  have hS0 := h.cp.set.S0
  cases D; cases D'
  dsimp only at hR hhost
  subst hR; subst hhost
  rename Rows.Data _ => r1; cases r1; rename Rows.Data _ => r2; cases r2
  dsimp only at hTau
  subst hTau
  dsimp only at heTau hhc
  subst heTau; subst hhc
  rename NData _ _ _ => nd1; cases nd1
  rename NData _ _ _ => nd2; cases nd2
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  rename NTw _ _ _ _ _ => n1; cases n1
  rename NTw _ _ _ _ _ => n2; cases n2
  dsimp only at xcc
  subst xcc
  dsimp only at hTw hl hO0 hcrO0 hab hsideL hO hcrO halgO hS0
  subst hTw; subst hl; subst hO0; subst hcrO0; subst hab; subst hsideL; subst hO; subst hcrO; subst hS0
  dsimp only at xalgO0 xtopO0 xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS xhEig xRCG xgrpRCG xfinRCG xart xth hjL hs2 hlamG hXv hqs halgO
  subst xalgO0; subst xtopO0; subst halgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst xhEig; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  subst hjL; subst hs2; subst hlamG; subst hXv; subst hqs
  cases C; cases cf'  
  dsimp only at f1 f2 f3 f4
  subst f1; subst f2; subst f3; subst f4
  refine ⟨⟨_, q, w0, c, chi⟩, ⟨(by with_unfolding_all exact (hOk.places :)), (by with_unfolding_all exact (hOk.aux :)), (by with_unfolding_all exact (hOk.big :))⟩, (by with_unfolding_all exact (hT :)), rfl, (by with_unfolding_all exact (hq :)), fun i hi => ?_⟩
  obtain ⟨t0, j, t1, t2⟩ := hF i ((hinW1 i i HEq.rfl).2 hi)
  refine ⟨(by with_unfolding_all exact (t0 :)), (by with_unfolding_all exact (j :)), fun x => ?_, (by with_unfolding_all exact (t2 :))⟩
  exact (congrArg j (he x)).trans ((t1 (e x)).trans ((by with_unfolding_all exact ((congrArg (GlobalTheory.ToricDenom.toBar _ i) (eq_of_heq (hemb0 i i HEq.rfl x))) :))))

end GlobalTheory.HeightCounting.SideCopy.LamCopy
