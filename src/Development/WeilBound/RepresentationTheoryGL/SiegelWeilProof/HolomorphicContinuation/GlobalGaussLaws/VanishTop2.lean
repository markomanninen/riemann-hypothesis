module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.VanishTop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GenCoreTop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.NullIff
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.LcOf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Wtc
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.StrongEisensteinBounds.Strong
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaAutomorphicOfConvergenceStatement

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem absThm : AbsThm := AbsSt.absThm_of lv (cyc_of fft) (lc_of fft) nullIff

theorem top2 (hLF : LocFact) (hAA : AwayAct) (hLi : LocInst) (hTA : PositivityTheory.PfSWUS.ThetaAuto) (hLC : LieComm)
    (hDO : DerivOne) (hId : GIdil) (hC : PositivityTheory.PfSWUS.CoefND) :
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, GlobalTheory.Cont.HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (GlobalTheory.StdUnn.s0 V n) (GlobalTheory.StdUnn.thetaInt ω ν Φ g) :=
  top absThm hLF hAA hLi hTA hLC hDO hId PositivityTheory.Rg.SwEis.Hd.eisStrong hC wtc

theorem top3 (hLF : LocFact) (hAA : AwayAct) (hLi : LocInst) (hLC : LieComm) (hDO : DerivOne) (hId : GIdil)
    (hC : PositivityTheory.PfSWUS.CoefND) :
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, GlobalTheory.Cont.HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (GlobalTheory.StdUnn.s0 V n) (GlobalTheory.StdUnn.thetaInt ω ν Φ g) :=
  top2 hLF hAA hLi (GlobalTheory.T.theta_automorphic_of_convergence wtc) hLC hDO hId hC

end PositivityTheory.Rg.Sw.Glob
