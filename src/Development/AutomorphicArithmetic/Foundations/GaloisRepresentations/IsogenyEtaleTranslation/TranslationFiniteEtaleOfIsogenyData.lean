module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.FixedPointsIntBaseHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PScalEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PWitScal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PPowFEt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PTrScal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PEtCancel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PDescEt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PDescFin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PTrFEt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PAlFEt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PLegOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.TrEqRe
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PTanIso
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PDimUniq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PCxFinOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PBridge

@[expose] public section

namespace UpperTheory.Gal.FixZ

theorem translation_finite_etale_of_isogeny_data (h1 : G3.SysOf) (h2 : G3.RelComp) (h3 : G3.WitUniq) (h4 : G3.IsogFEt) (h5 : G3.PowSm) : TrFEt :=
  trFEt_of h5 (scalEx_of h1) (trScal_of h3 h4 (witScal_of h2) powFEt_of) etCancel_of descEt_of descFin_of

theorem tower_fixed_points_of_isogeny_data (h1 : G3.SysOf) (h2 : G3.RelComp) (h3 : G3.WitUniq) (h4 : G3.IsogFEt) (h5 : G3.PowSm) : LocalSmoothExtension.FixK :=
  bridge_of (translation_finite_etale_of_isogeny_data h1 h2 h3 h4 h5) (alFEt_of h4 powFEt_of) legOf_of wtEq_of tanIso_of dimUniq_of cxFinOf_of
    W2.fixedPoints_int_base_holds W2.FixZ_holds

end UpperTheory.Gal.FixZ
