module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
public import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
public import Formalism.LocalToGlobal.InertKernelTheory.StatementJets
public import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JInvNormLeOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodOrdinaryModelAtTwoCmLatticeSevenModEight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocJetsAll
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntSExpMulTranslate
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceExtendsToIso

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

namespace GlobalTheory.ThLoc

theorem inputs_of_algT (hT : Formalism.L2.KerInert.AlgTAll) : Inputs := by
  exact
    { jInt := cm1
      modelTwo := goodOrdinaryModelAtTwo_cmLattice_seven_mod_eight
      jetsOdd := locJets_all.1
      jetsTwo := locJets_all.2.1
      jetsThree := thetaZJetsThree
      shape := locJets_all.2.2
      algT := hT
      lamExt := place_extends_to_iso }

end GlobalTheory.ThLoc
