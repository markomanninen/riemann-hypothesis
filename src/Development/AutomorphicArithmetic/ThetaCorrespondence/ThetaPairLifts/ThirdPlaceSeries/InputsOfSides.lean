module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT4OfRationalRows
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalSide
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisInputs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TwInputs
theorem exists_inputs_of_hkSup_galHodge : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator →
    ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), ∀ G : _root_.GlobalTheory.TwInputs.GalSideAlt D,
      (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → XiBdd Y.Z.rd →
      (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j) → _root_.UpperTheory.GalS.GalHodgeN D G.wd →
      (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange) →
      ∃ N0, Inputs D E N0 := by
  intro hCh hArt hTor D X E Y G hRat hBdd hSup hHodge hRoots
  obtain ⟨a1, a2, a8, good, sig, ⟨N0, a9⟩, a10, hyp⟩ := _root_.GlobalTheory.TwGalInputs.galois_inputs_alt hCh hArt hTor D G hHodge
  have hUnit : ∀ i b P, P ∉ D.ntw.S0 i → ∃ u : (D.ntw.O i)ˣ, Y.H.cHk i b 1 P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u := by
    intro i b P hP
    obtain ⟨σ, -, hσ⟩ := GlobalTheory.TripleGal.exists_mem_Dec_isFrob D P (D.nd.plOm.1 P) (D.nd.plOm.2 P)
    exact ⟨Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom
      (if b then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹), Y.del i b P hP σ hσ⟩
  have hKs : ∀ j, 1 ≤ j → j ≤ D.R.m → (Y.S.A j).IsKsForm := by
    intro j h1 h2
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
    exact GlobalTheory.isKsForm_of_formsIso _ _ (Y.YS.fi ⟨n, h2⟩) (X.integral ⟨n, h2⟩).1
  have hL : Laws Y.Z.good Y.Z.rd := by
    refine ⟨fun i j b => ?_, fun i j b => ?_, fun i j b => ?_, fun i hi j b => Y.Z.rat (hRat i hi j b)⟩
    · exact GlobalTheory.SeriesTie.realRd_faithful D _ _ _ _ _ _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b _
        (Y.Z.scalar i j b).ne X.unif X.char.models.HW (Y.Z.vec j)
        (hKs _ (Nat.le_add_left _ _) j.2)
    · exact GlobalTheory.SeriesTie.actRead_realRd D _ _ _ _ _ _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b _
        Y.Z.pin X.unif X.char.models.HW
    · exact Y.Z.heckeRead (GlobalTheory.SeriesTie.HkRat.ratHecke_realRd D _ _ _ _ _ _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b _
        Y.Z.pin (X.char.lev.mu0 j) (GlobalTheory.SplitOffS0.main Y.Z.good i _ (Y.Sb i)) Y.H.hL
        (Y.H.hs _ (Nat.le_add_left _ _) j.2) Y.reads)
  have hLevel : Y.Z.ρ.LevelOf D.nexp :=
    ⟨fun i j b g => (Y.Z.tie i j b).U_eq g, fun i j b u hu => (Y.Z.tie i j b).psiU_eq u hu⟩
  have hXi : XiType Y.Z.rd := GlobalTheory.XiTypeProof.xiType D Y.Z.ρ Y.Z.good Y.Z.rd hL.faithful hL.act hLevel
  have hSupLaws : SupG D ∧ SupFull D ∧ SupHk D ∧ CommG D ∧ HkComm D := by
    obtain ⟨h1, h2⟩ := GlobalTheory.T.twistedFormSupLattice_full_groupStable_of_eq_rational D X.Γ X.Pl0 X.I0 X.T X.A3 X.core.Q.c.F X.R X.cG Y.S Y.YS Y.sup X.integral
    obtain ⟨h3, h4⟩ := GlobalTheory.HkSupComm.supHk_commG D X.Γ X.Pl0 X.I0 X.T X.A3 X.core X.R X.cG Y.S Y.YS Y.H Y.sup X.char.lev X.char.allPl
      (fun i => (X.integral i).2.1) hSup Y.reads (fun i b P h _ => hUnit i b P h)
    have hC : GlobalTheory.ExportPin.Model.Covered X.R := GlobalTheory.ExportPin.Model.covered_of_allPlaces X.R X.char.lev X.char.allPl
    have hComm : HkComm D := by
      exact hkComm_of_family X.R X.cG Y.S Y.YS Y.H.hL Y.H.hs Y.H.cHk Y.H.hkEq fun i j a b k P k' P' hk hk' =>
        family_comm X.R X.cG Y.S Y.YS X.char.lev X.char.fam X.char.models.HW
          (fun n => GlobalTheory.ExportPin.Model.j_injective X.R X.unif n _) hC Y.H.hL
          (fun i n k P hk α R ha hR => ⟨_, fun x => Y.reads n k P hk.2.2.1 (hC i P hk.2.2.2 hk.2.2.1) hk.2.1 α R ha hR x⟩)
          i j a b k P k' P' hk hk'
    exact ⟨h1, h2, h3, h4, hComm⟩
  obtain ⟨supG, supFull, supHk, commG, comm⟩ := hSupLaws
  have hSS : HkSS D := by
    have hX : Formalism.IndefR.NX.NExpHeckeRowX X.R X.cG Y.S Y.YS Y.H (fun j => Formalism.IndefR.NX.goodProjW Y.S j D.nexp.eLL0) :=
      ⟨fun i k P hs ho _ _ hk α R hα hR x _ => Y.reads i k P hs ho hk α R hα hR x⟩
    exact GlobalTheory.GoodSpan.hkSS_of_rows_guarded X.R X.F X.cG Y.S Y.YS Y.H commG comm supFull hX X.char X.unif X.integral
      (fun i P P' hP hc => Y.Z.good.goodSetup_badPlaces_conj i P hP P' hc) (fun i => Y.Z.good.goodSetup_placesOverTwo_subset i) Y.Sb
      (fun i _ j hj b k P hk x => Y.hk_emb i j b k P x (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2 hk)
      Y.B_range Y.hk_split
  exact ⟨N0,
    { a1 := a1
      a2 := a2
      a8 := a8
      good := good
      sig := sig
      a9 := a9
      a10 := a10
      univChar := Y.Z.univ
      off := Y.off
      rel := GlobalTheory.T.universalTwistedSeriesDistribution_of_compatibility D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.full hL
      l3 := GlobalTheory.SeriesTie.thetaLatticeCondition_of_fullSeriesComparison D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.full hL
      t4 := GlobalTheory.T.admT4_of_roots_in_field D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.full hRoots E
      type := GlobalTheory.ExportType.typeKept_of_fullTie D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.full hL.act E
      univ := univSup_of_xi D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.full hL hXi hBdd E
      supG := supG
      supFull := supFull
      supHk := supHk
      commG := commG
      comm := comm
      ss := hSS
      hyp := hyp }⟩
end GlobalTheory.TwInputs
end
