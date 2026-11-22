module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ConjPlace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PhiDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PpSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CharpolySmulUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CpCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CpRedProdScaleRoots
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PhiUnr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ResidueEqOneOfMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CharpolyGspConjInvScaled
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.SpacePsiMul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ResLeMemDec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PhiFlag

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem chi_map {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G] (E : W.GDet n A G) (f : A →+* A') (g : G) :
    (E.map f).chi (MonoidAlgebra.single g 1) = (E.chi (MonoidAlgebra.single g 1)).map f := by
  have h (y : MonoidAlgebra A G) :
      (E.map f).chi (MonoidAlgebra.mapRingHom G f y) = (E.chi y).map f := by
    have e : MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C (MonoidAlgebra.mapRingHom G f y) =
        MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y) := by
      rw [map_sub, MonoidAlgebra.mapRingHom_single, Polynomial.coe_mapRingHom, Polynomial.map_X,
        ← RingHom.comp_apply, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp,
        ← MonoidAlgebra.mapRingHom_comp, Polynomial.mapRingHom_comp_C]
    show (E.map f).D A'[X] _ = _
    rw [e]
    let : Algebra A A'[X] := ((algebraMap A' A'[X]).comp f).toAlgebra
    exact E.nat A[X] A'[X] { Polynomial.mapRingHom f with
      commutes' := fun a => by
        change (Polynomial.mapRingHom f) (C a) = C (f a)
        simp } _
  simpa only [MonoidAlgebra.mapRingHom_single, map_one] using h (MonoidAlgebra.single g 1)
