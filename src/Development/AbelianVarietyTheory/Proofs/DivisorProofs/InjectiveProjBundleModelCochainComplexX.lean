module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotDComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SxProdIsoHomSnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSheafProjBundleCochainPresheafEtaleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NaturalSectionsLinearExtension

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC
open CupSpec

variable {R : Type} [CommRing R]

section Build
variable (q N : ℕ) (I : Cx R) (n : ℤ) {B : Shv R}
  (χ : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ V : Scheme.{0}, Sx (fibQ q N) p V → Sec B V →ₗ[ULift.{1} R] Sec (I.X s) V)
  (hχ : ∀ p s h (V W : Scheme.{0}) (w : W ⟶ V) (x : Sx (fibQ q N) p V) (b : Sec B V),
      Sec.res w (χ p s h V x b) = χ p s h W (x.res w) (Sec.res w b))
include hχ in
theorem buildC_exists (U : Scheme.{0}) (b : Sec B U) :
    ∃ α : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n, ∀ p s h W y,
      _root_.GlobalTheory.EtC.ev (R := R) α p s h W y =
        χ p s h W (y.map prod.snd) (Sec.res (show W ⟶ U from y.map prod.fst) b) := by
  let E : Spc := sch.obj U ⨯ fibQ q N
  let a (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (W : Scheme.{0}) (y : Sx E p W) :=
    χ p s h W (y.map prod.snd) (Sec.res (show W ⟶ U from y.map prod.fst) b)
  have ha (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (V W : Scheme.{0})
      (g : V ⟶ W) (y : Sx E p W) : Sec.res g (a p s h W y) = a p s h V (y.res g) := by
    dsimp only [a]
    erw [hχ, secRes_res, sxMap_res, sxMap_res]
    rfl
  have components (i j : ℤ) (hij : i + n = j) :
      ∃ φ : ((chains R).obj E).X i ⟶ I.X j, ∀ (p : ℕ) (hp : i = -(p : ℤ)) W y,
        Sec.map ((chainsXIso R E p).inv ≫ eqToHom (congrArg ((chains R).obj E).X hp.symm) ≫ φ)
          (freeGen R _ W y) = a p j (hp ▸ hij) W y := by
    by_cases hi : i ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
      obtain ⟨φ, hφ⟩ := free_exists (R := R) _ _ (a k j hij) (ha k j hij)
      refine ⟨(chainsXIso R E k).hom ≫ φ, fun p hp W y => ?_⟩
      obtain rfl : k = p := by omega
      rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
      exact hφ W y
    · exact ⟨0, fun p hp => by omega⟩
  choose φ hφ using components
  refine ⟨Cochain.mk φ, fun p s h W y => ?_⟩
  have he := hφ _ _ h p rfl W y
  rw [eqToHom_refl, Category.id_comp] at he
  exact he

def cochainOfSection (U : Scheme.{0}) (b : Sec B U) : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n :=
  (buildC_exists q N I n χ hχ U b).choose

theorem buildC_ev (U : Scheme.{0}) (b : Sec B U) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (W : Scheme.{0})
    (y : Sx (sch.obj U ⨯ fibQ q N) p W) :
    _root_.GlobalTheory.EtC.ev (R := R) (cochainOfSection q N I n χ hχ U b) p s h W y =
      χ p s h W (y.map prod.snd) (Sec.res (show W ⟶ U from y.map prod.fst) b) :=
  (buildC_exists q N I n χ hχ U b).choose_spec p s h W y

include χ hχ in
def buildMor : B.obj ⟶ cotPre R q N I n := by
  have evExt {E : Spc} (α β : Cochain ((chains R).obj E) I n)
      (he : ∀ p s h W y, ev (R := R) α p s h W y = ev (R := R) β p s h W y) : α = β := by
    ext i s h : 1
    by_cases hi : i ≤ 0
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R E p).inv]
      exact free_ext _ _ (fun W y => he p s h W y)
    · exact (isZero_chains E i (by omega)).eq_of_src _ _
  have evAdd {E : Spc} (α β : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
      (h : -(p : ℤ) + n = s) (W : Scheme.{0}) (y : Sx E p W) :
      ev (R := R) (α + β) p s h W y = ev (R := R) α p s h W y + ev (R := R) β p s h W y := by
    simp [ev, Cochain.add_v]
  have evSmul {E : Spc} (r : ULift.{1} R) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
      (h : -(p : ℤ) + n = s) (W : Scheme.{0}) (y : Sx E p W) :
      ev (R := R) (r • α) p s h W y = r • ev (R := R) α p s h W y := by
    unfold ev
    rw [Cochain.smul_v, Linear.comp_smul]
    rfl
  refine
    { app := fun U => ModuleCat.ofHom
        { toFun := cochainOfSection q N I n χ hχ U.unop
          map_add' := fun b b' => evExt _ _ (fun p s h W y => by
            simp only [evAdd, buildC_ev, Sec.res, map_add])
          map_smul' := fun r b => evExt _ _ (fun p s h W y => by
            simp only [RingHom.id_apply, evSmul, buildC_ev, Sec.res, map_smul]) }
      naturality := ?_ }
  intro U U' g
  have evPull {E E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
      (h : -(p : ℤ) + n = s) (W : Scheme.{0}) (y : Sx E' p W) :
      ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h W y =
        ev (R := R) α p s h W (y.map f) := by
    unfold ev
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chains_map, Category.assoc]
    change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (Sec.map ((free R).map _) (freeGen R _ W y)) = _
    rw [freeGen_map]
    rfl
  ext b : 2
  refine evExt _ _ (fun p s h W y => ?_)
  change ev (R := R) (cochainOfSection q N I n χ hχ U'.unop (Sec.res g.unop b)) p s h W y =
    ev (R := R) (((cotPre R q N I n).map g.unop.op).hom (cochainOfSection q N I n χ hχ U.unop b)) p s h W y
  have e2 := evPull (prod.map (sch.map g.unop) (𝟙 (fibQ q N)))
    (cochainOfSection q N I n χ hχ U.unop b) p s h W y
  refine Eq.trans ?_ e2.symm
  let f := prod.map (sch.map g.unop) (𝟙 (fibQ q N))
  have hsnd : (y.map f).map prod.snd = y.map prod.snd := by
    rw [← sxMap_comp, prod.map_snd, Category.comp_id]
  have hfst : (show W ⟶ U.unop from (y.map f).map prod.fst) =
      (show W ⟶ U'.unop from y.map prod.fst) ≫ g.unop := by
    change (y.map f).map prod.fst = schSx ((show W ⟶ U'.unop from y.map prod.fst) ≫ g.unop) p
    rw [← sxMap_comp, prod.map_fst, sxMap_comp]
    exact schSx_map (show W ⟶ U'.unop from y.map prod.fst) g.unop p
  erw [buildC_ev, buildC_ev, secRes_res, hsnd, hfst]

end Build

theorem injective_cotSheaf (q N : ℕ) (I : Cx R) (hI : ∀ m, Injective (I.X m)) (n : ℤ)
    (hS : Presheaf.IsSheaf Scheme.etaleTopology.{0} (cotPre R q N I n)) :
    Injective (⟨cotPre R q N I n, hS⟩ : Shv R) := by
  constructor
  intro A B g f hf
  let eval {E : Spc} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (V : Scheme.{0}) (x : Sx E p V) :
      Cochain ((chains R).obj E) I n →ₗ[ULift.{1} R] Sec (I.X s) V :=
    { toFun := fun α => ev (R := R) α p s h V x
      map_add' := fun α β => by simp [ev, Cochain.add_v]
      map_smul' := fun r α => by
        unfold ev
        rw [Cochain.smul_v, Linear.comp_smul]
        rfl }
  have evRes {E : Spc} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
      {V W : Scheme.{0}} (w : W ⟶ V) (x : Sx E p V) :
      Sec.res w (ev (R := R) α p s h V x) = ev (R := R) α p s h W (x.res w) := by
    change Sec.res w (Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (freeGen R _ V x)) = _
    rw [map_res, freeGen_res]
    rfl
  have evPull {E E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
      (h : -(p : ℤ) + n = s) (W : Scheme.{0}) (y : Sx E' p W) :
      ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h W y =
        ev (R := R) α p s h W (y.map f) := by
    unfold ev
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chains_map, Category.assoc]
    change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (Sec.map ((free R).map _) (freeGen R _ W y)) = _
    rw [freeGen_map]
    rfl
  let ψ : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ V : Scheme.{0}, Sx (fibQ q N) p V → Sec A V →ₗ[ULift.{1} R] Sec (I.X s) V :=
    fun p s h V x => (eval p s h V (sxPair (schSx (𝟙 V) p) x)).comp (g.hom.app (op V)).hom
  have hψ : ∀ p s h (V W : Scheme.{0}) (w : W ⟶ V) (x : Sx (fibQ q N) p V) (a : Sec A V),
      Sec.res w (ψ p s h V x a) = ψ p s h W (x.res w) (Sec.res w a) := by
    intro p s h V W w x a
    have hn : (g.hom.app (op W)).hom (Sec.res w a) = ((cotPre R q N I n).map w.op).hom ((g.hom.app (op V)).hom a) :=
      ConcreteCategory.congr_hom (g.hom.naturality w.op) a
    refine (evRes (E := sch.obj V ⨯ fibQ q N)
      ((g.hom.app (op V)).hom a) p s h w _).trans ?_
    refine Eq.trans ?_ (congrArg (fun c => _root_.GlobalTheory.EtC.ev (R := R) (E := sch.obj W ⨯ fibQ q N) (I := I) c p s h W
      (sxPair (schSx (𝟙 W) p) (x.res w))) hn).symm
    have e2 := evPull (prod.map (sch.map w) (𝟙 (fibQ q N))) ((g.hom.app (op V)).hom a) p s h W
      (sxPair (schSx (𝟙 W) p) (x.res w))
    refine Eq.trans ?_ e2.symm
    rw [sxPair_res, sxPair_map]
    congr 2
  have hχ := fun p s h => GlobalTheory.T.natural_sections_linear_extension R ((fibQ q N).obj (op (SimplexCategory.mk p))) (I.X s) (hI s) f hf (ψ p s h) (hψ p s h)
  choose χ hχn hχf using hχ
  refine ⟨⟨buildMor q N I n χ hχn⟩, ?_⟩
  ext U : 4
  refine LinearMap.ext fun a => ?_
  change cochainOfSection q N I n χ hχn U.unop (Sec.map f a) = (g.hom.app U).hom a
  have evExt {E : Spc} (α β : Cochain ((chains R).obj E) I n)
      (he : ∀ p s h W y, ev (R := R) α p s h W y = ev (R := R) β p s h W y) : α = β := by
    ext i s h : 1
    by_cases hi : i ≤ 0
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R E p).inv]
      exact free_ext _ _ (fun W y => he p s h W y)
    · exact (isZero_chains E i (by omega)).eq_of_src _ _
  refine evExt _ _ (fun p s h W y => ?_)
  refine (buildC_ev q N I n χ hχn U.unop (Sec.map f a) p s h W y).trans ?_
  refine (congrArg (χ p s h W (y.map prod.snd))
    (_root_.GlobalTheory.EtC.CupSpec.map_res f (show W ⟶ U.unop from y.map prod.fst) a)).trans ?_
  refine (hχf p s h W _ _).trans ?_
  have hn := ConcreteCategory.congr_hom (g.hom.naturality (show W ⟶ U.unop from y.map prod.fst).op) a
  refine (congrArg (fun c => _root_.GlobalTheory.EtC.ev (R := R) (E := sch.obj W ⨯ fibQ q N) (I := I) c p s h W
    (sxPair (schSx (𝟙 W) p) (y.map prod.snd))) hn).trans ?_
  refine (evPull (prod.map (sch.map (show W ⟶ U.unop from y.map prod.fst)) (𝟙 (fibQ q N)))
    ((g.hom.app U).hom a) p s h W _).trans ?_
  congr 1
  rw [sxPair_map]
  exact sxPair_eta y

theorem Jcx_X_injective : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R), (∀ n, CategoryTheory.Injective (I.X n)) →
    ∀ n, CategoryTheory.Injective ((Jcx R q N I).X n) := by
  intro R _ q N I hI n
  have hS := GlobalTheory.T.isSheaf_projBundleCochainPresheaf_etale R q N I n
  exact Injective.of_iso (sheafificationIso (⟨cotPre R q N I n, hS⟩ : Shv R)) (injective_cotSheaf q N I hI n hS)

end GlobalTheory.EtC

end
