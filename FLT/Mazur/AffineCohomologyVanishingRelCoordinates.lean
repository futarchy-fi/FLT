/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizationCechCompare
public import FLT.Mazur.LocalizationCechIso

/-!
# Relative localization-Cech coordinates

Sections on intersections inside a principal open are computed after localizing
the base ring and module. The comparisons use actual restriction maps and commute
with tuple reindexing and the alternating differentials.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FLT.Mazur.AffineCohomologyVanishingRelCoordinates

open TildePrincipalOpen LocalizationCech LocalizationCechCompare

/-- Principal sections have their canonical localization structure over any bundled ring. -/
lemma sections_isLocalized {A : CommRingCat.{u}} (N : ModuleCat.{u} A) (g : A) :
    IsLocalizedModule (.powers g) (toSections N g) := inferInstance

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (r : R)

/-- The module of sections on the fixed principal open, over its localized ring. -/
abbrev localizedModule : ModuleCat (CommRingCat.of (Localization.Away r)) :=
  ModuleCat.of (Localization.Away r) (sections M r)

/-- These coefficients are the usual localized module. -/
def localizedModuleEquiv :
    localizedModule M r ≃ₗ[Localization.Away r] LocalizedModule (.powers r) M :=
  sectionsEquiv M r

/-- Restriction from `D(r)` to `D(rg)` localizes its section module at `g`. -/
instance restriction_isLocalized (g : R) :
    IsLocalizedModule (.powers g) (restriction M r g) := by
  have h : (restriction M r g).comp (toSections M r) = toSections M (r * g) := rfl
  have : IsLocalizedModule.Away (g * r)
      ((restriction M r g).comp (toSections M r)) := by
    rw [h, mul_comm g r]
    infer_instance
  exact away_in_stages g r (toSections M r) (restriction M r g)

/-- Sections on the localized spectrum, regarded as modules over the original ring. -/
abbrev localizedSections (g : R) : ModuleCat R :=
  (ModuleCat.restrictScalars (algebraMap R (Localization.Away r))).obj
    (sections (localizedModule M r) (algebraMap R (Localization.Away r) g))

/-- The original ring acts on localized-spectrum sections through its localization. -/
local instance localizedSectionModule
    (U : Opens (PrimeSpectrum (Localization.Away r))) :
    Module R ((modulesSpecToSheaf.obj (tilde (localizedModule M r))).presheaf.obj (op U)) :=
  Module.compHom _ (algebraMap R (Localization.Away r))

local instance localizedSectionScalarTower
    (U : Opens (PrimeSpectrum (Localization.Away r))) :
    IsScalarTower R (Localization.Away r)
      ((modulesSpecToSheaf.obj (tilde (localizedModule M r))).presheaf.obj (op U)) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Localization from the coefficient module on `D(r)`, with original scalars. -/
abbrev toLocalizedSections (g : R) : sections M r →ₗ[R] localizedSections M r g :=
  (toSections (localizedModule M r) (algebraMap R (Localization.Away r) g)).restrictScalars R

instance toLocalizedSections_isLocalized (g : R) :
    IsLocalizedModule (.powers g) (toLocalizedSections M r g) := by
  let localizedSectionsTower :
      IsScalarTower R (Localization.Away r) (localizedSections M r g) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have localizedSectionsAway :
      IsLocalizedModule (.powers (algebraMap R (Localization.Away r) g))
        (toSections (localizedModule M r) (algebraMap R (Localization.Away r) g)) :=
    sections_isLocalized (localizedModule M r) (algebraMap R (Localization.Away r) g)
  exact IsLocalizedModule.restrictScalars_powers (R := R) (A := Localization.Away r) g
    (toSections (localizedModule M r) (algebraMap R (Localization.Away r) g))

/-- Localization in stages identifies sections on the two spectra. -/
def sectionEquiv (g : R) : localizedSections M r g ≃ₗ[R] sections M (r * g) :=
  IsLocalizedModule.linearEquiv (.powers g)
    (toLocalizedSections M r g) (restriction M r g)

@[simp]
lemma sectionEquiv_toSections (g : R) (x : sections M r) :
    sectionEquiv M r g (toLocalizedSections M r g x) = restriction M r g x :=
  IsLocalizedModule.linearEquiv_apply _ _ _ _

/-- The same stage comparison with an explicitly identified localized denominator. -/
def sectionEquivAt (g : R) (g' : Localization.Away r)
    (hg : g' = algebraMap R (Localization.Away r) g) :
    (ModuleCat.restrictScalars (algebraMap R (Localization.Away r))).obj
      (sections (localizedModule M r) g') ≃ₗ[R] sections M (r * g) :=
  hg ▸ sectionEquiv M r g

@[simp]
lemma sectionEquivAt_toSections (g : R) (g' : Localization.Away r)
    (hg : g' = algebraMap R (Localization.Away r) g) (x : sections M r) :
    sectionEquivAt M r g g' hg (toSections (localizedModule M r) g' x) =
      restriction M r g x := by
  subst g'
  exact sectionEquiv_toSections M r g x

/-- The stage comparison commutes with restriction between principal opens. -/
lemma sectionEquivAt_restrict (g h : R) (g' h' : Localization.Away r)
    (hg : g' = algebraMap R (Localization.Away r) g)
    (hh : h' = algebraMap R (Localization.Away r) h)
    (e : PrimeSpectrum.basicOpen h ≤ PrimeSpectrum.basicOpen g)
    (e' : PrimeSpectrum.basicOpen h' ≤ PrimeSpectrum.basicOpen g')
    (x : sections (localizedModule M r) g') :
    sectionEquivAt M r h h' hh
        (((modulesSpecToSheaf.obj (tilde (localizedModule M r))).presheaf.map
          (homOfLE e').op).hom x) =
      ((modulesSpecToSheaf.obj (tilde M)).presheaf.map
        (homOfLE (show PrimeSpectrum.basicOpen (r * h) ≤
            PrimeSpectrum.basicOpen (r * g) by
          simpa only [PrimeSpectrum.basicOpen_mul] using inf_le_inf_left _ e)).op).hom
        (sectionEquivAt M r g g' hg x) := by
  subst g' h'
  let a : localizedSections M r g →ₗ[R] localizedSections M r h :=
    ((ModuleCat.restrictScalars (algebraMap R (Localization.Away r))).map
      ((modulesSpecToSheaf.obj (tilde (localizedModule M r))).presheaf.map
        (homOfLE e').op)).hom
  let b := ((modulesSpecToSheaf.obj (tilde M)).presheaf.map
    (homOfLE (show PrimeSpectrum.basicOpen (r * h) ≤ PrimeSpectrum.basicOpen (r * g) by
      simpa only [PrimeSpectrum.basicOpen_mul] using inf_le_inf_left _ e)).op).hom
  suffices he : (sectionEquiv M r h).toLinearMap.comp a =
      b.comp (sectionEquiv M r g).toLinearMap from DFunLike.congr_fun he x
  apply IsLocalizedModule.ext (.powers g) (toLocalizedSections M r g)
  · rintro ⟨_, n, rfl⟩
    rw [map_pow]
    exact ((tilde M).isUnit_algebraMap_end_of_le_basicOpen g
      ((PrimeSpectrum.basicOpen_mul_le_right r h).trans e)).pow n
  · ext y
    change sectionEquiv M r h (a (toLocalizedSections M r g y)) =
      b (sectionEquiv M r g (toLocalizedSections M r g y))
    have ha : a (toLocalizedSections M r g y) = toLocalizedSections M r h y :=
      congrArg (fun k ↦ k.hom y) (tilde.toOpen_res (localizedModule M r) _ _ (homOfLE e'))
    rw [ha, sectionEquiv_toSections, sectionEquiv_toSections]
    change ((modulesSpecToSheaf.obj (tilde M)).presheaf.map _).hom y =
      (((modulesSpecToSheaf.obj (tilde M)).presheaf.map _) ≫
        ((modulesSpecToSheaf.obj (tilde M)).presheaf.map _)).hom y
    rw [← Functor.map_comp]
    rfl

variable {ι : Type u} (f : ι → R)

/-- The image of the principal family in the localized ring. -/
abbrev localizedFamily : ι → CommRingCat.of (Localization.Away r) :=
  fun i ↦ algebraMap R (Localization.Away r) (f i)

set_option maxHeartbeats 800000 in
-- Comparing the two bundled scalar restrictions requires extra reduction.
/-- The term comparison over the localized base uses the actual stage equivalences. -/
def localizedTermEquiv (q : ℕ) :
    (ModuleCat.restrictScalars (algebraMap R (Localization.Away r))).obj
        (term (localizedFamily r f) (localizedModule M r) q) ≃ₗ[R]
      baseTerm f M r q :=
  LinearEquiv.piCongrRight fun s : Fin (q + 1) → ι ↦ sectionEquivAt M r (∏ j, f (s j))
    (∏ j, localizedFamily r f (s j))
    (map_prod (algebraMap R (Localization.Away r)) (fun j ↦ f (s j)) Finset.univ).symm

/-- Every reindexing map is preserved, in particular all Cech cofaces. -/
lemma localizedTermEquiv_reindex {p q : ℕ} (a : Fin (p + 1) → Fin (q + 1))
    (x : term (localizedFamily r f) (localizedModule M r) p) :
    localizedTermEquiv M r f q
        ((reindex (localizedFamily r f) (localizedModule M r) a).hom x) =
      (baseReindex f M r a).hom (localizedTermEquiv M r f p x) := by
  funext s
  exact sectionEquivAt_restrict M r _ _ _ _ _ _
    (intersection_le f a s) (intersection_le (localizedFamily r f) a s) (x (s ∘ a))

/-- A differential-compatible isomorphism over the original scalar ring. -/
def localizedTermIso (q : ℕ) :
    (ModuleCat.restrictScalars (algebraMap R (Localization.Away r))).obj
        (term (localizedFamily r f) (localizedModule M r) q) ≅ baseTerm f M r q :=
  (localizedTermEquiv M r f q).toModuleIso

lemma localizedTermIso_differential (q : ℕ) :
    (ModuleCat.restrictScalars (algebraMap R (Localization.Away r))).map
        ((complex (localizedFamily r f) (localizedModule M r)).d q (q + 1)) ≫
        (localizedTermIso M r f (q + 1)).hom =
      (localizedTermIso M r f q).hom ≫ (baseComplex f M r).d q (q + 1) := by
  rw [differential, baseDifferential]
  simp only [Functor.map_sum, Functor.map_zsmul, Preadditive.sum_comp,
    Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply ModuleCat.hom_ext
  exact LinearMap.ext (localizedTermEquiv_reindex M r f i.succAbove)

/-- The relative section complex is the localization-Cech complex over the localized ring. -/
def localizedComplexIso :
    ((ModuleCat.restrictScalars (algebraMap R (Localization.Away r))).mapHomologicalComplex
      (.up ℕ)).obj (complex (localizedFamily r f) (localizedModule M r)) ≅
        baseComplex f M r :=
  HomologicalComplex.Hom.isoOfComponents (localizedTermIso M r f)
    (by
      intro p q h
      obtain rfl : p + 1 = q := h
      exact (localizedTermIso_differential M r f p).symm)

variable (hf : (⨆ i, PrimeSpectrum.basicOpen (f i)) = PrimeSpectrum.basicOpen r)

include hf in
/-- Every nonempty cover intersection is already inside the fixed principal open. -/
lemma coverIntersection_eq (q : ℕ) (s : Fin (q + 1) → ι) :
    PrimeSpectrum.basicOpen (r * ∏ j, f (s j)) =
      PrimeSpectrum.basicOpen (∏ j, f (s j)) := by
  rw [PrimeSpectrum.basicOpen_mul, inf_eq_right]
  rw [cechTerm_open f q s, ← hf]
  exact (iInf_le _ 0).trans (le_iSup (fun i : ι ↦ PrimeSpectrum.basicOpen (f i)) (s 0))

/-- For a cover of `D(r)`, termwise restriction to `D(r)` is an isomorphism. -/
def coverTermIso (q : ℕ) : term f M q ≅ baseTerm f M r q :=
  (LinearEquiv.piCongrRight fun s : Fin (q + 1) → ι ↦
    (((modulesSpecToSheaf.obj (tilde M)).presheaf.mapIso
      (eqToIso (congrArg op (coverIntersection_eq r f hf q s).symm))).toLinearEquiv)).toModuleIso

lemma coverTermIso_hom (q : ℕ) :
    (coverTermIso M r f hf q).hom.hom = toBaseTerm f M r q := rfl

/-- Restriction to the fixed open preserves the differentials of the original cover. -/
lemma coverTermIso_differential (q : ℕ) :
    (complex f M).d q (q + 1) ≫ (coverTermIso M r f hf (q + 1)).hom =
      (coverTermIso M r f hf q).hom ≫ (baseComplex f M r).d q (q + 1) := by
  rw [differential, baseDifferential]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1

/-- The cover complex agrees with its restriction to the open it covers. -/
def coverComplexIso : complex f M ≅ baseComplex f M r :=
  HomologicalComplex.Hom.isoOfComponents (coverTermIso M r f hf)
    (by
      intro p q h
      obtain rfl : p + 1 = q := h
      exact (coverTermIso_differential M r f hf p).symm)

/-- Actual relative sheaf sections identified with the Cech complex over `R_r`. -/
def relativeCechIso :
    CechSheafHZero.C (fun i ↦ PrimeSpectrum.basicOpen (f i))
        (FCurve.moduleAbelianSheaf (tilde M)) ≅
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj
        (((ModuleCat.restrictScalars (algebraMap R (Localization.Away r))).mapHomologicalComplex
          (.up ℕ)).obj (complex (localizedFamily r f) (localizedModule M r))) :=
  (localizationCechIso f M).symm ≪≫
    ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).mapIso
      (coverComplexIso M r f hf ≪≫ (localizedComplexIso M r f).symm)

/-- The relative coordinates retain the canonical finite-product localization comparison. -/
lemma compare_coverTermIso [Finite ι] (q : ℕ) (x : term f M q) :
    compare f M r q (toSections (term f M q) r x) =
      (coverTermIso M r f hf q).hom x :=
  compare_toSections f M r q x

end FLT.Mazur.AffineCohomologyVanishingRelCoordinates
