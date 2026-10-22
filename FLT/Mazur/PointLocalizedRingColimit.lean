/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointLocalizedRingDiagram
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Recovery of the local ring from the localized affine stages

Every denominator outside the limiting prime comes from a stage element outside
its induced prime. The universal map out of the original colimit therefore
inverts all these denominators. This constructs the localized colimit cocone.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace FLT.Mazur.PointLocalizedRingDiagram
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
variable {I : Type v} [Category.{w} I] {F : I ⥤ CommRingCat.{u}}
  (c : Cocone F) (P : Ideal c.pt) [P.IsPrime]

/-- Forgetting denominators turns a cocone of local stage rings into one of affine rings. -/
def originalCocone (s : Cocone (diagram c P)) : Cocone F where
  pt := s.pt
  ι.app i := CommRingCat.ofHom ((s.ι.app i).hom.comp (algebraMap _ (Stage c P i)))
  ι.naturality i j f := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change s.ι.app j (algebraMap _ (Stage c P j) (F.map f x)) =
      s.ι.app i (algebraMap _ (Stage c P i) x)
    have h := ConcreteCategory.congr_hom (s.w f) (algebraMap _ (Stage c P i) x)
    change s.ι.app j (transition c P f (algebraMap _ _ x)) = _ at h
    rw [transition_algebraMap] at h
    exact h

variable (hc : IsColimit c)

/-- The map out of the original affine colimit, before inverting its denominators. -/
def originalDesc (s : Cocone (diagram c P)) : c.pt →+* s.pt :=
  (hc.desc (originalCocone c P s)).hom

/-- This map recovers the prescribed local-stage cocone on affine elements. -/
theorem originalDesc_app (s : Cocone (diagram c P)) (i : I) (x : F.obj i) :
    originalDesc c P hc s (c.ι.app i x) = s.ι.app i (algebraMap _ (Stage c P i) x) :=
  ConcreteCategory.congr_hom (hc.fac (originalCocone c P s) i) x

variable [PreservesColimit F (forget CommRingCat)]

/-- Every denominator of the limiting local ring is inverted by the universal affine map. -/
theorem originalDesc_isUnit (s : Cocone (diagram c P)) (x : P.primeCompl) :
    IsUnit (originalDesc c P hc s x) := by
  obtain ⟨i, y, hy⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget CommRingCat) hc) x.val
  change F.obj i at y
  have hy' : c.ι.app i y = x.val := hy
  have hn : y ∈ (prime c P i).primeCompl := by
    change c.ι.app i y ∉ P
    rw [hy']
    exact x.property
  rw [← hy', originalDesc_app]
  exact (IsLocalization.map_units (Stage c P i) ⟨y, hn⟩).map (s.ι.app i).hom

/-- The actual universal map out of the local ring at the limiting point. -/
def localizedDesc (s : Cocone (diagram c P)) : Localization.AtPrime P →+* s.pt :=
  IsLocalization.lift (originalDesc_isUnit c P hc s)

/-- The localized universal map extends the original affine universal map. -/
@[simp] theorem localizedDesc_algebraMap (s : Cocone (diagram c P)) (x : c.pt) :
    localizedDesc c P hc s (algebraMap _ _ x) = originalDesc c P hc s x :=
  IsLocalization.lift_eq _ x

/-- Localization at a compatible point commutes with the filtered affine colimit. -/
def localizedIsColimit : IsColimit (cocone c P) where
  desc s := CommRingCat.ofHom (localizedDesc c P hc s)
  fac s i := by
    apply CommRingCat.hom_ext
    change (localizedDesc c P hc s).comp (toPoint c P i) = (s.ι.app i).hom
    apply IsLocalization.ringHom_ext (prime c P i).primeCompl
    ext x
    change localizedDesc c P hc s (toPoint c P i (algebraMap _ _ x)) = _
    rw [toPoint_algebraMap, localizedDesc_algebraMap, originalDesc_app]
    rfl
  uniq s m hm := by
    apply CommRingCat.hom_ext
    change m.hom = localizedDesc c P hc s
    apply IsLocalization.ringHom_ext (S := Localization.AtPrime P) P.primeCompl
    ext x
    obtain ⟨i, y, hy⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget CommRingCat) hc) x
    change F.obj i at y
    have hy' : c.ι.app i y = x := hy
    change m (algebraMap c.pt (Localization.AtPrime P) x) =
      localizedDesc c P hc s (algebraMap _ _ x)
    rw [← hy', localizedDesc_algebraMap, originalDesc_app]
    have h := ConcreteCategory.congr_hom (hm i) (algebraMap _ (Stage c P i) y)
    change m (toPoint c P i (algebraMap (F.obj i) (Stage c P i) y)) = _ at h
    rwa [toPoint_algebraMap] at h

end FLT.Mazur.PointLocalizedRingDiagram
