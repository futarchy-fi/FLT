/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule

/-!
# Affine stage rings localized at a point of a cocone

A prime of the limiting affine ring determines compatible primes at every
stage. Localization constructs the actual local transition maps and cocone;
locality and Noetherianity are proved for these rings, not supplied as data.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace FLT.Mazur.PointLocalizedRingDiagram
universe u v w
variable {I : Type v} [Category.{w} I] {F : I ⥤ CommRingCat.{u}}
  (c : Cocone F) (P : Ideal c.pt) [P.IsPrime]

/-- The point on each affine stage induced by the chosen limiting point. -/
abbrev prime (i : I) : Ideal (F.obj i) := P.comap (c.ι.app i).hom

/-- The actual local ring of a stage at the induced prime. -/
abbrev Stage (i : I) := Localization.AtPrime (prime c P i)

omit [P.IsPrime] in
/-- The stage primes are compatible with the original transitions. -/
theorem prime_comap {i j : I} (f : i ⟶ j) :
    prime c P i = (prime c P j).comap (F.map f).hom := by
  rw [prime, prime, Ideal.comap_comap]
  exact congrArg (fun f ↦ P.comap f) (congrArg CommRingCat.Hom.hom (c.w f)).symm

/-- The local map induced by an actual stage transition. -/
def transition {i j : I} (f : i ⟶ j) : Stage c P i →+* Stage c P j :=
  Localization.localRingHom _ _ (F.map f).hom (prime_comap c P f)

/-- Localization retains the value of every original stage element. -/
@[simp] theorem transition_algebraMap {i j : I} (f : i ⟶ j) (x : F.obj i) :
    transition c P f (algebraMap _ _ x) = algebraMap _ _ (F.map f x) :=
  Localization.localRingHom_to_map _ _ _ _ x

instance transition_isLocalHom {i j : I} (f : i ⟶ j) :
    IsLocalHom (transition c P f) :=
  Localization.isLocalHom_localRingHom _ _ _ _

instance stage_noetherian (i : I) [IsNoetherianRing (F.obj i)] :
    IsNoetherianRing (Stage c P i) := inferInstance

/-- The localized affine stage diagram at the specified point. -/
def diagram : I ⥤ CommRingCat.{u} where
  obj i := .of (Stage c P i)
  map f := CommRingCat.ofHom (transition c P f)
  map_id i := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (prime c P i).primeCompl
    ext x
    simp only [RingHom.comp_apply, transition_algebraMap, F.map_id,
      CommRingCat.hom_ofHom, CommRingCat.hom_id, RingHom.id_apply]
  map_comp {i j k} f g := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (prime c P i).primeCompl
    ext x
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp, RingHom.comp_apply,
      transition_algebraMap, F.map_comp]

/-- The canonical maps into the local ring of the limiting affine point. -/
def toPoint (i : I) : Stage c P i →+* Localization.AtPrime P :=
  Localization.localRingHom _ _ (c.ι.app i).hom rfl

@[simp] theorem toPoint_algebraMap (i : I) (x : F.obj i) :
    toPoint c P i (algebraMap _ _ x) = algebraMap c.pt (Localization.AtPrime P) (c.ι.app i x) :=
  Localization.localRingHom_to_map _ _ _ _ x

instance toPoint_isLocalHom (i : I) : IsLocalHom (toPoint c P i) :=
  Localization.isLocalHom_localRingHom _ _ _ _

/-- The local ring of the limiting point receives the localized stage diagram. -/
def cocone : Cocone (diagram c P) where
  pt := .of (Localization.AtPrime P)
  ι.app i := CommRingCat.ofHom (toPoint c P i)
  ι.naturality i j f := by
    apply CommRingCat.hom_ext
    change (toPoint c P j).comp (transition c P f) = toPoint c P i
    apply IsLocalization.ringHom_ext (prime c P i).primeCompl
    ext x
    change toPoint c P j (transition c P f (algebraMap _ _ x)) =
      toPoint c P i (algebraMap _ _ x)
    rw [transition_algebraMap, toPoint_algebraMap, toPoint_algebraMap]
    exact congrArg (algebraMap c.pt (Localization.AtPrime P)) (ConcreteCategory.congr_hom (c.w f) x)

end FLT.Mazur.PointLocalizedRingDiagram
