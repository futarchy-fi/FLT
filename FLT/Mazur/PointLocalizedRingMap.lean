/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointLocalizedRingDiagram
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Localizing a morphism of affine stage systems at a chosen point

The chosen target point determines the base point and every stage map. The
original commuting squares yield a natural transformation of local diagrams
and the actual local map between their cocone points.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace FLT.Mazur.PointLocalizedRingMap
open PointLocalizedRingDiagram
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
variable {I : Type v} [Category.{w} I] {F G : I ⥤ CommRingCat.{u}}
  (c : Cocone F) (d : Cocone G) (η : F ⟶ G) (φ : c.pt →+* d.pt)
  (hφ : ∀ i, (d.ι.app i).hom.comp (η.app i).hom = φ.comp (c.ι.app i).hom)
  (Q : Ideal d.pt) [Q.IsPrime]

include hφ in
omit [Q.IsPrime] in
/-- The prime on the base stage is the inverse image of the target-stage prime. -/
theorem stage_prime_comap (i : I) :
    prime c (Q.comap φ) i = (prime d Q i).comap (η.app i).hom := by
  simp only [prime, Ideal.comap_comap]
  rw [hφ i]

/-- The induced map between the actual local rings of corresponding affine stages. -/
def stageMap (i : I) : Stage c (Q.comap φ) i →+* Stage d Q i :=
  Localization.localRingHom _ _ (η.app i).hom (stage_prime_comap c d η φ hφ Q i)

@[simp] theorem stageMap_algebraMap (i : I) (x : F.obj i) :
    stageMap c d η φ hφ Q i (algebraMap _ _ x) =
      algebraMap (G.obj i) (Stage d Q i) (η.app i x) :=
  Localization.localRingHom_to_map _ _ _ _ x

instance stageMap_isLocalHom (i : I) : IsLocalHom (stageMap c d η φ hφ Q i) :=
  Localization.isLocalHom_localRingHom _ _ _ _

/-- The actual stage maps assemble into a morphism of localized diagrams. -/
def localizedMap : diagram c (Q.comap φ) ⟶ diagram d Q where
  app i := CommRingCat.ofHom (stageMap c d η φ hφ Q i)
  naturality i j f := by
    apply CommRingCat.hom_ext
    change (stageMap c d η φ hφ Q j).comp (transition c (Q.comap φ) f) =
      (transition d Q f).comp (stageMap c d η φ hφ Q i)
    apply IsLocalization.ringHom_ext (prime c (Q.comap φ) i).primeCompl
    ext x
    simp only [RingHom.comp_apply, transition_algebraMap, stageMap_algebraMap]
    exact congrArg (algebraMap (G.obj j) (Stage d Q j))
      (ConcreteCategory.congr_hom (η.naturality f) x)

/-- The original map localized at the chosen target point and its base image. -/
def pointMap : Localization.AtPrime (Q.comap φ) →+* Localization.AtPrime Q :=
  Localization.localRingHom _ _ φ rfl

@[simp] theorem pointMap_algebraMap (x : c.pt) :
    pointMap c d φ Q (algebraMap _ _ x) = algebraMap d.pt (Localization.AtPrime Q) (φ x) :=
  Localization.localRingHom_to_map _ _ _ _ x

instance pointMap_isLocalHom : IsLocalHom (pointMap c d φ Q) :=
  Localization.isLocalHom_localRingHom _ _ _ _

/-- The localized cocones retain the original commuting square at every stage. -/
theorem pointMap_square (i : I) :
    (toPoint d Q i).comp (stageMap c d η φ hφ Q i) =
      (pointMap c d φ Q).comp (toPoint c (Q.comap φ) i) := by
  apply IsLocalization.ringHom_ext (prime c (Q.comap φ) i).primeCompl
  ext x
  simp only [RingHom.comp_apply, stageMap_algebraMap, toPoint_algebraMap, pointMap_algebraMap]
  exact congrArg (algebraMap d.pt (Localization.AtPrime Q)) (RingHom.congr_fun (hφ i) x)

/-- Flatness of the original affine map gives flatness of the constructed local map. -/
theorem pointMap_flat (hflat : φ.Flat) : (pointMap c d φ Q).Flat :=
  hflat.localRingHom Q (Q.comap φ) rfl

end FLT.Mazur.PointLocalizedRingMap
