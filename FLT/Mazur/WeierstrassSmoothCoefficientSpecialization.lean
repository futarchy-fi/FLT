/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothCoefficientCartesian

/-!
# Specialization of the entire original smooth coefficient scheme

An actual algebra map gives a map of the original geometric smooth loci by
their proved cartesian comparison. Both original projections are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
  {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  (f : S →ₐ[R] T)
local notation "sS" => integralSmoothStructure (W.map (algebraMap R S))
local notation "sT" => integralSmoothStructure (W.map (algebraMap R T))
local notation "pS" => originalSmoothCoefficientMap S W
local notation "pT" => originalSmoothCoefficientMap T W
local notation "b" => Spec.map (CommRingCat.ofHom f.toRingHom)
local notation "qS" => Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- The full original smooth coefficient projections form the specialization square. -/
theorem originalSmoothSpecialization_square :
    pT ≫ integralSmoothStructure W = (sT ≫ b) ≫ qS := by
  have hf : b ≫ qS = Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext f.commutes)
  exact (originalSmoothCoefficientMap_structure T W).trans
    ((Category.assoc sT b qS).trans (congrArg (sT ≫ ·) hf)).symm

/-- Specialize the full original smooth scheme along the actual coefficient map. -/
def originalSmoothSpecialization :
    (integralSmoothOpen (W.map (algebraMap R T))).toScheme ⟶
      (integralSmoothOpen (W.map (algebraMap R S))).toScheme :=
  (originalSmoothCoefficientMap_isPullback S W).lift pT (sT ≫ b)
    (originalSmoothSpecialization_square W f)

/-- The original integral smooth parameter is unchanged by specialization. -/
@[reassoc] theorem originalSmoothSpecialization_projection :
    originalSmoothSpecialization W f ≫ pS = pT :=
  (originalSmoothCoefficientMap_isPullback S W).lift_fst _ _ _

/-- The structure morphism specializes by the prescribed algebra map. -/
@[reassoc] theorem originalSmoothSpecialization_structure :
    originalSmoothSpecialization W f ≫ sS = sT ≫ b :=
  (originalSmoothCoefficientMap_isPullback S W).lift_snd _ _ _

/-- Both original projections characterize the entire smooth specialization. -/
theorem originalSmoothSpecialization_unique {Z : Scheme.{u}}
    (x : Z ⟶ (integralSmoothOpen (W.map (algebraMap R T))).toScheme)
    (y : Z ⟶ (integralSmoothOpen (W.map (algebraMap R S))).toScheme)
    (hp : y ≫ pS = x ≫ pT) (hs : y ≫ sS = x ≫ sT ≫ b) :
    y = x ≫ originalSmoothSpecialization W f := by
  apply (originalSmoothCoefficientMap_isPullback S W).hom_ext
  · rw [Category.assoc, originalSmoothSpecialization_projection, hp]
  · rw [Category.assoc, originalSmoothSpecialization_structure, hs]

end FLT.Mazur.WeierstrassDividedDepth
