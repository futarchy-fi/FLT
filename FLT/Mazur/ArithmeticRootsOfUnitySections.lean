/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticTorusPoints
public import FLT.Mazur.RootsOfUnityAlgebraPoints
public import FLT.Mazur.RootsOfUnityScheme

/-!
# Actual arithmetic sections of the roots-of-unity subgroup

A specified torsion unit gives an actual section of the character group scheme.
Its inclusion and every power are the corresponding Laurent unit evaluations.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.ArithmeticRootsOfUnitySections

universe u
variable (R : Type u) [CommRing R] (n : ℕ) [NeZero n]

/-- Evaluation of a torsion unit is a section of the actual finite subgroup scheme. -/
def rootSection (a : Rˣ) (ha : a ^ n = 1) :
    𝟙_ (Over (Spec (.of R))) ⟶ RootsOfUnityScheme.model R n :=
  Over.homMk (Spec.map (CommRingCat.ofHom
    (RootsOfUnityAlgebraPoints.evalRoot (R := R) n a ha).toRingHom)) (by
      change Spec.map _ ≫ Spec.map _ = 𝟙 _
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 1
      exact CommRingCat.hom_ext
        (RootsOfUnityAlgebraPoints.evalRoot (R := R) n a ha).comp_algebraMap)

/-- Inclusion of the root section is exactly Laurent evaluation at the same unit. -/
theorem section_inclusion (a : Rˣ) (ha : a ^ n = 1) :
    rootSection R n a ha ≫ RootsOfUnityScheme.inclusion R n =
      ArithmeticTorusPoints.point R a := by
  have h : (RootsOfUnityAlgebraPoints.evalRoot (R := R) n a ha).comp
      (RootsOfUnityAlgebra.restriction R n).toAlgHom =
      LaurentUnitPoints.evalUnit (R := R) a := by
    apply LaurentUnitPoints.pointsEquiv.injective
    change LaurentUnitPoints.pointUnit _ = LaurentUnitPoints.pointUnit _
    rw [RootsOfUnityAlgebraPoints.pointRoot_restriction,
      RootsOfUnityAlgebraPoints.pointRoot_evalRoot, LaurentUnitPoints.pointUnit_evalUnit]
  apply Over.OverMorphism.ext
  change (rootSection R n a ha).left ≫ (RootsOfUnityScheme.inclusion R n).left = _
  rw [RootsOfUnityScheme.inclusion_left, ArithmeticTorusPoints.point_left]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f))) h

/-- All powers of a root section retain their actual Laurent unit coordinates. -/
theorem section_pow_inclusion (a : Rˣ) (ha : a ^ n = 1) (k : ℕ) :
    (rootSection R n a ha ^ k) ≫ RootsOfUnityScheme.inclusion R n =
      ArithmeticTorusPoints.point R (a ^ k) := by
  rw [pow_comp, section_inclusion, ArithmeticTorusPoints.point_pow]

/-- The actual subgroup section satisfies its specified torsion relation. -/
theorem section_pow_order (a : Rˣ) (ha : a ^ n = 1) : rootSection R n a ha ^ n = 1 := by
  apply (cancel_mono (RootsOfUnityScheme.inclusion R n)).mp
  rw [section_pow_inclusion, ha, ArithmeticTorusPoints.point_one, one_comp]

end FLT.Mazur.ArithmeticRootsOfUnitySections
