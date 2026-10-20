/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSpectrumKernelIdeal
public import FLT.Mazur.SmoothNilpotentLocalLift
public import FLT.Mazur.WeierstrassDiagonalizableLiftUniqueness

/-!
# Actual local lifts on nonlocal diagonalizable tests

The original character coefficient reduction is a square-zero closed immersion
on schemes. Smoothness constructs underlying scheme-map lifts on affine open
neighborhoods of every point, without assuming the roots coordinate ring is
local. Agreement of these lifts on overlaps is not asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.WeierstrassDiagonalizableDefect

open DiagonalizableCobar WeierstrassIntegralChart BaseAdicThickening

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R G : Type} [CommRing R] [AddCommMonoid G] (I : Ideal R)

/-- The original coefficient reduction as a closed test-scheme inclusion. -/
def coefficientImmersion : Spec (.of (AddMonoidAlgebra (R ⧸ I) G)) ⟶
    Spec (.of (AddMonoidAlgebra R G)) :=
  Spec.map (CommRingCat.ofHom (coefficientReduction R G I).toRingHom)

instance coefficientImmersion_closed : IsClosedImmersion (coefficientImmersion (G := G) I) :=
  IsClosedImmersion.spec_of_surjective _ (coefficientReduction_surjective R G I)

/-- The scheme-theoretic kernel is exactly the full original coefficient ideal sheaf. -/
theorem coefficientImmersion_ker : (coefficientImmersion (G := G) I).ker =
    baseIdeal (.of (AddMonoidAlgebra R G)) (coefficientIdeal R G I) :=
  specMap_ker_baseIdeal _

/-- The actual test-scheme thickening retains square-zero nilpotence everywhere. -/
theorem coefficientImmersion_ker_sq_zero (hI : I ^ 2 = ⊥) :
    (coefficientImmersion (G := G) I).ker ^ 2 = ⊥ := by
  rw [coefficientImmersion_ker, ← baseIdeal_pow, coefficientIdeal_sq_zero R G I hI]
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp [baseIdeal_top]

/-- Every point of the original diagonalizable test has an affine neighborhood with a lift. -/
theorem exists_local_lift (W : WeierstrassCurve R) (hI : I ^ 2 = ⊥)
    (p : Points W (AddMonoidAlgebra (R ⧸ I) G))
    (x : Spec (.of (AddMonoidAlgebra R G))) :
    ∃ U : (Spec (.of (AddMonoidAlgebra R G))).Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∃ s : U.toScheme ⟶ (integralSmoothOpen W).toScheme,
        (coefficientImmersion I ∣_ U) ≫ s = (coefficientImmersion I ⁻¹ᵁ U).ι ≫ p.left ∧
        s ≫ integralSmoothStructure W =
          U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R G))) := by
  apply SmoothNilpotentLocalLift.exists_lift (coefficientImmersion I)
    ⟨2, coefficientImmersion_ker_sq_zero I hI⟩ (integralSmoothStructure W) p.left
    (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R G)))) _ x
  exact (smoothAlgebraTestMap (coefficientReduction R G I)).w.trans p.w.symm

end FLT.Mazur.WeierstrassDiagonalizableDefect
