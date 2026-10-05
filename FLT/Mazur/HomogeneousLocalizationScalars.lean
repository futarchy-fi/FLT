/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjStructuralMap

/-!
# Structural scalars on homogeneous localizations

A homogeneous localization is an algebra over the structural scalar ring,
and its inclusion in the ordinary localization is linear over that ring.
-/

@[expose] public noncomputable section
open HomogeneousLocalization
universe u
namespace FLT.Mazur.HomogeneousLocalizationScalars
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (f : A)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Structural scalars enter a homogeneous localization as degree-zero fractions. -/
scoped instance scalarAlgebra : Algebra R (Away 𝒜 f) where
  smul := (· • ·)
  algebraMap := GradedProjStructuralMap.scalarToAway 𝒜 f
  commutes' _ _ := mul_comm _ _
  smul_def' r x := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_smul, val_mul]
    change r • x.val = Localization.mk (algebraMap R A r) ⟨1, _⟩ * x.val
    exact Algebra.smul_def r x.val

/-- The structural scalar fraction has the usual value in the ordinary localization. -/
lemma val_algebraMap (r : R) :
    (algebraMap R (Away 𝒜 f) r).val = algebraMap R (Localization.Away f) r := by
  change Localization.mk (algebraMap R A r) ⟨1, _⟩ = _
  rfl

/-- The homogeneous-localization inclusion respects the structural scalar ring. -/
def valAlgHom : Away 𝒜 f →ₐ[R] Localization.Away f where
  __ := algebraMap (Away 𝒜 f) (Localization.Away f)
  commutes' := val_algebraMap 𝒜 f

/-- The homogeneous-localization inclusion is injective. -/
lemma valAlgHom_injective : Function.Injective (valAlgHom 𝒜 f) :=
  HomogeneousLocalization.val_injective _

end FLT.Mazur.HomogeneousLocalizationScalars
