/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentProjectiveConjugation
public import FLT.Mazur.ProjectiveLineHomogeneousReversal

/-!
# Complete root conjugation in ordered normalization coordinates

The actual root-sheared operation becomes coefficient conjugation followed
by homogeneous endpoint reversal after q=z/(z+a), on the entire projective line.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
namespace FLT.Mazur
open ProjectiveSpace ProjectiveLine
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "a" => WeierstrassCurve.a₁ (nodeTangentShear W)
local notation "σ" => RingEquiv.toRingHom (AlgEquiv.toRingEquiv (nodeTangentConjugation W))

/-- Ordered homogeneous normalization converts actual root exchange into complete reflection. -/
@[reassoc] theorem nodeTangentProjectiveConjugation_normalization
    (t : Sˣ) (ht : (t : S) = a) :
    nodeTangentProjectiveConjugation W ≫ (slopeNormalizationProjIso t).hom =
      (slopeNormalizationProjIso t).hom ≫
        coefficientMap σ (ULift.{u} (Fin 2)) ≫ (reversalProjIso S).hom := by
  change (Proj.map _ _ ≫ Proj.map _ _) ≫ Proj.map _ _ =
    Proj.map _ _ ≫ Proj.map _ _ ≫ Proj.map _ _
  simp only [← Proj.map_comp]
  congr 1
  apply GradedRingHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [linearGradedMap, linearSubstitution, coefficientGradedMap]
  · intro i
    change linearSubstitution (translationMap a)
        (MvPolynomial.map σ (linearSubstitution (slopeNormalizationMap t) (X i))) =
      linearSubstitution (slopeNormalizationMap t)
        (MvPolynomial.map σ (linearSubstitution (reversalMap S) (X i)))
    rw [slopeNormalization_substitution, reversal_substitution]
    rcases i with ⟨i⟩
    fin_cases i <;>
      simp [-linearSubstitution_X, translation_substitution, slopeNormalization_substitution,
        ht, nodeTangentShear_a₁_conjugate,
        show ∀ c, linearSubstitution (translationMap a) (C c) = C c from
          fun c => AlgHom.commutes _ c]
    ring

end FLT.Mazur
