/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonFiniteCoefficientCurve
public import FLT.Mazur.OneGonFiniteCoefficientClosed
public import FLT.Mazur.WeierstrassIntegralSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Closed finite-coefficient embeddings in the entire cubic

The finite character source and separated whole cubic turn the descended
chart immersion into a closed immersion. Its full ideal sheaf recovers by
the proved Cartesian square, with no flatness requirement on coefficient inclusion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.OneGonFiniteCoefficientCoordinates

open WeierstrassIntegralChart OneGonSmoothing CharacterSchemeBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R G : Type} [CommRing R] [AddCommMonoid G] [Finite G]
  (t : R) (j : Fin 3) (φ : Coordinate (equation t) j →ₐ[R] AddMonoidAlgebra R G)

/-- Finite character coordinates give a finite morphism into the entire separated cubic. -/
theorem coordinateCurveMap_isFinite : IsFinite (coordinateCurveMap t j φ) := by
  let _ : Module.Finite R (AddMonoidAlgebra R G) :=
    Module.Finite.of_basis (AddMonoidAlgebra.basis G R)
  let _ : IsFinite (model R G).hom := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  let _ : IsFinite (coordinateCurveMap t j φ ≫ integralCurveStructure (equation t)) := by
    rw [coordinateCurveMap_structure]
    infer_instance
  exact IsFinite.of_comp _ (integralCurveStructure (equation t))

/-- Surjective chart coordinates give a closed embedding in the whole cubic. -/
theorem coordinateCurveMap_isClosedImmersion (hφ : Function.Surjective φ) :
    IsClosedImmersion (coordinateCurveMap t j φ) := by
  let _ : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hφ
  let _ : Mono (coordinateCurveMap t j φ) := by
    unfold coordinateCurveMap
    infer_instance
  exact (IsClosedImmersion.iff_isFinite_and_mono _).mpr
    ⟨coordinateCurveMap_isFinite t j φ, inferInstance⟩

variable (s : Set R) (hφ : Function.Surjective (modelCoordinates t j φ s))

include hφ

/-- The actual descended model embeds closedly in its entire finite-coefficient cubic. -/
theorem modelCurveMap_isClosedImmersion : IsClosedImmersion (modelCurveMap t j φ s) :=
  coordinateCurveMap_isClosedImmersion _ _ _ hφ

/-- Recovery pulls back the full model ideal, including its infinitesimal structure. -/
theorem modelCurveMap_ker :
    (coordinateCurveMap t j φ).ker =
      (modelCurveMap t j φ s).ker.comap (modelCurveProjection t j φ s) := by
  let _ := modelCurveMap_isClosedImmersion t j φ s hφ
  let h := (modelCurveMap_isPullback t j φ s).flip
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
  exact Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _

end FLT.Mazur.OneGonFiniteCoefficientCoordinates
