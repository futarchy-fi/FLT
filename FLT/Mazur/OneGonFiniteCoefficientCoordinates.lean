/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CharacterFiniteCoefficientModel
public import FLT.Mazur.OneGonSmoothingEquation
public import FLT.Mazur.WeierstrassChartCoefficientRingMap

/-!
# Descending original one-gon character coordinates

The full coordinate map to a finite character algebra descends to a finite
coefficient ring. Cubic and normalization equations are proved by injective
coefficient inclusion; no equation or descended map is assumed.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.OneGonFiniteCoefficientCoordinates

open WeierstrassIntegralChart OneGonSmoothing

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R G : Type*} [CommRing R] [AddCommMonoid G]
  (t : R) (j : Fin 3) (φ : Coordinate (equation t) j →ₐ[R] AddMonoidAlgebra R G)
  (s : Set R)

/-- The three actual normalized coordinate images. -/
def values (i : Fin 3) : AddMonoidAlgebra R G := φ (coord (equation t) j i)

/-- Retain the smoothing parameter as well as all actual coordinate coefficients. -/
abbrev modelRing : Subalgebra ℤ R :=
  CharacterFiniteCoefficientModel.coefficientRing (values t j φ) (s ∪ {t})

/-- The smoothing parameter over the selected coefficient ring. -/
def modelParameter : modelRing t j φ s :=
  ⟨t, CharacterFiniteCoefficientModel.subset_coefficientRing _ _ (Or.inr rfl)⟩

/-- The lifted projective coordinates on the unchanged character group. -/
def modelValues : Fin 3 → AddMonoidAlgebra (modelRing t j φ s) G :=
  CharacterFiniteCoefficientModel.lift (values t j φ) (s ∪ {t})

/-- The injective original coefficient inclusion on character algebras. -/
abbrev modelInclusion :=
  CharacterFiniteCoefficientModel.inclusion (values t j φ) (s ∪ {t})

/-- Every coordinate is recovered in full. -/
@[simp] theorem modelValues_recovery (i : Fin 3) :
    modelInclusion t j φ s (modelValues t j φ s i) = values t j φ i :=
  CharacterFiniteCoefficientModel.inclusion_lift _ _ i

/-- The actual coordinate images satisfy the cubic equation. -/
theorem values_equation :
    ((equation t).map (algebraMap R (AddMonoidAlgebra R G))).toProjective.Equation
      (values t j φ) := by
  have h := (coord_equation (equation t) j).map φ.toRingHom
  change (((equation t).map (algebraMap R (Coordinate (equation t) j))).map
    φ.toRingHom).toProjective.Equation (φ ∘ coord (equation t) j) at h
  have he : φ.toRingHom.comp (algebraMap R (Coordinate (equation t) j)) =
      algebraMap R (AddMonoidAlgebra R G) := by
    apply RingHom.ext
    intro a
    exact φ.commutes a
  rw [WeierstrassCurve.map_map, he] at h
  exact h

/-- Injective coefficient inclusion proves the descended cubic equation. -/
theorem modelValues_equation :
    ((equation (modelParameter t j φ s)).map
      (algebraMap (modelRing t j φ s)
        (AddMonoidAlgebra (modelRing t j φ s) G))).toProjective.Equation
      (modelValues t j φ s) := by
  apply (WeierstrassCurve.Projective.map_equation
    (W' := ((equation (modelParameter t j φ s)).map
      (algebraMap (modelRing t j φ s) (AddMonoidAlgebra (modelRing t j φ s) G))))
    (f := modelInclusion t j φ s)
    (CharacterFiniteCoefficientModel.inclusion_injective _ _) _).mp
  have hmap : (modelInclusion t j φ s).comp
      (algebraMap (modelRing t j φ s) (AddMonoidAlgebra (modelRing t j φ s) G)) =
        (algebraMap R (AddMonoidAlgebra R G)).comp (modelRing t j φ s).val.toRingHom := by
    ext a
    simp [modelInclusion, CharacterFiniteCoefficientModel.inclusion]
  change ((equation (modelParameter t j φ s)).map
    ((modelInclusion t j φ s).comp (algebraMap (modelRing t j φ s)
      (AddMonoidAlgebra (modelRing t j φ s) G)))).toProjective.Equation _
  rw [hmap, ← WeierstrassCurve.map_map, equation_map]
  change ((equation t).map (algebraMap R (AddMonoidAlgebra R G))).toProjective.Equation
    (modelInclusion t j φ s ∘ modelValues t j φ s)
  simpa only [Function.comp_def, modelValues_recovery] using values_equation t j φ

/-- The selected projective coordinate remains one before coefficient extension. -/
theorem modelValues_normalized : modelValues t j φ s j = 1 := by
  apply CharacterFiniteCoefficientModel.inclusion_injective (values t j φ) (s ∪ {t})
  rw [modelValues_recovery, map_one, values, coord_self, map_one]

/-- The constructed full coordinate map over the selected coefficient ring. -/
def modelCoordinates : Coordinate (equation (modelParameter t j φ s)) j →ₐ[modelRing t j φ s]
    AddMonoidAlgebra (modelRing t j φ s) G :=
  evaluation _ j (modelValues t j φ s) (modelValues_equation t j φ s)
    (modelValues_normalized t j φ s)

/-- The model is of finite type over the integers. -/
theorem modelRing_finiteType [Finite G] (hs : s.Finite) :
    Algebra.FiniteType ℤ (modelRing t j φ s) :=
  CharacterFiniteCoefficientModel.coefficientRing_finiteType _ _
    (hs.union (Set.finite_singleton t))

end FLT.Mazur.OneGonFiniteCoefficientCoordinates
