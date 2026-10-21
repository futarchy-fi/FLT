/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarImageKernelGeometry

/-!
# The full original kernel pair over an image neighborhood

Restrict the original kernel pair over an arbitrary open of its exact image.
Both endpoints remain present, and local image geometry controls the entire
restricted kernel pair, without any global image hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarImageKernelNeighborhood
open SchemeScalarImageQuotient
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme.{0}}
  (f : X ⟶ Spec (.of R)) (U : (Spec (.of (Scalars f))).Opens)
local notation "c" => projection f
local notation "u" => pullback.fst f f
local notation "v" => pullback.snd f f

/-- Both full original kernel coordinates lie over the same image neighborhood. -/
theorem kernel_preimage_eq : u ⁻¹ᵁ (c ⁻¹ᵁ U) = v ⁻¹ᵁ (c ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
    (SchemeScalarImageKernelGeometry.kernel_isPullback f).w]

/-- The second original endpoint restricted on the whole first-endpoint preimage. -/
def second : (u ⁻¹ᵁ (c ⁻¹ᵁ U)).toScheme ⟶ (c ⁻¹ᵁ U).toScheme :=
  (v).resLE (c ⁻¹ᵁ U) (u ⁻¹ᵁ (c ⁻¹ᵁ U)) (kernel_preimage_eq f U).le

/-- The restricted second endpoint still has the original second coordinate. -/
@[reassoc] theorem second_ι : second f U ≫ (c ⁻¹ᵁ U).ι =
    (u ⁻¹ᵁ (c ⁻¹ᵁ U)).ι ≫ v :=
  Scheme.Hom.resLE_comp_ι v (kernel_preimage_eq f U).le

/-- The whole restricted original kernel square is cartesian over the restricted image. -/
theorem kernel_isPullback :
    IsPullback (u ∣_ (c ⁻¹ᵁ U)) (second f U) (c ∣_ U) (c ∣_ U) := by
  have hle := (kernel_preimage_eq f U).le
  have H : IsPullback (second f U) (u ∣_ (c ⁻¹ᵁ U)) (c ∣_ U) (c ∣_ U) := by
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict, second] using
      Scheme.Hom.isPullback_resLE
        (SchemeScalarImageKernelGeometry.kernel_isPullback f).flip
        (le_rfl : c ⁻¹ᵁ U ≤ c ⁻¹ᵁ U) (le_rfl : c ⁻¹ᵁ U ≤ c ⁻¹ᵁ U)
        (inf_eq_right.mpr hle).symm
  exact H.flip

/-- Local etale image geometry makes the full first kernel projection etale. -/
theorem first_etale [Etale (c ∣_ U)] : Etale (u ∣_ (c ⁻¹ᵁ U)) :=
  MorphismProperty.of_isPullback (kernel_isPullback f U).flip inferInstance

/-- Local integral image geometry makes the full first kernel projection integral. -/
theorem first_integral [IsIntegralHom (c ∣_ U)] : IsIntegralHom (u ∣_ (c ⁻¹ᵁ U)) :=
  MorphismProperty.of_isPullback (kernel_isPullback f U).flip inferInstance

/-- The full kernel image map restricted over the neighborhood is integral. -/
theorem image_integral [IsIntegralHom (c ∣_ U)] : IsIntegralHom ((u ≫ c) ∣_ U) := by
  let _ := first_integral f U
  rw [morphismRestrict_comp]
  infer_instance

end FLT.Mazur.SchemeScalarImageKernelNeighborhood
