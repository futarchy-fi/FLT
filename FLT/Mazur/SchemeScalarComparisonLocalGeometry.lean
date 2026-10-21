/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeComparisonLocalClosedObstruction
public import FLT.Mazur.SchemeScalarImageKernelNeighborhood
public import FLT.Mazur.SchemePullbackThroughOpen

/-!
# Full scalar comparison geometry on original image neighborhoods

Etale integral geometry on one original image open closes the local missed
comparison image. Coverage of a whole original fiber produces a smaller open
with the same image geometry and surjective full comparison.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarComparisonLocalGeometry
open SchemeScalarImageQuotient SchemeComparisonCoverageLocus
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {D X : Scheme.{0}}
  (f : X ⟶ Spec (.of R)) (a b : D ⟶ X) (h : a ≫ f = b ≫ f)
  (U : (Spec (.of (Scalars f))).Opens)
local notation "c" => projection f
local notation "u" => pullback.fst f f
local notation "k" => pullback.lift a b h
local notation "m" => u ≫ c

/-- The comparison restricted over a local etale image is etale. -/
theorem comparison_etale [Etale a] [Etale (c ∣_ U)] : Etale (k ∣_ (m ⁻¹ᵁ U)) := by
  change Etale (k ∣_ (u ⁻¹ᵁ (c ⁻¹ᵁ U)))
  let _ := SchemeScalarImageKernelNeighborhood.first_etale f U
  let _ : Etale (k ≫ u) := by rw [pullback.lift_fst]; infer_instance
  let _ : Etale ((k ∣_ (u ⁻¹ᵁ (c ⁻¹ᵁ U))) ≫ (u ∣_ (c ⁻¹ᵁ U))) := by
    simpa only [morphismRestrict_comp] using
      (inferInstance : Etale ((k ≫ u) ∣_ (c ⁻¹ᵁ U)))
  exact Etale.of_comp _ (u ∣_ (c ⁻¹ᵁ U))

/-- A monic full comparison is open over the original etale image neighborhood. -/
theorem comparison_isOpenImmersion [Etale a] [Etale (c ∣_ U)] [Mono k] :
    IsOpenImmersion (k ∣_ (m ⁻¹ᵁ U)) := by
  let _ := comparison_etale f a b h U
  let _ := (isPullback_morphismRestrict k (m ⁻¹ᵁ U)).mono_fst_of_mono
  exact IsOpenImmersion.of_flat_of_mono _

/-- Only neighborhood integral geometry is needed to close the local obstruction. -/
theorem missedImage_isClosed [Etale a] [Etale (c ∣_ U)] [IsIntegralHom (c ∣_ U)]
    [Mono k] : IsClosed ((m ∣_ U) '' (Set.range (k ∣_ (m ⁻¹ᵁ U)))ᶜ) := by
  let _ := comparison_isOpenImmersion f a b h U
  let _ := SchemeScalarImageKernelNeighborhood.image_integral f U
  exact SchemeComparisonCoverageLocus.missedImage_isClosed _ _

/-- Any base-change stable image property survives shrinking the original neighborhood. -/
theorem restrict_property_of_le {Y Z : Scheme.{0}} (g : Y ⟶ Z) {V W : Z.Opens}
    (hVW : V ≤ W) (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange]
    (hP : P (g ∣_ W)) : P (g ∣_ V) :=
  SchemePullbackThroughOpen.property (isPullback_morphismRestrict g V).flip W
    (Z.homOfLE hVW) (Z.homOfLE_ι hVW) P hP

/-- Full original fiber coverage constructs a smaller etale integral comparison neighborhood. -/
theorem exists_neighborhood [Etale a] [Etale (c ∣_ U)] [IsIntegralHom (c ∣_ U)] [Mono k]
    (z : Spec (.of (Scalars f))) (hzU : z ∈ U)
    (hz : ∀ w : (pullback f f : Scheme), m w = z → w ∈ Set.range k) :
    ∃ V : (Spec (.of (Scalars f))).Opens, V ≤ U ∧ z ∈ V ∧
      Etale (c ∣_ V) ∧ IsIntegralHom (c ∣_ V) ∧ Surjective (k ∣_ (m ⁻¹ᵁ V)) := by
  obtain ⟨V, hVU, hzV, hV⟩ := exists_neighborhood_of_local_fiber_coverage k m U
    (missedImage_isClosed f a b h U) z hzU hz
  exact ⟨V, hVU, hzV, restrict_property_of_le c hVU (@Etale) inferInstance,
    restrict_property_of_le c hVU (@IsIntegralHom) inferInstance, hV⟩

end FLT.Mazur.SchemeScalarComparisonLocalGeometry
