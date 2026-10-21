/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationScalarCartesian

/-!
# Original comparison coverage survives full scalar extension

The full relation map to the original scalar kernel pair has a cartesian
scalar extension. The extended original kernel pair identifies with the exact
new image kernel pair, so original coverage supplies full branch coverage.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeRelationScalarBaseChange
set_option backward.isDefEq.respectTransparency false
variable {R S : Type} [CommRing R] [CommRing S] {D X : Scheme.{0}}
  (a b : D ⟶ X) (f : X ⟶ Spec (.of R)) (h : a ≫ f = b ≫ f)
  (ρ : R →+* S)
local notation "g" => Spec.map (CommRingCat.ofHom ρ)
local notation "k" => pullback.lift a b h
local notation "u" => pullback.fst f f
local notation "v" => pullback.snd f f

/-- The entire relation extends to the scalar extension of its original full kernel pair. -/
def comparisonExtension : relation a f ρ ⟶ relation u f ρ :=
  pullback.lift (original a f ρ ≫ k) (pullback.snd (a ≫ f) g) (by
    simp only [Category.assoc, pullback.lift_fst_assoc]
    exact pullback.condition)

/-- Extension retains the literal original comparison. -/
@[reassoc] theorem comparisonExtension_original :
    comparisonExtension a b f h ρ ≫ original u f ρ = original a f ρ ≫ k :=
  pullback.lift_fst _ _ _

/-- The original full relation comparison extends cartesianly. -/
theorem comparisonExtension_isPullback :
    IsPullback (original a f ρ) (comparisonExtension a b f h ρ) k (original u f ρ) := by
  apply IsPullback.of_bot _ (comparisonExtension_original a b f h ρ).symm
    (IsPullback.of_hasPullback (u ≫ f) g)
  simpa only [comparisonExtension, pullback.lift_snd, pullback.lift_fst_assoc, original]
    using IsPullback.of_hasPullback (a ≫ f) g

/-- Comparing the extended original kernel pair recovers the exact branch image comparison. -/
theorem comparisonExtension_kernelComparison :
    comparisonExtension a b f h ρ ≫ kernelComparison u v f pullback.condition ρ =
      kernelComparison a b f h ρ := by
  apply pullback.hom_ext
  · rw [Category.assoc, kernelComparison_first, kernelComparison_first]
    apply pullback.hom_ext
    · simp only [Category.assoc, first_original, comparisonExtension_original_assoc,
        pullback.lift_fst]
    · simp only [Category.assoc, first, pullback.lift_snd, comparisonExtension]
  · rw [Category.assoc, kernelComparison_second, kernelComparison_second]
    apply pullback.hom_ext
    · simp only [Category.assoc, second_original, comparisonExtension_original_assoc,
        pullback.lift_snd]
    · simp only [Category.assoc, second, pullback.lift_snd, comparisonExtension]

/-- Full original kernel-pair coverage covers the exact branch kernel pair. -/
theorem kernelComparison_surjective_of_original [Surjective (pullback.lift a b h)] :
    Surjective (kernelComparison a b f h ρ) := by
  let _ : Surjective (comparisonExtension a b f h ρ) :=
    MorphismProperty.of_isPullback (comparisonExtension_isPullback a b f h ρ) inferInstance
  let _ := kernelComparison_isIso_of_original u v f pullback.condition ρ
    (IsPullback.of_hasPullback f f)
  rw [← comparisonExtension_kernelComparison a b f h ρ]
  infer_instance

end FLT.Mazur.SchemeRelationScalarBaseChange
