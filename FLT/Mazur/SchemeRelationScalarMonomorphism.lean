/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationScalarEtale
public import Mathlib.CategoryTheory.EquivalenceRelation
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-!
# The full scalar relation embeds in the image kernel pair

Joint monicity of the original endpoints survives full scalar base change.
Consequently the canonical comparison is a monomorphism; when the original
endpoint and exact image projection are etale, it is an open immersion.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeRelationScalarBaseChange
set_option backward.isDefEq.respectTransparency false
variable {R S : Type} [CommRing R] [CommRing S] {D X : Scheme.{0}}
  (a b : D ⟶ X) (f : X ⟶ Spec (.of R)) (h : a ≫ f = b ≫ f)
  (ρ : R →+* S) [JointlyMono₂ a b]
local notation "g" => Spec.map (CommRingCat.ofHom ρ)
local notation "c" => SchemeScalarImageQuotient.projection (pullback.snd f g)

/-- The full new endpoints detect arrows using the original jointly monic relation. -/
instance endpoints_jointlyMono : JointlyMono₂ (first a f ρ) (second a b f h ρ) where
  right_cancellation := by
    intro Y u v hu hv
    apply pullback.hom_ext
    · apply JointlyMono₂.right_cancellation (p₁ := a) (p₂ := b)
      · simpa only [Category.assoc, first_original, original] using
          congrArg (fun k ↦ k ≫ pullback.fst f g) hu
      · simpa only [Category.assoc, second_original, original] using
          congrArg (fun k ↦ k ≫ pullback.fst f g) hv
    · simpa only [Category.assoc, first, pullback.lift_snd] using
        congrArg (fun k ↦ k ≫ pullback.snd f g) hu

/-- No new relation arrows are identified by the exact image-kernel comparison. -/
instance kernelComparison_mono : Mono (kernelComparison a b f h ρ) where
  right_cancellation := by
    intro Y u v huv
    apply JointlyMono₂.right_cancellation (p₁ := first a f ρ) (p₂ := second a b f h ρ)
    · simpa only [Category.assoc, kernelComparison_first] using
        congrArg (fun k ↦ k ≫ pullback.fst c c) huv
    · simpa only [Category.assoc, kernelComparison_second] using
        congrArg (fun k ↦ k ≫ pullback.snd c c) huv

/-- The whole relation is an actual open subscheme of the full kernel pair. -/
theorem kernelComparison_isOpenImmersion [Etale a] [Etale c] :
    IsOpenImmersion (kernelComparison a b f h ρ) := by
  let _ := kernelComparison_etale a b f h ρ
  exact IsOpenImmersion.of_flat_of_mono _

/-- Surjectivity of this open immersion identifies the full relation scheme. -/
theorem kernelComparison_isIso [Etale a] [Etale c]
    [Surjective (kernelComparison a b f h ρ)] : IsIso (kernelComparison a b f h ρ) := by
  let _ := kernelComparison_isOpenImmersion a b f h ρ
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩

end FLT.Mazur.SchemeRelationScalarBaseChange
