/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationScalarComparisonCover

/-!
# The full branch comparison is an original comparison pullback

Identify the scalar extension of the original kernel pair with the exact
branch image kernel pair. Transporting its original projection gives a
cartesian square for the full comparison, without assuming domination.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeRelationScalarBaseChange
set_option backward.isDefEq.respectTransparency false
variable {R S : Type} [CommRing R] [CommRing S] {D X : Scheme.{0}}
  (a b : D ⟶ X) (f : X ⟶ Spec (.of R)) (h : a ≫ f = b ≫ f)
  (ρ : R →+* S)
local notation "g" => Spec.map (CommRingCat.ofHom ρ)
local notation "c" => SchemeScalarImageQuotient.projection (pullback.snd f g)
local notation "u" => pullback.fst f f
local notation "v" => pullback.snd f f

/-- The whole exact branch kernel pair maps to the original scalar kernel pair. -/
def kernelOriginal : pullback c c ⟶ pullback f f := by
  let _ := kernelComparison_isIso_of_original u v f pullback.condition ρ
    (IsPullback.of_hasPullback f f)
  exact inv (kernelComparison u v f pullback.condition ρ) ≫ original u f ρ

/-- Transport to the branch kernel pair preserves the original projection. -/
@[reassoc] theorem kernelComparison_kernelOriginal :
    kernelComparison u v f pullback.condition ρ ≫ kernelOriginal f ρ =
      original u f ρ := by
  let _ := kernelComparison_isIso_of_original u v f pullback.condition ρ
    (IsPullback.of_hasPullback f f)
  simp only [kernelOriginal, IsIso.hom_inv_id_assoc]

/-- The full comparison square commutes over the unchanged original relation. -/
@[reassoc] theorem kernelComparison_original :
    kernelComparison a b f h ρ ≫ kernelOriginal f ρ =
      original a f ρ ≫ pullback.lift a b h := by
  rw [← comparisonExtension_kernelComparison, Category.assoc,
    kernelComparison_kernelOriginal, comparisonExtension_original]

/-- The full branch comparison itself is a base change of the original comparison. -/
theorem kernelComparison_isPullback :
    IsPullback (original a f ρ) (kernelComparison a b f h ρ)
      (pullback.lift a b h) (kernelOriginal f ρ) := by
  let _ := kernelComparison_isIso_of_original u v f pullback.condition ρ
    (IsPullback.of_hasPullback f f)
  have H : IsPullback (original u f ρ)
      (kernelComparison u v f pullback.condition ρ) (𝟙 _) (kernelOriginal f ρ) :=
    IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, kernelComparison_kernelOriginal]⟩
  simpa only [comparisonExtension_kernelComparison, Category.comp_id] using
    (comparisonExtension_isPullback a b f h ρ).paste_vert H

end FLT.Mazur.SchemeRelationScalarBaseChange
