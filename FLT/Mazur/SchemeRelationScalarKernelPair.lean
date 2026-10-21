/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationScalarMonomorphism

/-!
# Full scalar relation kernel pairs from geometric coverage

The canonical comparison's surjectivity promotes the whole scalar relation
to the actual image kernel pair. The constructed inverse preserves both
independent endpoints, so this result supplies full scheme descent diagrams.
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

/-- The isomorphism is the canonical comparison from the entire original scalar relation. -/
def kernelIso [JointlyMono₂ a b] [Etale a] [Etale c]
    [Surjective (kernelComparison a b f h ρ)] : relation a f ρ ≅ pullback c c := by
  let _ := kernelComparison_isIso a b f h ρ
  exact asIso (kernelComparison a b f h ρ)

/-- The inverse reconstructs the first full endpoint of each kernel arrow. -/
@[reassoc] theorem kernelIso_inv_first [JointlyMono₂ a b] [Etale a] [Etale c]
    [Surjective (kernelComparison a b f h ρ)] :
    (kernelIso a b f h ρ).inv ≫ first a f ρ = pullback.fst c c := by
  rw [← kernelComparison_first a b f h ρ]
  exact (kernelIso a b f h ρ).inv_hom_id_assoc _

/-- The inverse independently reconstructs the second full endpoint. -/
@[reassoc] theorem kernelIso_inv_second [JointlyMono₂ a b] [Etale a] [Etale c]
    [Surjective (kernelComparison a b f h ρ)] :
    (kernelIso a b f h ρ).inv ≫ second a b f h ρ = pullback.snd c c := by
  rw [← kernelComparison_second a b f h ρ]
  exact (kernelIso a b f h ρ).inv_hom_id_assoc _

/-- The original full scalar relation is the cartesian image-kernel diagram. -/
theorem image_isPullback [JointlyMono₂ a b] [Etale a] [Etale c]
    [Surjective (kernelComparison a b f h ρ)] : IsPullback (first a f ρ) (second a b f h ρ) c c :=
  IsPullback.of_iso_pullback ⟨image_condition a b f h ρ⟩ (kernelIso a b f h ρ)
    (kernelComparison_first a b f h ρ) (kernelComparison_second a b f h ρ)

end FLT.Mazur.SchemeRelationScalarBaseChange
