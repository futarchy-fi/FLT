/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarImageQuotient

/-!
# Full scalar base change of a scheme relation

Both endpoints and the map to the exact scalar-image kernel pair are
constructed geometrically. The relation domain is the entire scalar pullback,
with no reduction, component selection or assumed kernel-pair domination.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeRelationScalarBaseChange
set_option backward.isDefEq.respectTransparency false
variable {R S : Type} [CommRing R] [CommRing S] {D X : Scheme.{0}}
  (a b : D ⟶ X) (f : X ⟶ Spec (.of R)) (h : a ≫ f = b ≫ f)
  (ρ : R →+* S)
local notation "g" => Spec.map (CommRingCat.ofHom ρ)

/-- The entire original relation after changing the scalar base. -/
def relation : Scheme := pullback (a ≫ f) g

/-- Its map to the unchanged original relation. -/
def original : relation a f ρ ⟶ D := pullback.fst _ _

/-- The first endpoint on the full source pullback. -/
def first : relation a f ρ ⟶ pullback f g :=
  pullback.lift (original a f ρ ≫ a) (pullback.snd _ _) (by
    rw [Category.assoc]
    exact pullback.condition)

/-- The independent second endpoint uses the original coequalizing equation. -/
def second : relation a f ρ ⟶ pullback f g :=
  pullback.lift (original a f ρ ≫ b) (pullback.snd _ _) (by
    rw [Category.assoc, ← h]
    exact pullback.condition)

/-- First endpoints recover the literal original arrow. -/
@[reassoc] theorem first_original :
    first a f ρ ≫ pullback.fst f g = original a f ρ ≫ a := pullback.lift_fst _ _ _

/-- Second endpoints recover the independent literal original arrow. -/
@[reassoc] theorem second_original :
    second a b f h ρ ≫ pullback.fst f g = original a f ρ ≫ b := pullback.lift_fst _ _ _

/-- Both full endpoints have the same new scalar coordinate. -/
theorem scalar_condition :
    first a f ρ ≫ pullback.snd f g = second a b f h ρ ≫ pullback.snd f g := by
  exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm

/-- Both endpoints also have the same coordinate in the constructed exact scalar image. -/
theorem image_condition :
    first a f ρ ≫ SchemeScalarImageQuotient.projection (pullback.snd f g) =
      second a b f h ρ ≫ SchemeScalarImageQuotient.projection (pullback.snd f g) :=
  (SchemeScalarImageQuotient.projection_eq_iff _ _ _).mpr (scalar_condition a b f h ρ)

/-- The comparison to the entire image kernel pair is canonical. -/
def kernelComparison : relation a f ρ ⟶
    pullback (SchemeScalarImageQuotient.projection (pullback.snd f g))
      (SchemeScalarImageQuotient.projection (pullback.snd f g)) :=
  pullback.lift (first a f ρ) (second a b f h ρ) (image_condition a b f h ρ)

/-- The comparison's first coordinate preserves the original relation. -/
@[reassoc] theorem kernelComparison_first :
    kernelComparison a b f h ρ ≫ pullback.fst _ _ = first a f ρ := pullback.lift_fst _ _ _

/-- The comparison's second coordinate preserves the original relation. -/
@[reassoc] theorem kernelComparison_second :
    kernelComparison a b f h ρ ≫ pullback.snd _ _ = second a b f h ρ := pullback.lift_snd _ _ _

end FLT.Mazur.SchemeRelationScalarBaseChange
