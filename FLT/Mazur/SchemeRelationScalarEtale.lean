/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationScalarBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Geometric domination for full scalar relation comparisons

The first new endpoint is an actual base change of the original first endpoint.
For an etale original relation and an etale full scalar-image projection, the
canonical kernel comparison is etale. Surjectivity then supplies effective
domination, including all structure sheaf equations.
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

/-- The full first endpoint square is cartesian over the unchanged original source. -/
theorem first_isPullback :
    IsPullback (original a f ρ) (first a f ρ) a (pullback.fst f g) := by
  apply IsPullback.of_bot ?_ (first_original a f ρ).symm (IsPullback.of_hasPullback f g)
  simpa only [first, pullback.lift_snd, original] using
    (IsPullback.of_hasPullback (a ≫ f) g)

/-- Etaleness comes from the original endpoint, without any boundary reduction. -/
instance first_etale [Etale a] : Etale (first a f ρ) :=
  MorphismProperty.of_isPullback (first_isPullback a f ρ) (inferInstanceAs (Etale a))

/-- An etale full scalar-image projection makes the canonical kernel comparison etale. -/
theorem kernelComparison_etale [Etale a] [Etale c] :
    Etale (kernelComparison a b f h ρ) := by
  have : Etale (kernelComparison a b f h ρ ≫ pullback.fst c c) := by
    rw [kernelComparison_first]
    infer_instance
  exact Etale.of_comp _ (pullback.fst c c)

/-- Actual surjectivity of the constructed etale comparison supplies effective domination. -/
theorem kernelComparison_effectiveEpi [Etale a] [Etale c]
    [Surjective (kernelComparison a b f h ρ)] : EffectiveEpi (kernelComparison a b f h ρ) := by
  let _ := kernelComparison_etale a b f h ρ
  infer_instance

end FLT.Mazur.SchemeRelationScalarBaseChange
