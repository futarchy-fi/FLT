/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.EquivalenceRelation

/-!
# The full finite relation is closed in the endpoint product

Joint monicity retains every arrow of the original relation. Finiteness of
its first projection, together with separatedness of the base, makes the
endpoint map a closed immersion and its affine section map surjective.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteRelationEndpointImmersion
universe u
variable {D A S : Scheme.{u}} (p q : D ⟶ A) (f : A ⟶ S)
  (h : p ≫ f = q ≫ f) (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- The two endpoints jointly embed the whole original relation. -/
theorem endpoint_mono : Mono (pullback.lift p q h) := by
  constructor
  intro T a b hab
  apply e.toJointlyMono₂.right_cancellation a b
  · simpa only [Category.assoc, pullback.lift_fst] using
      congrArg (fun k ↦ k ≫ pullback.fst f f) hab
  · simpa only [Category.assoc, pullback.lift_snd] using
      congrArg (fun k ↦ k ≫ pullback.snd f f) hab

/-- Full first-projection finiteness makes the endpoint map finite. -/
theorem endpoint_finite [IsFinite p] [IsSeparated f] :
    IsFinite (pullback.lift p q h) := by
  let _ : IsFinite (pullback.lift p q h ≫ pullback.fst f f) := by
    simpa only [pullback.lift_fst] using inferInstanceAs (IsFinite p)
  exact IsFinite.of_comp _ (pullback.fst f f)

include e in
/-- No chosen relation chart is substituted for the full endpoint image. -/
theorem endpoint_closed [IsFinite p] [IsSeparated f] :
    IsClosedImmersion (pullback.lift p q h) :=
  (IsClosedImmersion.iff_isFinite_and_mono _).mpr
    ⟨endpoint_finite p q f h, endpoint_mono p q f h e⟩

include e in
/-- Every full-relation function extends to the affine endpoint product. -/
theorem endpoint_appTop_surjective [IsFinite p] [IsSeparated f]
    [IsAffine A] [IsAffine S] :
    Function.Surjective (pullback.lift p q h).appTop := by
  let _ := endpoint_closed p q f h e
  exact Scheme.Hom.app_surjective (pullback.lift p q h) ⊤
    (isAffineOpen_top _)

end FLT.Mazur.FiniteRelationEndpointImmersion
