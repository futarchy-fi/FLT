/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianQuotientRefinement

/-!
# Compatibility of quotient-sheaf transitions with affine refinement

The transition on a common affine refinement pulls back to the transition on
any further coefficient refinement. The proof retains the full quotient and
uses its original epi projection, so it needs no flatness assumption.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A B D E M : Type u} [CommRing R] [CommRing A] [CommRing B]
  [CommRing D] [CommRing E] [Algebra R A] [Algebra R B] [Algebra R D]
  [Algebra R E] [AddCommGroup M] [Module R M] {d : ℕ}
variable (f : A →ₐ[R] D) (g : B →ₐ[R] D) (k : D →ₐ[R] E)
  (N : Module.Grassmannian A (A ⊗[R] M) d)
  (P : Module.Grassmannian B (B ⊗[R] M) d)
  (h : Module.Grassmannian.map f N = Module.Grassmannian.map g P)

include h in
/-- Equality of full quotient relations persists under every further coefficient map. -/
theorem grassmannianCommonRefinement_eq :
    Module.Grassmannian.map (k.comp f) N = Module.Grassmannian.map (k.comp g) P := by
  rw [Module.Grassmannian.map_comp, Module.Grassmannian.map_comp, h]

attribute [local irreducible] grassmannianRefinedQuotientMap grassmannianRefinementIso
attribute [local irreducible] grassmannianQuotientSheafTransition Scheme.Modules.pullback
attribute [local irreducible] grassmannianAmbientSheafPullbackIso grassmannianQuotientSheaf

/-- Actual quotient transitions commute with successive affine refinement. -/
@[reassoc] theorem grassmannianQuotientSheafTransition_refine :
    (pullback (Spec.map (CommRingCat.ofHom k.toRingHom))).map
        (grassmannianQuotientSheafTransition f g N P h).hom ≫
      (grassmannianRefinementIso g k (grassmannianQuotientSheaf P)).hom =
    (grassmannianRefinementIso f k (grassmannianQuotientSheaf N)).hom ≫
      (grassmannianQuotientSheafTransition (k.comp f) (k.comp g) N P
        (grassmannianCommonRefinement_eq f g k N P h)).hom := by
  apply QuotientRefinementCoherence.transition_refine
    (pullback (Spec.map (CommRingCat.ofHom k.toRingHom)))
    (grassmannianRefinedQuotientMap f N) (grassmannianRefinedQuotientMap g P)
    (grassmannianQuotientSheafTransition f g N P h).hom
    (grassmannianAmbientSheafPullbackIso (M := M) k).inv
    (grassmannianRefinementIso f k (grassmannianQuotientSheaf N)).hom
    (grassmannianRefinementIso g k (grassmannianQuotientSheaf P)).hom
    (grassmannianRefinedQuotientMap (k.comp f) N)
    (grassmannianRefinedQuotientMap (k.comp g) P)
  · exact grassmannianQuotientSheafTransition_projection f g N P h
  · exact grassmannianRefinedQuotientMap_refine f k N
  · exact grassmannianRefinedQuotientMap_refine g k P
  · exact grassmannianQuotientSheafTransition_projection _ _ _ _ _

end FLT.Mazur.GrassmannianChart
