/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianQuotientBaseChange

/-!
# Quotient-sheaf transitions on common affine refinements

Equality of the full functor-image relation gives an actual transition between
pulled-back quotient sheaves. Its normalization uses the ambient projection,
which determines the transition uniquely and proves the cocycle.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A B C D M : Type u} [CommRing R] [CommRing A] [CommRing B]
  [CommRing C] [CommRing D] [Algebra R A] [Algebra R B] [Algebra R C]
  [Algebra R D] [AddCommGroup M] [Module R M] {d : ℕ}

/-- Equal original points give an isomorphism of their actual quotient sheaves. -/
def grassmannianQuotientSheafCongr
    {N P : Module.Grassmannian A (A ⊗[R] M) d} (h : N = P) :
    grassmannianQuotientSheaf N ≅ grassmannianQuotientSheaf P :=
  eqToIso (congrArg grassmannianQuotientSheaf h)

/-- Equality transport retains the original projection, not just the quotient object. -/
@[reassoc] theorem grassmannianQuotientSheafCongr_projection
    {N P : Module.Grassmannian A (A ⊗[R] M) d} (h : N = P) :
    grassmannianQuotientSheafMap N ≫ (grassmannianQuotientSheafCongr h).hom =
      grassmannianQuotientSheafMap P := by
  subst P
  exact Category.comp_id _

variable (f : A →ₐ[R] D) (g : B →ₐ[R] D)
  (N : Module.Grassmannian A (A ⊗[R] M) d)
  (P : Module.Grassmannian B (B ⊗[R] M) d)
  (h : Module.Grassmannian.map f N = Module.Grassmannian.map g P)

/-- A common affine refinement identifies the two actual pulled-back quotients. -/
def grassmannianQuotientSheafTransition :
    (pullback (Spec.map (CommRingCat.ofHom f.toRingHom))).obj
        (grassmannianQuotientSheaf N) ≅
      (pullback (Spec.map (CommRingCat.ofHom g.toRingHom))).obj
        (grassmannianQuotientSheaf P) :=
  grassmannianQuotientSheafPullbackIso f N ≪≫ grassmannianQuotientSheafCongr h ≪≫
    (grassmannianQuotientSheafPullbackIso g P).symm

/-- The quotient projection pulled back and expressed in the common ambient sheaf. -/
def grassmannianRefinedQuotientMap :
    tilde (ModuleCat.of D (D ⊗[R] M)) ⟶
      (pullback (Spec.map (CommRingCat.ofHom f.toRingHom))).obj
        (grassmannianQuotientSheaf N) :=
  (grassmannianAmbientSheafPullbackIso f).inv ≫
    (pullback (Spec.map (CommRingCat.ofHom f.toRingHom))).map
      (grassmannianQuotientSheafMap N)

/-- The original full quotient remains epi on every common affine refinement. -/
instance grassmannianRefinedQuotientMap_epi : Epi (grassmannianRefinedQuotientMap f N) := by
  unfold grassmannianRefinedQuotientMap
  infer_instance

/-- The refined projection becomes the projection of the actual functor-image quotient. -/
@[reassoc] theorem grassmannianRefinedQuotientMap_comparison :
    grassmannianRefinedQuotientMap f N ≫ (grassmannianQuotientSheafPullbackIso f N).hom =
      grassmannianQuotientSheafMap (Module.Grassmannian.map f N) := by
  rw [grassmannianRefinedQuotientMap, Category.assoc,
    grassmannianQuotientSheafPullbackIso_projection, Iso.inv_hom_id_assoc]

/-- Transitions identify the two original ambient quotient projections. -/
@[reassoc] theorem grassmannianQuotientSheafTransition_projection :
    grassmannianRefinedQuotientMap f N ≫
        (grassmannianQuotientSheafTransition f g N P h).hom =
      grassmannianRefinedQuotientMap g P := by
  apply (cancel_mono (grassmannianQuotientSheafPullbackIso g P).hom).mp
  simp only [grassmannianQuotientSheafTransition, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, grassmannianRefinedQuotientMap_comparison,
    grassmannianQuotientSheafCongr_projection, grassmannianRefinedQuotientMap_comparison]

/-- Agreement on the ambient projection uniquely determines a quotient-sheaf transition. -/
theorem grassmannianQuotientSheafTransition_unique
    (a : (pullback (Spec.map (CommRingCat.ofHom f.toRingHom))).obj
        (grassmannianQuotientSheaf N) ⟶
      (pullback (Spec.map (CommRingCat.ofHom g.toRingHom))).obj
        (grassmannianQuotientSheaf P))
    (ha : grassmannianRefinedQuotientMap f N ≫ a = grassmannianRefinedQuotientMap g P) :
    a = (grassmannianQuotientSheafTransition f g N P h).hom := by
  apply (cancel_epi (grassmannianRefinedQuotientMap f N)).mp
  exact ha.trans (grassmannianQuotientSheafTransition_projection f g N P h).symm

/-- The actual transition cocycle follows through the epi ambient quotient projection. -/
@[reassoc] theorem grassmannianQuotientSheafTransition_cocycle (k : C →ₐ[R] D)
    (Q : Module.Grassmannian C (C ⊗[R] M) d)
    (h' : Module.Grassmannian.map g P = Module.Grassmannian.map k Q) :
    (grassmannianQuotientSheafTransition f g N P h).hom ≫
        (grassmannianQuotientSheafTransition g k P Q h').hom =
      (grassmannianQuotientSheafTransition f k N Q (h.trans h')).hom := by
  apply grassmannianQuotientSheafTransition_unique
  rw [← Category.assoc, grassmannianQuotientSheafTransition_projection,
    grassmannianQuotientSheafTransition_projection]

end FLT.Mazur.GrassmannianChart
