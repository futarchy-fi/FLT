/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianTransitionRefinement
public import FLT.Mazur.SheafPullbackPathComparison

/-!
# Quotient transition refinement with named coordinate maps

Affine tests carry coordinate maps recovered from their geometric paths.
Those maps equal composites without being syntactically composites. This
form of refinement retains the specified scheme pullback comparisons.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
open SheafPullbackPathComparison
universe u
variable {R A B D E M : Type u} [CommRing R] [CommRing A] [CommRing B]
  [CommRing D] [CommRing E] [Algebra R A] [Algebra R B] [Algebra R D]
  [Algebra R E] [AddCommGroup M] [Module R M] {d : ℕ}
attribute [local irreducible] Scheme.Modules.pullback comparison pullbackComp pullbackCongr
attribute [local irreducible] grassmannianQuotientSheaf grassmannianQuotientSheafTransition

/-- A sealed natural comparison for a specified coefficient path. -/
@[irreducible] def grassmannianNamedRefinement
    (f : A →ₐ[R] D) (k : D →ₐ[R] E) (f' : A →ₐ[R] E)
    (wf : Spec.map (CommRingCat.ofHom k.toRingHom) ≫
      Spec.map (CommRingCat.ofHom f.toRingHom) = Spec.map (CommRingCat.ofHom f'.toRingHom)) :
    pullback (Spec.map (CommRingCat.ofHom f.toRingHom)) ⋙
      pullback (Spec.map (CommRingCat.ofHom k.toRingHom)) ≅
        pullback (Spec.map (CommRingCat.ofHom f'.toRingHom)) :=
  pullbackComp (Spec.map (CommRingCat.ofHom k.toRingHom))
    (Spec.map (CommRingCat.ofHom f.toRingHom)) ≪≫ pullbackCongr wf

/-- Evaluation of the named natural comparison at an original sheaf. -/
@[irreducible] def grassmannianNamedRefinementIso
    (f : A →ₐ[R] D) (k : D →ₐ[R] E) (f' : A →ₐ[R] E)
    (wf : Spec.map (CommRingCat.ofHom k.toRingHom) ≫
      Spec.map (CommRingCat.ofHom f.toRingHom) = Spec.map (CommRingCat.ofHom f'.toRingHom))
    (F : (Spec (.of A)).Modules) :
    (pullback (Spec.map (CommRingCat.ofHom k.toRingHom))).obj
        ((pullback (Spec.map (CommRingCat.ofHom f.toRingHom))).obj F) ≅
      (pullback (Spec.map (CommRingCat.ofHom f'.toRingHom))).obj F :=
  (grassmannianNamedRefinement f k f' wf).app F

/-- For composite coordinates, the named natural comparison is the existing refinement. -/
theorem grassmannianNamedRefinement_comp (f : A →ₐ[R] D) (k : D →ₐ[R] E)
    (wf : Spec.map (CommRingCat.ofHom k.toRingHom) ≫
      Spec.map (CommRingCat.ofHom f.toRingHom) =
        Spec.map (CommRingCat.ofHom (k.comp f).toRingHom)) :
    grassmannianNamedRefinement f k (k.comp f) wf = grassmannianRefinementNatIso f k := by
  unfold grassmannianNamedRefinement grassmannianRefinementNatIso
  rfl

/-- Evaluating a composite named comparison gives the original comparison on sheaves. -/
theorem grassmannianNamedRefinementIso_comp (f : A →ₐ[R] D) (k : D →ₐ[R] E)
    (wf : Spec.map (CommRingCat.ofHom k.toRingHom) ≫
      Spec.map (CommRingCat.ofHom f.toRingHom) =
        Spec.map (CommRingCat.ofHom (k.comp f).toRingHom))
    (F : (Spec (.of A)).Modules) :
    grassmannianNamedRefinementIso f k (k.comp f) wf F = grassmannianRefinementIso f k F := by
  unfold grassmannianNamedRefinementIso grassmannianRefinementIso
  rw [grassmannianNamedRefinement_comp]

/-- The named comparison is the canonical scheme path comparison. -/
theorem grassmannianNamedRefinementIso_eq (f : A →ₐ[R] D) (k : D →ₐ[R] E)
    (f' : A →ₐ[R] E)
    (wf : Spec.map (CommRingCat.ofHom k.toRingHom) ≫
      Spec.map (CommRingCat.ofHom f.toRingHom) = Spec.map (CommRingCat.ofHom f'.toRingHom))
    (F : (Spec (.of A)).Modules) :
    grassmannianNamedRefinementIso f k f' wf F =
      (comparison (Spec.map (CommRingCat.ofHom k.toRingHom))
        (Spec.map (CommRingCat.ofHom f.toRingHom))
        (Spec.map (CommRingCat.ofHom f'.toRingHom)) wf).app F := by
  unfold grassmannianNamedRefinementIso grassmannianNamedRefinement comparison
  rfl

/-- The actual refinement equation for two specified coefficient coordinates. -/
@[irreducible] def grassmannianNamedTransitionRefines
    (f : A →ₐ[R] D) (g : B →ₐ[R] D) (k : D →ₐ[R] E)
    (f' : A →ₐ[R] E) (g' : B →ₐ[R] E)
    (N : Module.Grassmannian A (A ⊗[R] M) d)
    (P : Module.Grassmannian B (B ⊗[R] M) d)
    (h : Module.Grassmannian.map f N = Module.Grassmannian.map g P)
    (h' : Module.Grassmannian.map f' N = Module.Grassmannian.map g' P)
    (wf : Spec.map (CommRingCat.ofHom k.toRingHom) ≫
      Spec.map (CommRingCat.ofHom f.toRingHom) = Spec.map (CommRingCat.ofHom f'.toRingHom))
    (wg : Spec.map (CommRingCat.ofHom k.toRingHom) ≫
      Spec.map (CommRingCat.ofHom g.toRingHom) = Spec.map (CommRingCat.ofHom g'.toRingHom)) :
    Prop :=
  (pullback (Spec.map (CommRingCat.ofHom k.toRingHom))).map
        (grassmannianQuotientSheafTransition f g N P h).hom ≫
      (grassmannianNamedRefinementIso g k g' wg (grassmannianQuotientSheaf P)).hom =
    (grassmannianNamedRefinementIso f k f' wf (grassmannianQuotientSheaf N)).hom ≫
      (grassmannianQuotientSheafTransition f' g' N P h').hom

/-- The original transition refinement holds for all equal named coordinate maps. -/
theorem grassmannianNamedTransitionRefines_of_eq
    (f : A →ₐ[R] D) (g : B →ₐ[R] D) (k : D →ₐ[R] E)
    (f' : A →ₐ[R] E) (g' : B →ₐ[R] E) (hf : k.comp f = f') (hg : k.comp g = g')
    (N : Module.Grassmannian A (A ⊗[R] M) d)
    (P : Module.Grassmannian B (B ⊗[R] M) d)
    (h : Module.Grassmannian.map f N = Module.Grassmannian.map g P)
    (h' : Module.Grassmannian.map f' N = Module.Grassmannian.map g' P)
    (wf : Spec.map (CommRingCat.ofHom k.toRingHom) ≫
      Spec.map (CommRingCat.ofHom f.toRingHom) = Spec.map (CommRingCat.ofHom f'.toRingHom))
    (wg : Spec.map (CommRingCat.ofHom k.toRingHom) ≫
      Spec.map (CommRingCat.ofHom g.toRingHom) = Spec.map (CommRingCat.ofHom g'.toRingHom)) :
    grassmannianNamedTransitionRefines f g k f' g' N P h h' wf wg := by
  subst f' g'
  unfold grassmannianNamedTransitionRefines
  rw [grassmannianNamedRefinementIso_comp, grassmannianNamedRefinementIso_comp]
  exact grassmannianQuotientSheafTransition_refine f g k N P h

/-- Refinement compatibility uses any equal named coefficient paths and their scheme squares. -/
theorem grassmannianQuotientSheafTransition_refine_of_eq
    (f : A →ₐ[R] D) (g : B →ₐ[R] D) (k : D →ₐ[R] E)
    (f' : A →ₐ[R] E) (g' : B →ₐ[R] E) (hf : k.comp f = f') (hg : k.comp g = g')
    (N : Module.Grassmannian A (A ⊗[R] M) d)
    (P : Module.Grassmannian B (B ⊗[R] M) d)
    (h : Module.Grassmannian.map f N = Module.Grassmannian.map g P)
    (h' : Module.Grassmannian.map f' N = Module.Grassmannian.map g' P)
    (wf : Spec.map (CommRingCat.ofHom k.toRingHom) ≫
      Spec.map (CommRingCat.ofHom f.toRingHom) = Spec.map (CommRingCat.ofHom f'.toRingHom))
    (wg : Spec.map (CommRingCat.ofHom k.toRingHom) ≫
      Spec.map (CommRingCat.ofHom g.toRingHom) = Spec.map (CommRingCat.ofHom g'.toRingHom)) :
    (pullback (Spec.map (CommRingCat.ofHom k.toRingHom))).map
        (grassmannianQuotientSheafTransition f g N P h).hom ≫
      (comparison (Spec.map (CommRingCat.ofHom k.toRingHom))
        (Spec.map (CommRingCat.ofHom g.toRingHom))
        (Spec.map (CommRingCat.ofHom g'.toRingHom)) wg).hom.app (grassmannianQuotientSheaf P) =
    (comparison (Spec.map (CommRingCat.ofHom k.toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom f'.toRingHom)) wf).hom.app (grassmannianQuotientSheaf N) ≫
      (grassmannianQuotientSheafTransition f' g' N P h').hom := by
  have ht := grassmannianNamedTransitionRefines_of_eq f g k f' g' hf hg N P h h' wf wg
  unfold grassmannianNamedTransitionRefines at ht
  rw [grassmannianNamedRefinementIso_eq, grassmannianNamedRefinementIso_eq] at ht
  exact ht

end FLT.Mazur.GrassmannianChart
