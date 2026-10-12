/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianNamedRefinement
public import FLT.Mazur.SheafPullbackRefinementLaw

/-!
# From coefficient refinement to test refinement

Transport the original quotient transition law to the geometric test pullbacks
without expanding the resulting concrete sheaf equation.
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
open SheafPullbackCoordinateRefinement SheafPullbackRefinementLaw
attribute [local irreducible] Scheme.Modules.pullback comparison coordinateMap
attribute [local irreducible] grassmannianQuotientSheaf grassmannianQuotientSheafTransition
variable {X : Scheme.{u}} (z : Spec (.of D) ⟶ X) (z' : Spec (.of E) ⟶ X)
variable (p : X ⟶ Spec (.of A)) (q : X ⟶ Spec (.of B))
variable (f : A →ₐ[R] D) (g : B →ₐ[R] D) (k : D →ₐ[R] E)
  (f' : A →ₐ[R] E) (g' : B →ₐ[R] E)
variable (hf : z ≫ p = Spec.map (CommRingCat.ofHom f.toRingHom))
  (hg : z ≫ q = Spec.map (CommRingCat.ofHom g.toRingHom))
  (hf' : z' ≫ p = Spec.map (CommRingCat.ofHom f'.toRingHom))
  (hg' : z' ≫ q = Spec.map (CommRingCat.ofHom g'.toRingHom))
  (hz : Spec.map (CommRingCat.ofHom k.toRingHom) ≫ z = z')
variable (wf : Spec.map (CommRingCat.ofHom k.toRingHom) ≫
  Spec.map (CommRingCat.ofHom f.toRingHom) = Spec.map (CommRingCat.ofHom f'.toRingHom))
  (wg : Spec.map (CommRingCat.ofHom k.toRingHom) ≫
  Spec.map (CommRingCat.ofHom g.toRingHom) = Spec.map (CommRingCat.ofHom g'.toRingHom))
variable (N : Module.Grassmannian A (A ⊗[R] M) d)
  (P : Module.Grassmannian B (B ⊗[R] M) d)
  (h : Module.Grassmannian.map f N = Module.Grassmannian.map g P)
  (h' : Module.Grassmannian.map f' N = Module.Grassmannian.map g' P)

/-- Named quotient coherence gives the original geometric refinement law on test maps. -/
theorem grassmannianCoordinateMap_refines
    (hr : grassmannianNamedTransitionRefines f g k f' g' N P h h' wf wg) :
    Refines (Spec.map (CommRingCat.ofHom k.toRingHom)) z z' hz
      (coordinateMap z p q _ _ hf hg (grassmannianQuotientSheafTransition f g N P h).hom)
      (coordinateMap z' p q _ _ hf' hg'
        (grassmannianQuotientSheafTransition f' g' N P h').hom) := by
  apply coordinate_refines _ z z' hz p q _ _ hf hg _ _ hf' hg' wf wg
  unfold grassmannianNamedTransitionRefines at hr
  rw [grassmannianNamedRefinementIso_eq, grassmannianNamedRefinementIso_eq] at hr
  exact hr

end FLT.Mazur.GrassmannianChart
