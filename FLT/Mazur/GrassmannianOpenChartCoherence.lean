/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianOpenChartComparisons

/-!
# Coherence of actual Grassmannian subopen comparisons

An arbitrary morphism to the Grassmannian gives compatible quotient sheaves on
its affine open charts. The whole-overlap comparisons satisfy the geometric
refinement and cocycle hypotheses of module-sheaf gluing.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianOpenChartDescent
open GrassmannianChart GrassmannianOverlapAffineTransition
open ModuleSheafOpenImageChart SheafPullbackPathComparison
universe u
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)
variable {X : Scheme.{u}} (f : X ⟶ ambientGrassmannianScheme R M κ d)
variable {J : Type u} (A : J → Type u) [∀ j, CommRing (A j)] [∀ j, Algebra R (A j)]
  (i : ∀ j, Spec (.of (A j)) ⟶ X) [∀ j, IsOpenImmersion (i j)]
variable (a : ∀ j, {a : Spec (.of (A j)) ⟶ ambientGrassmannianScheme R M κ d //
  a ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R (A j)})
  (h : ∀ j, i j ≫ f = (a j).val)
attribute [local irreducible] Scheme.Modules.pullback grassmannianQuotientSheaf overlapIso

/-- The constructed comparisons restrict to the constructed comparison on every smaller open. -/
theorem subopenIso_refines (j k : J) (U V : X.Opens) (hv : V ≤ U)
    (hj : U ≤ (i j).opensRange) (hk : U ≤ (i k).opensRange) :
    (pullback (X.homOfLE hv)).map (subopenIso b hκ f (fun j ↦ .of (A j)) i a h j k U hj hk).hom ≫
        (comparison (X.homOfLE hv) (coordinate (i k) U hk)
          (coordinate (i k) V (hv.trans hk)) (coordinate_refine (i k) hv hk)).hom.app
            (grassmannianQuotientSheaf (ambientMorphismPoint (a k).val (a k).property)) =
      (comparison (X.homOfLE hv) (coordinate (i j) U hj)
          (coordinate (i j) V (hv.trans hj)) (coordinate_refine (i j) hv hj)).hom.app
            (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)) ≫
        (subopenIso b hκ f (fun j ↦ .of (A j)) i a h j k V (hv.trans hj) (hv.trans hk)).hom := by
  delta subopenIso
  exact overlapIso_refines b hκ (a j) (a k) _ _ _ (X.homOfLE hv) _ _
    (coordinate_refine (i j) hv hj) (coordinate_refine (i k) hv hk) _

/-- The actual quotient comparisons satisfy the cocycle on every common subopen. -/
theorem subopenIso_cocycle (j k l : J) (U : X.Opens)
    (hj : U ≤ (i j).opensRange) (hk : U ≤ (i k).opensRange) (hl : U ≤ (i l).opensRange) :
    (subopenIso b hκ f (fun j ↦ .of (A j)) i a h j k U hj hk).hom ≫
        (subopenIso b hκ f (fun j ↦ .of (A j)) i a h k l U hk hl).hom =
      (subopenIso b hκ f (fun j ↦ .of (A j)) i a h j l U hj hl).hom := by
  delta subopenIso
  exact overlapIso_cocycle b hκ (a j) (a k) (a l) _ _ _ _ _

end FLT.Mazur.GrassmannianOpenChartDescent
