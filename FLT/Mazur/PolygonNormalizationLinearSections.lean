/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleDirectImageHZero
public import FLT.Mazur.PolygonNormalizationSectionFamilies

/-!
# Linear normalization component families

The actual normalization H0 is linearly the product of the actual component H0
spaces. This works for arbitrary coefficients and preserves geometric restriction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

universe u

namespace FLT.Mazur.PolygonNormalizationLinearSections

open FCurve PolygonPinching LinePullbackRestriction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type u) [Field K] (n : ℕ) {C : Over (Spec (.of K))}
  (p : components K n ⟶ C) (L : C.left.Modules)

/-- The original component coefficient, before choosing any trivialization. -/
abbrev componentLine (i : Fin n) :=
  (Scheme.Modules.pullback (componentι K n i ≫ p).left).obj L

/-- Restriction to all components as a map of vector spaces over the original field. -/
def componentMap : ModuleScalarH C.hom ((pushforward p.left).obj
    ((Scheme.Modules.pullback p.left).obj L)) 0 →ₗ[K]
      (∀ i : Fin n, ModuleScalarH (component K).hom (componentLine K n p L i) 0) :=
  LinearMap.pi fun i ↦
    (moduleDirectImageH0Equiv (componentι K n i ≫ p).left C.hom (component K).hom
      (componentι K n i ≫ p).w (componentLine K n p L i)).toLinearMap.comp
        (moduleScalarHMap C.hom
          (sealedAlong (componentι K n i).left p.left (componentι K n i ≫ p).left rfl L) 0)

/-- Each coordinate is the actual sealed geometric restriction on sections. -/
theorem componentMap_sections
    (x : ModuleScalarH C.hom ((pushforward p.left).obj ((Scheme.Modules.pullback p.left).obj L)) 0)
    (i : Fin n) :
    moduleScalarH0Equiv (component K).hom (componentLine K n p L i)
        (componentMap K n p L x i) =
      (sealedAlong (componentι K n i).left p.left (componentι K n i ≫ p).left rfl L).app ⊤
        (moduleScalarH0Equiv C.hom _ x) := by
  change moduleScalarH0Equiv _ _ (moduleDirectImageH0Equiv _ _ _ (componentι K n i ≫ p).w _ _) = _
  rw [moduleDirectImageH0Equiv_sections, moduleScalarH0Equiv_naturality]

/-- Component H0 classes can be prescribed independently, uniquely and linearly. -/
theorem componentMap_bijective : Function.Bijective (componentMap K n p L) := by
  let e i := (moduleScalarH0Equiv (component K).hom (componentLine K n p L i)).toEquiv
  have hb := (Function.Bijective.piMap (fun i ↦ (e i).symm.bijective)).comp
    ((PolygonPowerBranchValues.componentRestriction_bijective K n p L).comp
      (moduleScalarH0Equiv C.hom
        ((pushforward p.left).obj ((Scheme.Modules.pullback p.left).obj L))).bijective)
  convert hb using 1
  funext x i
  apply (e i).injective
  exact (componentMap_sections K n p L x i).trans ((e i).apply_symm_apply _).symm

/-- The normalization H0 and the full product of component H0 spaces are linearly equal. -/
def componentEquiv : ModuleScalarH C.hom ((pushforward p.left).obj
    ((Scheme.Modules.pullback p.left).obj L)) 0 ≃ₗ[K]
      (∀ i : Fin n, ModuleScalarH (component K).hom (componentLine K n p L i) 0) :=
  LinearEquiv.ofBijective (componentMap K n p L) (componentMap_bijective K n p L)

/-- The equivalence retains the component restriction formula. -/
theorem componentEquiv_apply
    (x : ModuleScalarH C.hom ((pushforward p.left).obj ((Scheme.Modules.pullback p.left).obj L)) 0)
    (i : Fin n) : componentEquiv K n p L x i = componentMap K n p L x i := rfl

end FLT.Mazur.PolygonNormalizationLinearSections
