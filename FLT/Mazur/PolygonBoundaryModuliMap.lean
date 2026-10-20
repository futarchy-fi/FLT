/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicSmoothParameterScope
public import FLT.Mazur.PolygonCartierGenerator
public import FLT.Mazur.PolygonNodeLocus

/-!
# Actual split polygon boundary classes in the ample cyclic moduli presheaf

The canonical positive polygon and its transverse cyclic subgroup define an
original ample cyclic level and a natural moduli map on all base changes.
Its closed boundary class is outside both smooth normalized charts. These
are boundary test families, with no asserted fppf coverage of degenerations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonBoundaryModuli
open GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
local notation "p" => PolygonAtlas.normalization K n
local notation "q" => PolygonAtlas.nodes K n
local notation "h" => PolygonAtlas.isPushout K n (NeZero.pos n)

/-- The actual canonical split polygon, including the one-gon. -/
def boundaryCurve : GeneralizedEllipticCurve (Spec (.of K)) :=
  PolygonGeneralizedCurve.curve K n (NeZero.pos n) p q h

/-- The original transverse cyclic subgroup meets all components of this boundary curve. -/
def boundaryLevel : ampleCyclicLevels (Spec (.of K)) n :=
  ⟨⟨boundaryCurve K n, PolygonFiniteSubgroup.subgroup K n p (NeZero.pos n) q h⟩,
    PolygonCartierGenerator.isCyclic K n p (NeZero.pos n) q h,
    PolygonFiniteSubgroup.isAmple K n p (NeZero.pos n) q h⟩

/-- The unchanged ample cyclic moduli class of the split boundary level. -/
def boundaryClass : ampleCyclicClasses (Spec (.of K)) n := Quotient.mk _ (boundaryLevel K n)

/-- All base changes of the boundary level define an actual natural modular transformation. -/
def boundaryModuliMap : uliftYoneda.{1}.obj (Spec (.of K)) ⟶ ampleCyclicClassPresheaf n where
  app _ := ↾(fun g ↦ ampleCyclicClassesPullback g.down n (boundaryClass K n))
  naturality _ _ f := by
    ext g
    exact congrFun (ampleCyclicClassesPullback_comp g.down f.unop n) (boundaryClass K n)

/-- The identity parameter retains the original closed boundary object. -/
theorem boundaryModuliMap_identity :
    (boundaryModuliMap K n).app (Opposite.op (Spec (.of K))) (ULift.up (𝟙 _)) =
      boundaryClass K n :=
  congrFun (ampleCyclicClassesPullback_id _ n) (boundaryClass K n)

/-- The original split polygon has an actual nonsmooth node for every positive size. -/
theorem boundaryCurve_not_smooth : ¬ Smooth (boundaryCurve K n).curve.hom := by
  intro hs
  let _ := hs
  have hn := PolygonNodeLocus.atlas_node_not_smooth K n
    ⟨0, NeZero.pos n⟩ (default : Spec (.of K))
  have he : (PolygonAtlas.polygon K n).hom.smoothLocus = ⊤ :=
    (boundaryCurve K n).curve.hom.smoothLocus_eq_top
  rw [he] at hn
  exact hn trivial

/-- Neither smooth normalized characteristic chart represents this genuine boundary object. -/
theorem normalizedModuliMap_ne_boundary (b : Bool)
    (v : Spec (.of K) ⟶ CyclicCharacteristicAtlas.normalizedLocus n b) :
    (CyclicCharacteristicAtlas.normalizedModuliMap n b).app (Opposite.op (Spec (.of K)))
      (ULift.up v) ≠ boundaryClass K n :=
  CyclicCharacteristicAtlas.normalized_moduli_ne_of_not_smooth n
    (boundaryLevel K n).val.2 (boundaryLevel K n).property.1 (boundaryLevel K n).property.2
    (boundaryCurve_not_smooth K n) b v

end FLT.Mazur.PolygonBoundaryModuli
