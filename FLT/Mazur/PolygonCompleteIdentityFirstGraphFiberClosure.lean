/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphFiberPuncture
public import FLT.Mazur.PrincipalOpenSchematicDensityCriterion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The reduced original node is the closure of the actual fiber puncture

Factor the actual puncture through the original reduced node. The first
map is schematically dominant and the second is a closed immersion.
The literal special fiber can still have a residual square-zero ideal;
the factorization identifies exactly which functions the puncture loses.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
  completeIdentityFirstGraphReduction completeIdentityFirstGraphSource
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "N" => ChartRing (0 : R)
local notation "Q" => completeIdentityFirstGraphSpecialFiber K n h i
local notation "f" => completeIdentityFirstGraphFiberReduction K n h i
local notation "s" => completeIdentityFirstGraphFiberSection K n h i
local notation "x" => completeIdentityFirstGraphFiberLeft K n h i
local notation "y" => completeIdentityFirstGraphFiberRight K n h i
local notation "L" => Localization.Away ((x) + (y))
local notation "a" => algebraMap (Q) (L)

/-- The actual original-source section restricts to the punctured fiber. -/
def completeIdentityFirstGraphFiberPunctureNodeMap : (N) →+* (L) := (a).comp (s)

/-- Every original reduced-node function is retained on the actual punctured fiber. -/
theorem completeIdentityFirstGraphFiberPunctureNodeMap_injective :
    Function.Injective (completeIdentityFirstGraphFiberPunctureNodeMap K n h i) := by
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  apply le_antisymm _ bot_le
  intro z hz
  have hs : (s) z ∈ RingHom.ker (a) := hz
  rw [completeIdentityFirstGraphFiberPuncture_kernel] at hs
  exact (completeIdentityFirstGraphFiberSection_rightInverse K n h i z).symm.trans hs

/-- The factorization is the original restriction homomorphism on every fiber function. -/
theorem completeIdentityFirstGraphFiberPunctureNodeMap_comp :
    (completeIdentityFirstGraphFiberPunctureNodeMap K n h i).comp (f) = (a) := by
  apply RingHom.ext
  intro z
  have hz : z - (s) ((f) z) ∈ RingHom.ker (f) := by
    change (f).toAddMonoidHom (z - (s) ((f) z)) = 0
    rw [map_sub]
    change (f) z - (f) ((s) ((f) z)) = 0
    rw [completeIdentityFirstGraphFiberSection_rightInverse, sub_self]
  rw [← completeIdentityFirstGraphFiberPuncture_kernel] at hz
  change (a) (z - (s) ((f) z)) = 0 at hz
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

/-- The puncture is schematically dense in the unchanged original reduced node. -/
instance completeIdentityFirstGraphFiberPunctureNodeMap_dominant :
    IsSchemeTheoreticallyDominant
      (Spec.map (CommRingCat.ofHom (completeIdentityFirstGraphFiberPunctureNodeMap K n h i))) :=
  SurjectiveDominantEpi.spec_schematic _
    (completeIdentityFirstGraphFiberPunctureNodeMap_injective K n h i)

/-- The reduced original node embeds as a closed subscheme of the literal graph fiber. -/
instance completeIdentityFirstGraphFiberReduction_closed :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (f))) :=
  IsClosedImmersion.spec_of_surjective _
    (completeIdentityFirstGraphFiberReduction_surjective K n h i)

/-- The dense map followed by the closed immersion is the literal original puncture inclusion. -/
theorem completeIdentityFirstGraphFiberPuncture_factorization :
    Spec.map (CommRingCat.ofHom (completeIdentityFirstGraphFiberPunctureNodeMap K n h i)) ≫
        Spec.map (CommRingCat.ofHom (f)) =
      PrincipalAffineRefinement.inclusion ((x) + (y)) := by
  rw [← Spec.map_comp]
  exact congrArg (fun g : (Q) →+* (L) ↦ Spec.map (CommRingCat.ofHom g))
    (completeIdentityFirstGraphFiberPunctureNodeMap_comp K n h i)

end FLT.Mazur.PolygonInfinitesimalStages
