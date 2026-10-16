/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTopNodeGraphPresentation
public import FLT.Mazur.SurjectiveDominantEpi
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The higher finite graph as an original closed correspondence

The whole graph is a closed subscheme of the original node product and
is schematically detected by both full punctured branches. Its source
projection is finite when the preceding action is the prescribed scaling.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial TensorProduct
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal topNodeGraphPairMap
  topNodeGraphTensorMap topNodeActionDefect topNodeErrorAlgebra
variable (R : Type) [CommRing R] (m : ℕ)
variable (u v : ((Ring R (m + 1))[T;T⁻¹])ˣ)
local notation "S" => Ring R (m + 1)
local notation "B" => ChartRing (parameter R (m + 1))
local notation "L" => (S)[T;T⁻¹]
local notation "C" => stageNodeBranchSubalgebra R (m + 1)
local notation "β" => stageNodeBranchPair R (m + 1)
local notation "G" => topNodeGraphAlgebra R m u v

/-- The original source node map into the full graph. -/
def topNodeGraphSource : (B) →ₐ[S] (G) :=
  (β).codRestrict (G) (fun z ↦ (le_sup_left : (C) ≤ (G)) ⟨z, rfl⟩)

/-- The whole original graph scheme, with its full nonreduced structure. -/
def topNodeGraphScheme : Scheme := Spec (CommRingCat.of (G))

/-- The graph projects to the unchanged original source node. -/
def topNodeGraphSchemeSource : topNodeGraphScheme R m u v ⟶ Spec (CommRingCat.of (B)) :=
  Spec.map (CommRingCat.ofHom (topNodeGraphSource R m u v).toRingHom)

/-- The full graph is an actual closed subscheme of the original node product. -/
def topNodeGraphProductInclusion :
    topNodeGraphScheme R m u v ⟶ Spec (CommRingCat.of ((B) ⊗[S] (B))) :=
  Spec.map (CommRingCat.ofHom (topNodeGraphTensorMap R m u v).toRingHom)

instance topNodeGraphProductInclusion_closed :
    IsClosedImmersion (topNodeGraphProductInclusion R m u v) :=
  IsClosedImmersion.spec_of_surjective _ (topNodeGraphTensorMap_surjective R m u v)

/-- Both full branch graphs map to the unchanged graph scheme. -/
def topNodeGraphBranches : Spec (CommRingCat.of ((L) × (L))) ⟶ topNodeGraphScheme R m u v :=
  Spec.map (CommRingCat.ofHom (G).val.toRingHom)

instance topNodeGraphBranches_dominant :
    IsSchemeTheoreticallyDominant (topNodeGraphBranches R m u v) :=
  SurjectiveDominantEpi.spec_schematic _ Subtype.val_injective

/-- This dense/closed factorization retains the original full two-node evaluation. -/
theorem topNodeGraphBranches_factorization :
    topNodeGraphBranches R m u v ≫ topNodeGraphProductInclusion R m u v =
      Spec.map (CommRingCat.ofHom (topNodeGraphPairMap R m u v).toRingHom) := by
  rw [topNodeGraphBranches, topNodeGraphProductInclusion, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (topNodeGraphTensorMap_val R m u v)

variable (a : (Ring R (m + 1))ˣ)
  (hu : coeffMap (restriction R m).toRingHom u.val =
    LaurentPolynomial.C (restriction R m a.val) * LaurentPolynomial.T 1)
  (hv : coeffMap (restriction R m).toRingHom v.val =
    LaurentPolynomial.C (restriction R m a⁻¹.val) * LaurentPolynomial.T 1)
include hu hv

/-- The actual source map is finite, by the proved two-error description. -/
theorem topNodeGraphSource_finite : (topNodeGraphSource R m u v).toRingHom.Finite := by
  let E := topNodeErrorAlgebra R m u v a
  let _ : CommRing E := inferInstance
  let _ : Algebra (C) E := E.algebra
  let j : E ≃ₐ[S] (G) := Subalgebra.equivOfEq (E.restrictScalars (S)) (G)
    (topNodeErrorAlgebra_eq_graph R m u v a hu hv)
  have hj : (topNodeGraphSource R m u v).toRingHom =
      j.toRingHom.comp ((algebraMap (C) E).comp
        (stageNodeBranchEquiv R (m + 1)).toRingEquiv.toRingHom) := by
    apply RingHom.ext
    intro z
    apply Subtype.ext
    rfl
  rw [hj]
  have he : (algebraMap (C) E).Finite :=
    (@RingHom.finite_algebraMap (C) E _ _ _).mpr
      (topNodeErrorAlgebra_finite R m u v a hu hv)
  exact j.toRingEquiv.finite.comp
    (he.comp (stageNodeBranchEquiv R (m + 1)).toRingEquiv.finite)

/-- The original graph correspondence is finite over its original source node. -/
theorem topNodeGraphSchemeSource_finite : IsFinite (topNodeGraphSchemeSource R m u v) := by
  rw [topNodeGraphSchemeSource, IsFinite.SpecMap_iff]
  exact topNodeGraphSource_finite R m u v a hu hv

end FLT.Mazur.PolygonInfinitesimalStages
