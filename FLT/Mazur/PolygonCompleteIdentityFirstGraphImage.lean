/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphTensor
public import FLT.Mazur.SurjectiveDominantEpi
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The literal original first graph as a scheme-theoretic image

The branch graph factors through the finite graph by a schematically dense
map and a closed immersion into the original node product. Its defining
ideal is exactly the kernel of branch evaluation, with no radical taken.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial TensorProduct
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
  completeIdentityFirstGraphTensorMap completeIdentityFirstGraphPairMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) 1
local notation "B" => ChartRing (parameter (R) 1)
local notation "L" => (S)[T;T⁻¹]
local notation "E" => completeIdentityFirstErrorAlgebra K n h i
local notation "φ" => completeIdentityFirstGraphTensorMap K n h i
local notation "ψ" => completeIdentityFirstGraphPairMap K n h i
/-- Cache the existing graph ring before forming its quotient presentation. -/
local instance completeIdentityFirstGraphImageCommRing : CommRing (E) := inferInstance
/-- Cache the tensor ring so quotient inference does not traverse its factors again. -/
local instance completeIdentityFirstGraphImageTensorCommRing :
    CommRing ((B) ⊗[S] (B)) := inferInstance

/-- The full defining ideal of the actual original node correspondence. -/
def completeIdentityFirstGraphIdeal : Ideal ((B) ⊗[S] (B)) := RingHom.ker (ψ).toRingHom

/-- The original graph ideal is the full kernel of the surjective product map. -/
theorem completeIdentityFirstGraphIdeal_eq :
    completeIdentityFirstGraphIdeal K n h i = RingHom.ker (φ).toRingHom := by
  ext z
  change (ψ) z = 0 ↔ (φ) z = 0
  rw [← completeIdentityFirstGraphTensorMap_val]
  exact ⟨fun hz ↦ Subtype.ext hz, fun hz ↦ congrArg Subtype.val hz⟩

/-- The literal quotient by that ideal recovers the entire finite graph ring. -/
def completeIdentityFirstGraphQuotientEquiv :
    ((B) ⊗[S] (B)) ⧸ completeIdentityFirstGraphIdeal K n h i ≃+* (E) :=
  (Ideal.quotEquivOfEq (completeIdentityFirstGraphIdeal_eq K n h i)).trans
    (RingHom.quotientKerEquivOfSurjective
      (completeIdentityFirstGraphTensorMap_surjective K n h i))

/-- The finite graph is a closed subscheme of the original affine node product. -/
def completeIdentityFirstGraphProductInclusion :
    completeIdentityFirstGraphScheme K n h i ⟶ Spec (.of ((B) ⊗[S] (B))) :=
  Spec.map (CommRingCat.ofHom (φ).toRingHom)

instance completeIdentityFirstGraphProductInclusion_closed :
    IsClosedImmersion (completeIdentityFirstGraphProductInclusion K n h i) :=
  IsClosedImmersion.spec_of_surjective _
    (completeIdentityFirstGraphTensorMap_surjective K n h i)

/-- The entire branch graph maps into the finite graph, retaining both branches. -/
def completeIdentityFirstGraphBranches :
    Spec (.of ((L) × (L))) ⟶ completeIdentityFirstGraphScheme K n h i :=
  Spec.map (CommRingCat.ofHom (E).val.toRingHom)

instance completeIdentityFirstGraphBranches_dominant :
    IsSchemeTheoreticallyDominant (completeIdentityFirstGraphBranches K n h i) :=
  SurjectiveDominantEpi.spec_schematic _ Subtype.val_injective

/-- The dense/closed factorization is exactly the original two-input evaluation map. -/
theorem completeIdentityFirstGraphBranches_factorization :
    completeIdentityFirstGraphBranches K n h i ≫
        completeIdentityFirstGraphProductInclusion K n h i =
      Spec.map (CommRingCat.ofHom (ψ).toRingHom) := by
  rw [completeIdentityFirstGraphBranches, completeIdentityFirstGraphProductInclusion,
    ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (completeIdentityFirstGraphTensorMap_val K n h i)

/-- The schematic image ideal of branch evaluation equals the full closed graph ideal. -/
theorem completeIdentityFirstGraphBranches_imageIdeal :
    (Spec.map (CommRingCat.ofHom (ψ).toRingHom)).ker =
      (completeIdentityFirstGraphProductInclusion K n h i).ker := by
  rw [← completeIdentityFirstGraphBranches_factorization, Scheme.Hom.ker_comp,
    Scheme.Hom.ker_eq_bot, Scheme.IdealSheafData.map_bot]

end FLT.Mazur.PolygonInfinitesimalStages
