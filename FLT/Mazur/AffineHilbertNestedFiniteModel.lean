/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertNestedRestriction
public import FLT.Mazur.AffineHilbertFiniteKernelModel
public import FLT.Mazur.SchemeRelationInvariantFunctorial
public import FLT.Mazur.SchemeRelationJointModelGeometry

/-!
# Recomputed finite models on actual nested affine selections

Pull old finite coefficients through the full original relation map, then
join them with the finite coefficients freshly computed on the new chart.
Both original coefficient equations hold on the entire new source. The
joint target is affine and Noetherian; no equality of finite choices is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
attribute [local irreducible] relation fst snd
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  {B : Over (Spec (.of R))} [IsAffine B.left] (v : B ⟶ A) [IsOpenImmersion v.left]
local notation "p₀" => Over.Hom.left (fst f hL d V c k)
local notation "q₀" => Over.Hom.left (snd f hL d V c k)
local notation "p₁" => Over.Hom.left (fst f hL d V c (v ≫ k))
local notation "q₁" => Over.Hom.left (snd f hL d V c (v ≫ k))
local instance nestedFiniteChartOpen : IsOpenImmersion (v ≫ k).left :=
  inferInstanceAs (IsOpenImmersion (v.left ≫ k.left))
/-- The old invariant algebra uses the original ground-base coefficient map. -/
local instance nestedOldInvariantAlgebra : Algebra R
    (SchemeEffectiveEpiSections.compatibleFunctions p₀ q₀) :=
  (invariantCoefficientBase f hL d V c k).toAlgebra
/-- The recomputed invariant algebra retains that same original ground base. -/
local instance nestedNewInvariantAlgebra : Algebra R
    (SchemeEffectiveEpiSections.compatibleFunctions p₁ q₁) :=
  (invariantCoefficientBase f hL d V c (v ≫ k)).toAlgebra
local notation "C₀" => finiteKernelCoefficientAlgebra f hL d V c k
local notation "C₁" => finiteKernelCoefficientAlgebra f hL d V c (v ≫ k)

/-- Old finite coefficients are full invariants of the newly computed original relation. -/
def nestedOldFiniteCoefficients : C₀ →+* SchemeEffectiveEpiSections.compatibleFunctions p₁ q₁ :=
  (SchemeRelationInvariantSpectrum.relationPullback p₀ q₀ p₁ q₁ v.left
    (nestedToFullRelation f hL d V c k v).left
    (congrArg Over.Hom.left (nestedToFullRelation_fst f hL d V c k v))
    (congrArg Over.Hom.left (nestedToFullRelation_snd f hL d V c k v))).comp (C₀).val.toRingHom
local notation "α" => nestedOldFiniteCoefficients f hL d V c k v
local notation "β" => AlgHom.toRingHom (Subalgebra.val C₁)

/-- The joint target contains both old and freshly recomputed finite coefficients. -/
def nestedFiniteTarget : Scheme := SchemeRelationJointModel.target p₁ q₁ α β

/-- Its source projection uses the unchanged functions on the complete selected source. -/
def nestedFiniteProjection : B.left ⟶ nestedFiniteTarget f hL d V c k v :=
  SchemeRelationJointModel.projection p₁ q₁ α β

/-- The joint finite target compares to the actual old coefficient model. -/
def nestedFiniteToOld : nestedFiniteTarget f hL d V c k v ⟶
    (finiteKernelModel f hL d V c k).left := SchemeRelationJointModel.toLeft p₁ q₁ α β

/-- It also compares to the finite model recomputed from the new chart's full relation. -/
def nestedFiniteToNew : nestedFiniteTarget f hL d V c k v ⟶
    (finiteKernelModel f hL d V c (v ≫ k)).left := SchemeRelationJointModel.toRight p₁ q₁ α β

@[reassoc]
theorem nestedFiniteProjection_toOld : nestedFiniteProjection f hL d V c k v ≫
    nestedFiniteToOld f hL d V c k v = v.left ≫ (finiteKernelProjection f hL d V c k).left := by
  change SchemeRelationJointModel.projection p₁ q₁ α β ≫
    SchemeRelationJointModel.toLeft p₁ q₁ α β = _
  rw [SchemeRelationJointModel.projection_toLeft]
  change B.left.toSpecΓ ≫ Spec.map _ = v.left ≫ (A.left.toSpecΓ ≫ Spec.map _)
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  rfl

@[reassoc]
theorem nestedFiniteProjection_toNew : nestedFiniteProjection f hL d V c k v ≫
    nestedFiniteToNew f hL d V c k v = (finiteKernelProjection f hL d V c (v ≫ k)).left :=
  SchemeRelationJointModel.projection_toRight p₁ q₁ α β

/-- Both finite-model comparisons retain the same unchanged original ground base. -/
theorem nestedFinite_base_condition : nestedFiniteToOld f hL d V c k v ≫
    (finiteKernelModel f hL d V c k).hom = nestedFiniteToNew f hL d V c k v ≫
      (finiteKernelModel f hL d V c (v ≫ k)).hom := by
  apply SchemeRelationJointModel.affine_hom_ext p₁ q₁ α β
  change nestedFiniteProjection f hL d V c k v ≫ _ =
    nestedFiniteProjection f hL d V c k v ≫ _
  rw [← Category.assoc, nestedFiniteProjection_toOld, Category.assoc,
    (finiteKernelProjection f hL d V c k).w, v.w,
    ← Category.assoc, nestedFiniteProjection_toNew,
    (finiteKernelProjection f hL d V c (v ≫ k)).w]

/-- The newly joined finite model is a scheme over the original ground base. -/
def nestedFiniteOver : Over (Spec (.of R)) :=
  Over.mk (nestedFiniteToNew f hL d V c k v ≫ (finiteKernelModel f hL d V c (v ≫ k)).hom)

/-- The constructed source projection also retains its full relative scheme morphism. -/
def nestedFiniteRelativeProjection : B ⟶ nestedFiniteOver f hL d V c k v :=
  Over.homMk (nestedFiniteProjection f hL d V c k v) (by
    change nestedFiniteProjection f hL d V c k v ≫
      (nestedFiniteToNew f hL d V c k v ≫ _) = B.hom
    rw [← Category.assoc, nestedFiniteProjection_toNew]
    exact (finiteKernelProjection f hL d V c (v ≫ k)).w)

instance nestedFiniteTarget_isNoetherian : IsNoetherian (nestedFiniteTarget f hL d V c k v) := by
  have h₀ : Algebra.FiniteType ℤ C₀ := Algebra.FiniteType.trans
    (R := ℤ) (S := R) (A := C₀) inferInstance inferInstance
  have h₁ : Algebra.FiniteType ℤ C₁ := Algebra.FiniteType.trans
    (R := ℤ) (S := R) (A := C₁) inferInstance inferInstance
  exact @SchemeRelationJointModel.isNoetherian _ _ p₁ q₁ C₀ C₁ _ _ α β h₀ h₁

instance nestedFiniteTarget_isAffine : IsAffine (nestedFiniteTarget f hL d V c k v) :=
  inferInstanceAs (IsAffine (SchemeRelationJointModel.target p₁ q₁ α β))

/-- The newly joined coefficients coequalize the entire new original relation. -/
@[reassoc]
theorem nestedFiniteProjection_condition : p₁ ≫ nestedFiniteProjection f hL d V c k v =
    q₁ ≫ nestedFiniteProjection f hL d V c k v :=
  SchemeRelationJointModel.projection_condition p₁ q₁ α β

end FLT.Mazur.HilbertChart.AffineRestriction
