/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoproductConstantSections
public import FLT.Mazur.StructureDirectImageHZero
/-!
# Zeroth cohomology of the normalization and node direct images

Both actual module sheaves have H0 canonically isomorphic to `Fin n → K`.
Coordinate formulas retain the actual component and node restriction maps.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.CoproductConstantSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open FCurve StructureDirectImage
variable {K : Type u} [Field K] {ι : Type}
  (X : ι → Over (Spec (.of K))) (h : ∀ i, HasConstantGlobalSections (X i).hom)
  {C : Over (Spec (.of K))} (p : ∐ X ⟶ C)
/-- Direct-image H0 in componentwise constant coordinates, over the specified base field. -/
def imageH0Equiv : ModuleScalarH C.hom (image p.left) 0 ≃ₗ[K] (ι → K) := by
  letI := Module.compHom Γ((∐ X).left, ⊤) (structureScalarMap (p.left ≫ C.hom))
  let e := h0Sections p.left C.hom
  refine { toAddEquiv := e.toAddEquiv.trans (ringEquiv X h).toAddEquiv, map_smul' := ?_ }
  intro a x
  change ringEquiv X h (e (a • x)) = a • ringEquiv X h (e x)
  rw [e.map_smul]
  change ringEquiv X h (structureScalarMap (p.left ≫ C.hom) a * e x) = _
  have hs : structureScalarMap (p.left ≫ C.hom) a =
      structureScalarMap (∐ X).hom a := congrArg (fun f ↦ structureScalarMap f a) p.w
  rw [hs, map_mul]
  ext i
  exact congrArg (fun b ↦ b * ringEquiv X h (e x) i) (scalar X h a i)
theorem imageH0Equiv_coordinate (x : ModuleScalarH C.hom (image p.left) 0) (i : ι) :
    structureScalarMap (X i).hom (imageH0Equiv X h p x i) =
      (Sigma.ι X i).left.appTop (moduleH0Equiv (image p.left) x) :=
  coordinate X h _ i
end FLT.Mazur.CoproductConstantSections
namespace FLT.Mazur.PolygonNormalizationHZero
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open FCurve PolygonPinching PolygonStructureInclusion PolygonBranchDifferenceSheaf
open CoproductConstantSections
variable (K : Type u) [Field K] (n : ℕ) {C : Over (Spec (.of K))}
/-- The normalization direct image has one independent constant per projective line. -/
def normalizationEquiv (p : components K n ⟶ C) :
    ModuleScalarH C.hom (normalizationModule K n p) 0 ≃ₗ[K] (Fin n → K) :=
  imageH0Equiv (fun _ : Fin n ↦ component K)
    (fun _ ↦ ProjectiveLineConstantSections.constant_sections K) p
theorem point_constants : HasConstantGlobalSections (𝟙 (Spec (.of K))) := by
  change Function.Bijective ((Scheme.ΓSpecIso (.of K)).inv.hom)
  exact ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv
/-- The node direct image has one independent value per node. -/
def nodeEquiv (q : nodes K n ⟶ C) :
    ModuleScalarH C.hom (nodeModule K n q) 0 ≃ₗ[K] (Fin n → K) :=
  imageH0Equiv (fun _ : Fin n ↦ point K) (fun _ ↦ point_constants K) q
theorem normalization_coordinate (p : components K n ⟶ C)
    (x : ModuleScalarH C.hom (normalizationModule K n p) 0) (i : Fin n) :
    structureScalarMap (ProjectiveLine.toBase K) (normalizationEquiv K n p x i) =
      (componentι K n i).left.appTop (moduleH0Equiv (normalizationModule K n p) x) :=
  imageH0Equiv_coordinate _ _ p x i
theorem node_coordinate (q : nodes K n ⟶ C)
    (x : ModuleScalarH C.hom (nodeModule K n q) 0) (i : Fin n) :
    (Scheme.ΓSpecIso (.of K)).inv (nodeEquiv K n q x i) =
      (nodeι K n i).left.appTop (moduleH0Equiv (nodeModule K n q) x) :=
  imageH0Equiv_coordinate _ _ q x i
end FLT.Mazur.PolygonNormalizationHZero
