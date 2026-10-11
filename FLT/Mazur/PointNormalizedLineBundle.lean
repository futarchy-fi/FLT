/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RigidifiedPicardClasses

/-!
# Actual line-bundle normalization at a section

Tensor the original line with the pulled dual of its restriction at the point.
The section identity and canonical dual evaluation construct an actual
rigidification. Its Picard class is the existing normalization map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.SchemePicard
open FCurve
attribute [local irreducible] ModuleSheafTensor.tensor
variable {X S : Scheme.{u}} (f : X ⟶ S) (e : S ⟶ X)
  (L : X.Modules) (hL : LocallyFreeRankOne L)

/-- The original line with its actual point restriction removed by duality. -/
@[irreducible] def pointNormalizedLine : X.Modules :=
  ModuleSheafTensor.tensor L ((Scheme.Modules.pullback f).obj
    (moduleSheafDual ((Scheme.Modules.pullback e).obj L)))

include hL in
/-- The constructed normalization is an actual line bundle. -/
theorem pointNormalizedLine_rankOne : LocallyFreeRankOne (pointNormalizedLine f e L) := by
  unfold pointNormalizedLine
  exact hL.tensor (((hL.pullback e).dual).pullback f)

/-- The constructed sheaf represents precisely the existing Picard normalization. -/
theorem pointNormalizedLine_class :
    mk (pointNormalizedLine f e L) (pointNormalizedLine_rankOne f e L hL) =
      normalize f e (mk L hL) := by
  unfold pointNormalizedLine
  change mk L hL * pullback f ((pullback e (mk L hL))⁻¹) = _
  rw [map_inv]
  rfl

/-- The section equation constructs a canonical trivialization by dual evaluation. -/
@[irreducible] def pointNormalizedLinePointIso (he : e ≫ f = 𝟙 S) :
    (Scheme.Modules.pullback e).obj (pointNormalizedLine f e L) ≅ structureModule S := by
  let N := (Scheme.Modules.pullback e).obj L
  let d : (Scheme.Modules.pullback e).obj
      ((Scheme.Modules.pullback f).obj (moduleSheafDual N)) ≅ moduleSheafDual N :=
    (Scheme.Modules.pullbackComp e f).app _ ≪≫
      (Scheme.Modules.pullbackCongr he).app _ ≪≫ (Scheme.Modules.pullbackId S).app _
  unfold pointNormalizedLine
  exact ModuleLineBundleTensorPullback.tensorIso e L _ ≪≫
    ModuleSheafTensor.congr (Iso.refl N) d ≪≫
      ModuleSheafTensorAssociator.comm N (moduleSheafDual N) ≪≫
        lineSheafDualEvaluationIso (hL.pullback e)

/-- Normalization carries the constructed point trivialization, without choosing one. -/
def pointNormalizedRigidified (he : e ≫ f = 𝟙 S) : RigidifiedBundle e :=
  ⟨⟨pointNormalizedLine f e L, pointNormalizedLine_rankOne f e L hL⟩,
    pointNormalizedLinePointIso f e L hL he⟩

/-- Forgetting the actual trivialization gives the normalized kernel class. -/
theorem pointNormalizedRigidified_kernel (he : e ≫ f = 𝟙 S) :
    rigidifiedBundleKernel e (pointNormalizedRigidified f e L hL he) =
      normalizeToKernel f e he (mk L hL) := by
  apply Subtype.ext
  exact pointNormalizedLine_class f e L hL

end FLT.Mazur.SchemePicard
