/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjRingEquiv
public import FLT.Mazur.GradedProjZeroMapNaturality
public import FLT.Mazur.PolygonVeroneseProperProj
public import FLT.Mazur.PolygonVeroneseRotationEquiv

/-!
# The constructed cyclic action on the original complete projective model

Apply Proj to the actual compatible Veronese section automorphism. This gives
an action over the unchanged power-series base on the original chosen model.
Its comparison with the original marked stage embeddings remains separate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] compatibleSectionRotation compatibleVeroneseRotation

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The actual compatible section rotation as a graded ring homomorphism. -/
def completeRotationGradedMap (a : ZMod n) :
    compatibleVeroneseGrade K n h (exactVeroneseStep K n h) →+*ᵍ
      compatibleVeroneseGrade K n h (exactVeroneseStep K n h) :=
  GradedProjRingEquiv.forward _ _
    (compatibleVeroneseRotationEquiv K n h (exactVeroneseStep K n h) a)
    (compatibleVeroneseRotation_grade_iff K n h (exactVeroneseStep K n h) a)

/-- Cyclic rotation of the original projective model, constructed from its actual section ring. -/
def completeRotationIso (a : ZMod n) : exactVeroneseProj K n h ≅ exactVeroneseProj K n h :=
  GradedProjRingEquiv.iso _ _
    (compatibleVeroneseRotationEquiv K n h (exactVeroneseStep K n h) a)
    (compatibleVeroneseRotation_grade_iff K n h (exactVeroneseStep K n h) a)

/-- The cyclic automorphism as an actual scheme morphism of the original complete family. -/
def completeRotation (a : ZMod n) : exactVeroneseProj K n h ⟶ exactVeroneseProj K n h :=
  (completeRotationIso K n h a).hom

/-- Zero translation is the identity of the original complete model. -/
@[simp] theorem completeRotation_zero : completeRotation K n h 0 = 𝟙 _ := by
  change Proj.map (completeRotationGradedMap K n h 0) _ = _
  have hz : completeRotationGradedMap K n h 0 = GradedRingHom.id _ := by
    ext s : 1
    exact DFunLike.congr_fun
      (compatibleVeroneseRotation_zero K n h (exactVeroneseStep K n h)) s
  simp only [hz, Proj.map_id, exactVeroneseProj]

/-- The original cyclic addition acts by composition on the complete projective model. -/
theorem completeRotation_add (a b : ZMod n) :
    completeRotation K n h (a + b) = completeRotation K n h a ≫ completeRotation K n h b := by
  change Proj.map (completeRotationGradedMap K n h (a + b)) _ =
    Proj.map (completeRotationGradedMap K n h a) _ ≫
      Proj.map (completeRotationGradedMap K n h b) _
  have hab : completeRotationGradedMap K n h (a + b) =
      (completeRotationGradedMap K n h a).comp (completeRotationGradedMap K n h b) := by
    apply GradedRingHom.ext
    intro s
    change compatibleVeroneseRotation K n h (exactVeroneseStep K n h) (a + b) s =
      compatibleVeroneseRotation K n h (exactVeroneseStep K n h) a
        (compatibleVeroneseRotation K n h (exactVeroneseStep K n h) b s)
    exact DFunLike.congr_fun
      (compatibleVeroneseRotation_add K n h (exactVeroneseStep K n h) a b) s
  simp only [hab]
  exact Proj.map_comp _ _ _ _

/-- The constructed complete automorphism preserves the specified power-series structure map. -/
@[reassoc] theorem completeRotation_toBase (a : ZMod n) :
    completeRotation K n h a ≫ exactVeroneseProjToBase K n h =
      exactVeroneseProjToBase K n h := by
  let _ : NeZero (exactVeroneseStep K n h) := ⟨ne_of_gt (exactVeroneseStep_pos K n h)⟩
  exact GradedProjZeroMapNaturality.map_toSpec _ _ (completeRotationGradedMap K n h a)
    (algebraMap (PowerSeries K) _) (algebraMap (PowerSeries K) _)
    (compatibleVeroneseRotation_algebraMap K n h (exactVeroneseStep K n h) a) _

/-- The actual cyclic map carries every standard open to its original rotated section open. -/
theorem completeRotation_preimage_basicOpen (a : ZMod n)
    (s : CompatibleVeroneseSections K n h (exactVeroneseStep K n h)) :
    (completeRotation K n h a) ⁻¹ᵁ
        Proj.basicOpen (compatibleVeroneseGrade K n h (exactVeroneseStep K n h)) s =
      Proj.basicOpen (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))
        (compatibleVeroneseRotation K n h (exactVeroneseStep K n h) a s) := rfl

end FLT.Mazur.PolygonInfinitesimalStages
