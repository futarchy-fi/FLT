/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryBaseChange

/-!
# Faithful boundary parameters commute with arbitrary base change

Only the cyclic factor is required to be faithful. The isomorphism retains all
auxiliary labels and the original open inclusion, including over nonfield bases.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (g : T ⟶ S) (E : Over S) [GrpObj E] [IsSeparated E.hom]
  (n : ℕ) [NeZero n]

local instance boundaryPullbackGroup_separated : IsSeparated ((Over.pullback g).obj E).hom :=
  inferInstanceAs (IsSeparated (pullback.snd E.hom g))

/-- The pulled-back faithful boundary parameter retains a faithful cyclic projection. -/
theorem cyclicFaithfulBaseChange_marking :
    AuxiliaryLevel.UniversallyFaithful ((Over.pullback g).obj E) (Multiplicative (ZMod n))
      (((Over.pullback g).map (cyclicFaithfulInclusion E n) ≫
        (parameterBaseChangeIso g E n).hom) ≫ cyclicProjection ((Over.pullback g).obj E) n) := by
  apply (parameterBaseChange_faithful_iff g E n _).mpr
  have h := (Over.mapPullbackAdj g).homEquiv_naturality_right_symm
    (𝟙 ((Over.pullback g).obj (cyclicFaithfulParameter E n))) (cyclicFaithfulInclusion E n)
  rw [Category.id_comp] at h
  rw [h, Category.assoc]
  exact cyclicFaithful_projection E n _

/-- Restrict the actual boundary comparison to the cyclically faithful open. -/
def cyclicFaithfulBaseChangeHom :
    (Over.pullback g).obj (cyclicFaithfulParameter E n) ⟶
      cyclicFaithfulParameter ((Over.pullback g).obj E) n :=
  projectionFaithfulLift _ n _ (cyclicFaithfulBaseChange_marking g E n)

/-- Every original parameter label is retained by the restricted comparison. -/
@[reassoc] theorem cyclicFaithfulBaseChangeHom_inclusion :
    cyclicFaithfulBaseChangeHom g E n ≫ cyclicFaithfulInclusion ((Over.pullback g).obj E) n =
      (Over.pullback g).map (cyclicFaithfulInclusion E n) ≫
        (parameterBaseChangeIso g E n).hom :=
  projectionFaithfulLift_inclusion _ n _ _

/-- The inverse parameter retains cyclic faithfulness over the original base. -/
theorem cyclicFaithfulBaseChange_inverse_marking :
    AuxiliaryLevel.UniversallyFaithful E (Multiplicative (ZMod n))
      ((((Over.mapPullbackAdj g).homEquiv _ _).symm
        (cyclicFaithfulInclusion ((Over.pullback g).obj E) n ≫
          (parameterBaseChangeIso g E n).inv)) ≫ cyclicProjection E n) := by
  apply (parameterBaseChange_faithful_iff g E n _).mp
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.id_comp] using
    cyclicFaithful_projection ((Over.pullback g).obj E) n (𝟙 _)

/-- Construct the inverse from the full original boundary marking. -/
def cyclicFaithfulBaseChangeInv :
    cyclicFaithfulParameter ((Over.pullback g).obj E) n ⟶
      (Over.pullback g).obj (cyclicFaithfulParameter E n) :=
  (Over.mapPullbackAdj g).homEquiv _ _
    (projectionFaithfulLift E n _ (cyclicFaithfulBaseChange_inverse_marking g E n))

/-- The inverse comparison retains the actual full boundary equation scheme. -/
@[reassoc] theorem cyclicFaithfulBaseChangeInv_inclusion :
    cyclicFaithfulBaseChangeInv g E n ≫
        (Over.pullback g).map (cyclicFaithfulInclusion E n) =
      cyclicFaithfulInclusion ((Over.pullback g).obj E) n ≫
        (parameterBaseChangeIso g E n).inv := by
  rw [cyclicFaithfulBaseChangeInv, ← Adjunction.homEquiv_naturality_right,
    projectionFaithfulLift_inclusion, Equiv.apply_symm_apply]

/-- The actual faithful boundary scheme commutes with every change of base. -/
def cyclicFaithfulBaseChangeIso :
    (Over.pullback g).obj (cyclicFaithfulParameter E n) ≅
      cyclicFaithfulParameter ((Over.pullback g).obj E) n where
  hom := cyclicFaithfulBaseChangeHom g E n
  inv := cyclicFaithfulBaseChangeInv g E n
  hom_inv_id := by
    apply (cancel_mono ((Over.pullback g).map (cyclicFaithfulInclusion E n))).mp
    rw [Category.assoc, cyclicFaithfulBaseChangeInv_inclusion,
      cyclicFaithfulBaseChangeHom_inclusion_assoc, Iso.hom_inv_id, Category.comp_id,
      Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (cyclicFaithfulInclusion ((Over.pullback g).obj E) n)).mp
    rw [Category.assoc, cyclicFaithfulBaseChangeHom_inclusion,
      cyclicFaithfulBaseChangeInv_inclusion_assoc, Iso.inv_hom_id, Category.comp_id,
      Category.id_comp]

end FLT.Mazur.CyclicBoundaryParameter
