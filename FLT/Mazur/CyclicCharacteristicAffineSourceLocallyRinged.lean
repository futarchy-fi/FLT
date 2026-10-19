/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineSourceCover
public import FLT.Mazur.CyclicCharacteristicAffineSectionReconstruction

/-!
# The actual locally ringed projection of a characteristic source open

The projection on the original inverse-image source factors through the
characteristic orbit open. Its two chart composites are the existing locally
ringed factors, so its section map retains both actual chart pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool)
  (j : (invariantAffineCover n (!b)).I₀)

/-- The locally ringed source projection factors through the exact characteristic open. -/
def affineSourceToInvariantOpen :
    (affineSourceOpen n b j).toScheme.toLocallyRingedSpace ⟶
      invariantOpenSpace n (affineOrbitOpen n ⟨!b, j⟩) :=
  LocallyRingedSpace.IsOpenImmersion.lift
    ((invariantLocallyRingedSpace n).ofRestrict
      (affineOrbitOpen n ⟨!b, j⟩).isOpenEmbedding)
    ((affineSourceOpen n b j).ι.toLRSHom ≫ invariantLocallyRingedProjection n) (by
      rintro _ ⟨x, rfl⟩
      refine ⟨⟨projection n x.val, x.property⟩, ?_⟩
      change projection n x.val = (invariantLocallyRingedProjection n).base x.val
      rw [invariantLocallyRingedProjection_base]
      rfl)

/-- The factor retains the original ambient locally ringed projection. -/
@[reassoc] theorem affineSourceToInvariantOpen_comp :
    affineSourceToInvariantOpen n b j ≫ (invariantLocallyRingedSpace n).ofRestrict
      (affineOrbitOpen n ⟨!b, j⟩).isOpenEmbedding =
        (affineSourceOpen n b j).ι.toLRSHom ≫ invariantLocallyRingedProjection n :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

/-- The selected source chart has the original characteristic locally ringed factor. -/
@[reassoc] theorem affineSourceToInvariantOpen_selected :
    (selectedToAffineSource n b j).toLRSHom ≫ affineSourceToInvariantOpen n b j =
      affineToInvariantOpen n ⟨!b, j⟩ := by
  rw [← cancel_mono ((invariantLocallyRingedSpace n).ofRestrict
    (affineOrbitOpen n ⟨!b, j⟩).isOpenEmbedding)]
  rw [Category.assoc, affineSourceToInvariantOpen_comp, affineToInvariantOpen_comp,
    ← Category.assoc, ← Scheme.Hom.comp_toLRSHom, selectedToAffineSource_comp]
  rfl

/-- Actual invariant sections pulled back to the original source open. -/
def affineSourceInvariantSectionMap :
    (invariantSheaf n).obj.obj (op (affineOrbitOpen n ⟨!b, j⟩)) ⟶
      Γ((affineSourceOpen n b j).toScheme, ⊤) :=
  (invariantOpenSectionsIso n _).inv ≫
    LocallyRingedSpace.Γ.map (affineSourceToInvariantOpen n b j).op

/-- The selected component pullback is the actual characteristic section comparison. -/
theorem affineSourceInvariantSectionMap_selected :
    affineSourceInvariantSectionMap n b j ≫ (selectedToAffineSource n b j).appTop =
      affineInvariantSectionMap n ⟨!b, j⟩ := by
  have h := congrArg (fun f => LocallyRingedSpace.Γ.map f.op)
    (affineSourceToInvariantOpen_selected n b j)
  change LocallyRingedSpace.Γ.map ((affineSourceToInvariantOpen n b j).op ≫
    (selectedToAffineSource n b j).toLRSHom.op) = _ at h
  rw [Functor.map_comp] at h
  exact congrArg ((invariantOpenSectionsIso n _).inv ≫ ·) h

/-- The opposite component pullback on each cover member is the selected affine value. -/
theorem affineSourceToInvariantOpen_transition (k : (affineOppositeCover n b j).I₀) :
    ((affineOppositeCover n b j).f k ≫ oppositeToAffineSource n b j).toLRSHom ≫
        affineSourceToInvariantOpen n b j =
      (affineOppositeTarget n b j k).toLRSHom ≫ affineToInvariantOpen n ⟨!b, j⟩ := by
  rw [← cancel_mono ((invariantLocallyRingedSpace n).ofRestrict
    (affineOrbitOpen n ⟨!b, j⟩).isOpenEmbedding)]
  simp only [Category.assoc, affineSourceToInvariantOpen_comp, affineToInvariantOpen_comp,
    affineLocallyRingedProjection, Scheme.Hom.comp_toLRSHom]
  rw [← Category.assoc (oppositeToAffineSource n b j).toLRSHom,
    ← Scheme.Hom.comp_toLRSHom, oppositeToAffineSource_comp]
  change (((affineOppositeCover n b j).f k ≫ (affineOppositeOpen n b j).ι).toLRSHom ≫
    chartLocallyRingedProjection n b) =
      ((affineOppositeTarget n b j k ≫ invariantAffineInclusion n ⟨!b, j⟩).toLRSHom ≫
        chartLocallyRingedProjection n (!b))
  exact (chartLocallyRingedProjection_related n (!b) b _ _
    (affineOppositeCover_related n b j k)).symm

/-- The actual opposite pullback is exactly the reconstructed full residual section. -/
theorem affineSourceInvariantSectionMap_opposite
    (s : (invariantSheaf n).obj.obj (op (affineOrbitOpen n ⟨!b, j⟩))) :
    (oppositeToAffineSource n b j).appTop (affineSourceInvariantSectionMap n b j s) =
      affineSectionReconstruction n b j (affineResidualSectionMap n ⟨!b, j⟩ s) := by
  apply affineSectionReconstruction_unique
  intro k
  have h := congrArg (fun f => LocallyRingedSpace.Γ.map f.op)
    (affineSourceToInvariantOpen_transition n b j k)
  simp only [Scheme.Hom.comp_toLRSHom, op_comp, Functor.map_comp] at h
  have he := congrArg ((invariantOpenSectionsIso n (affineOrbitOpen n ⟨!b, j⟩)).inv ≫ ·) h
  exact congrArg (fun f => f s) he

end FLT.Mazur.CyclicCharacteristicOrbit
