/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicIntegerSourceCover
public import FLT.Mazur.CyclicCharacteristicResidualSectionComparison

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

/-- The locally ringed source projection factors through the exact characteristic open. -/
def integerSourceToInvariantOpen :
    (integerSourceOpen n b).toScheme.toLocallyRingedSpace ⟶
      invariantOpenSpace n (integerOpen n (chartInteger (!b))) :=
  LocallyRingedSpace.IsOpenImmersion.lift
    ((invariantLocallyRingedSpace n).ofRestrict
      (integerOpen n (chartInteger (!b))).isOpenEmbedding)
    ((integerSourceOpen n b).ι.toLRSHom ≫ invariantLocallyRingedProjection n) (by
      rintro _ ⟨x, rfl⟩
      refine ⟨⟨projection n x.val, x.property⟩, ?_⟩
      change projection n x.val = (invariantLocallyRingedProjection n).base x.val
      rw [invariantLocallyRingedProjection_base]
      rfl)

/-- The factor retains the original ambient locally ringed projection. -/
@[reassoc] theorem integerSourceToInvariantOpen_comp :
    integerSourceToInvariantOpen n b ≫ (invariantLocallyRingedSpace n).ofRestrict
      (integerOpen n (chartInteger (!b))).isOpenEmbedding =
        (integerSourceOpen n b).ι.toLRSHom ≫ invariantLocallyRingedProjection n :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

/-- The selected source chart has the original characteristic locally ringed factor. -/
@[reassoc] theorem integerSourceToInvariantOpen_selected :
    (selectedToIntegerSource n b).toLRSHom ≫ integerSourceToInvariantOpen n b =
      chartToInvariantOpen n (!b) := by
  rw [← cancel_mono ((invariantLocallyRingedSpace n).ofRestrict
    (integerOpen n (chartInteger (!b))).isOpenEmbedding)]
  rw [Category.assoc, integerSourceToInvariantOpen_comp, chartToInvariantOpen_comp,
    ← Category.assoc, ← Scheme.Hom.comp_toLRSHom, selectedToIntegerSource_comp]
  rfl

/-- The opposite source chart has the original opposite locally ringed factor. -/
@[reassoc] theorem integerSourceToInvariantOpen_opposite :
    (oppositeToIntegerSource n b).toLRSHom ≫ integerSourceToInvariantOpen n b =
      oppositeToInvariantOpen n b := by
  rw [← cancel_mono ((invariantLocallyRingedSpace n).ofRestrict
    (integerOpen n (chartInteger (!b))).isOpenEmbedding)]
  rw [Category.assoc, integerSourceToInvariantOpen_comp, oppositeToInvariantOpen_comp,
    ← Category.assoc, ← Scheme.Hom.comp_toLRSHom, oppositeToIntegerSource_comp]
  rfl

/-- Actual invariant sections pulled back to the original source open. -/
def integerSourceInvariantSectionMap :
    (invariantSheaf n).obj.obj (op (integerOpen n (chartInteger (!b)))) ⟶
      Γ((integerSourceOpen n b).toScheme, ⊤) :=
  (invariantOpenSectionsIso n _).inv ≫
    LocallyRingedSpace.Γ.map (integerSourceToInvariantOpen n b).op

/-- The selected component pullback is the actual characteristic section comparison. -/
theorem integerSourceInvariantSectionMap_selected :
    integerSourceInvariantSectionMap n b ≫ (selectedToIntegerSource n b).appTop =
      chartInvariantSectionMap n (!b) := by
  have h := congrArg (fun f => LocallyRingedSpace.Γ.map f.op)
    (integerSourceToInvariantOpen_selected n b)
  change LocallyRingedSpace.Γ.map ((integerSourceToInvariantOpen n b).op ≫
    (selectedToIntegerSource n b).toLRSHom.op) = _ at h
  rw [Functor.map_comp] at h
  exact congrArg ((invariantOpenSectionsIso n _).inv ≫ ·) h

/-- The opposite component pullback is the actual opposite section comparison. -/
theorem integerSourceInvariantSectionMap_opposite :
    integerSourceInvariantSectionMap n b ≫ (oppositeToIntegerSource n b).appTop =
      oppositeInvariantSectionMap n b := by
  have h := congrArg (fun f => LocallyRingedSpace.Γ.map f.op)
    (integerSourceToInvariantOpen_opposite n b)
  change LocallyRingedSpace.Γ.map ((integerSourceToInvariantOpen n b).op ≫
    (oppositeToIntegerSource n b).toLRSHom.op) = _ at h
  rw [Functor.map_comp] at h
  exact congrArg ((invariantOpenSectionsIso n _).inv ≫ ·) h

end FLT.Mazur.CyclicCharacteristicOrbit
