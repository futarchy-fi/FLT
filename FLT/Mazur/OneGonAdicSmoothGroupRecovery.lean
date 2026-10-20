/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicSmoothModelCharacters
public import FLT.Mazur.OneGonSmoothCoefficientTower
public import FLT.Mazur.OverPullbackTowerGroups

/-!
# The actual smooth-group recovery preserves the group structure

Recovery through the enlarged coefficient ring agrees with the original
smooth group comparison, retaining its specified geometric projection.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart CharacterSchemeBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]

/-- The enlarged coefficient tower has the same original inclusion into the complete ring. -/
theorem smoothModelBaseMap_comp :
    baseMap (smoothModelBase I t ht n) R ≫ smoothModelBaseMap I t ht n =
      baseMap (algebraicBase I t ht n) R := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The complete intrinsic smooth group is the recovery of the enlarged smooth group. -/
def smoothModelGroupRecoveryIso : (integralSmoothGroup (equation t)).X ≅
    (Over.pullback (baseMap (smoothModelBase I t ht n) R)).obj
      (smoothModelCurve I t ht n).group :=
  smoothCoefficientTowerIso (algebraicBase I t ht n) (smoothModelBase I t ht n) R
    (algebraicParameter I t ht n)

instance smoothModelGroupRecoveryIso_isMonHom :
    IsMonHom (smoothModelGroupRecoveryIso I t ht n).hom :=
  smoothCoefficientTowerIso_isMonHom _ _ _ _

/-- Forgetting the group comparison recovers precisely the previous geometric recovery map. -/
@[reassoc] theorem smoothModelGroupRecoveryIso_fst :
    (smoothModelGroupRecoveryIso I t ht n).hom.left ≫
      pullback.fst (smoothModelCurve I t ht n).group.hom
        (baseMap (smoothModelBase I t ht n) R) = smoothModelGroupRecovery I t ht n := by
  apply pullback.hom_ext
  · rw [Category.assoc, smoothModelGroupRecovery_fst]
    exact smoothCoefficientTowerIso_fst_fst (algebraicBase I t ht n)
      (smoothModelBase I t ht n) R (algebraicParameter I t ht n)
  · change ((smoothModelGroupRecoveryIso I t ht n).hom.left ≫
      pullback.fst (smoothModelCurve I t ht n).group.hom
        (baseMap (smoothModelBase I t ht n) R)) ≫
      (smoothModelCurve I t ht n).group.hom =
        smoothModelGroupRecovery I t ht n ≫ (smoothModelCurve I t ht n).group.hom
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have hw := (smoothModelGroupRecoveryIso I t ht n).hom.w
    change (smoothModelGroupRecoveryIso I t ht n).hom.left ≫ pullback.snd _ _ = _ at hw
    rw [hw, (smoothModelGroupRecovery_isPullback I t ht n).w]
    rfl

end FLT.Mazur.OneGonAdicCharacterTower
