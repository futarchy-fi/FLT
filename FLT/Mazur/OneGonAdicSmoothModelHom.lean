/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicSmoothGroupRecovery
public import FLT.Mazur.CharacterCoefficientHomDetection

/-!
# Homomorphism laws for the actual finite coefficient smooth model

The chosen closed factor preserves multiplication and the identity. Its
complete-base recovery is the original effective character homomorphism,
and injective character coefficients detect both sides of the group law.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart CharacterSchemeBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]

/-- The descended factor expressed on its intrinsic finite-base character scheme. -/
def smoothModelCharacterFactor : model (smoothModelBase I t ht n) (ZMod n) ⟶
    (smoothModelCurve I t ht n).group :=
  (smoothModelCharacterIso I t ht n).hom ≫ smoothModelFactor I t ht n

/-- Actual geometric recovery identifies the map with the original complete-base homomorphism. -/
theorem smoothModelCharacterFactor_recovery :
    (overIso (smoothModelBase I t ht n) R (ZMod n)).hom ≫
      (Over.pullback (baseMap (smoothModelBase I t ht n) R)).map
        (smoothModelCharacterFactor I t ht n) =
      effectiveSmoothOver I t ht (initialRootsHom n I t ht) ≫
        (smoothModelGroupRecoveryIso I t ht n).hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc]
    change _ ≫ pullback.lift _ _ _ ≫ _ = _
    rw [pullback.lift_fst, ← Category.assoc, overIso_fst,
      smoothModelGroupRecoveryIso_fst]
    change _ ≫ ((smoothModelCharacterIso I t ht n).hom.left ≫
      (smoothModelFactor I t ht n).left) = _
    rw [← Category.assoc, smoothModelCharacterIso_recovery, smoothModelFactor_recovery]
    rfl
  · exact (Over.w _).trans (Over.w _).symm

instance smoothModelCharacterFactor_pullback_isMonHom :
    IsMonHom ((Over.pullback (baseMap (smoothModelBase I t ht n) R)).map
      (smoothModelCharacterFactor I t ht n)) := by
  have he := smoothModelCharacterFactor_recovery I t ht n
  rw [← Iso.eq_inv_comp] at he
  rw [he]
  infer_instance

instance smoothModelCharacterFactor_isMonHom :
    IsMonHom (smoothModelCharacterFactor I t ht n) := by
  let _ : IsSeparated (algebraicCurve I t ht n).group.hom :=
    inferInstanceAs (IsSeparated
      (integralSmoothStructure (equation (algebraicParameter I t ht n))))
  let _ : IsSeparated (smoothModelCurve I t ht n).group.hom :=
    MorphismProperty.pullback_snd _ _ inferInstance
  apply isMonHom_of_pullback (smoothModelBase I t ht n) R (ZMod n)
    Subtype.val_injective (smoothModelCurve I t ht n).group

instance smoothModelFactor_isMonHom : IsMonHom (smoothModelFactor I t ht n) := by
  have he : smoothModelFactor I t ht n =
      (smoothModelCharacterIso I t ht n).inv ≫ smoothModelCharacterFactor I t ht n := by
    simp only [smoothModelCharacterFactor, Iso.inv_hom_id_assoc]
  rw [he]
  infer_instance

/-- The actual descended factor preserves the identity over the finite coefficient base. -/
theorem smoothModelFactor_one :
    η[smoothModelCarrier I t ht n] ≫ smoothModelFactor I t ht n =
      η[(smoothModelCurve I t ht n).group] := IsMonHom.one_hom _

/-- The actual descended factor preserves the full multiplication map over that same base. -/
theorem smoothModelFactor_mul :
    μ[smoothModelCarrier I t ht n] ≫ smoothModelFactor I t ht n =
      (smoothModelFactor I t ht n ⊗ₘ smoothModelFactor I t ht n) ≫
        μ[(smoothModelCurve I t ht n).group] := IsMonHom.mul_hom _

end FLT.Mazur.OneGonAdicCharacterTower
