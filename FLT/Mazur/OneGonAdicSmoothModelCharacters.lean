/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicSmoothFactorRecovery
public import FLT.Mazur.CharacterGroupBaseChange

/-!
# Character coordinates on the enlarged smooth model

The finite coefficient enlargement carries the original character group after
base change. Its comparison retains the actual recovery from the complete ring.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace FLT.Mazur.OneGonAdicCharacterTower

open CharacterSchemeBaseChange CharacterAlgebraScalarExtension

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]

instance smoothModelBaseAlgebra :
    Algebra (algebraicBase I t ht n) (smoothModelBase I t ht n) :=
  (Subalgebra.inclusion (algebraicSmoothStage I t ht n).unop.property.1).toAlgebra

instance smoothModelBase_tower :
    IsScalarTower (algebraicBase I t ht n) (smoothModelBase I t ht n) R :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

instance smoothModelCarrierMonObj : MonObj (smoothModelCarrier I t ht n) :=
  inferInstanceAs (MonObj ((Over.pullback (smoothModelBaseMap I t ht n)).obj
    (algebraicCarrier I t ht n)))

/-- The enlarged carrier is the same character group over its enlarged coefficient ring. -/
def smoothModelCharacterIso : model (smoothModelBase I t ht n) (ZMod n) ≅
    smoothModelCarrier I t ht n :=
  overIso (algebraicBase I t ht n) (smoothModelBase I t ht n) (ZMod n)

instance smoothModelCharacterIso_isMonHom :
    IsMonHom (smoothModelCharacterIso I t ht n).hom :=
  CharacterGroupBaseChange.comparison_isMonHom _ _ _

/-- The character comparison retains the initial coefficient projection. -/
@[reassoc] theorem smoothModelCharacterIso_fst :
    (smoothModelCharacterIso I t ht n).hom.left ≫
      pullback.fst (algebraicCarrier I t ht n).hom (smoothModelBaseMap I t ht n) =
        Spec.map (CommRingCat.ofHom
          (coeff (algebraicBase I t ht n) (smoothModelBase I t ht n) (ZMod n)).toRingHom) :=
  overIso_fst _ _ _

/-- Its coefficient projection is exactly the previously constructed source recovery. -/
theorem smoothModelCharacterIso_recovery :
    Spec.map (CommRingCat.ofHom (coeff (smoothModelBase I t ht n) R (ZMod n)).toRingHom) ≫
      (smoothModelCharacterIso I t ht n).hom.left = smoothModelSourceRecovery I t ht n := by
  apply pullback.hom_ext
  · rw [Category.assoc, smoothModelCharacterIso_fst, smoothModelSourceRecovery_fst,
      ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply AddMonoidAlgebra.ringHom_ext
    · intro x
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
        Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        coeff_single]
      rfl
    · intro x
      simp [coeff]
  · change (Spec.map _ ≫ (smoothModelCharacterIso I t ht n).hom.left) ≫
      (smoothModelCarrier I t ht n).hom =
        smoothModelSourceRecovery I t ht n ≫ (smoothModelCarrier I t ht n).hom
    rw [Category.assoc, (smoothModelCharacterIso I t ht n).hom.w,
      (smoothModelSourceRecovery_isPullback I t ht n).w]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact (coeff (smoothModelBase I t ht n) R (ZMod n)).commutes

end FLT.Mazur.OneGonAdicCharacterTower
