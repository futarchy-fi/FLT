/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentFullRecovery
public import FLT.Mazur.CharacterSchemeBaseChangeTower

/-!
# Tower coherence for arbitrary independent stages

The full source and generalized-curve recoveries agree with successive
coefficient changes along the supplied stage inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicIndependentModel
open OneGonAdicCharacterTower Approximation CharacterAlgebraScalarExtension
open OneGonSmoothing CharacterSchemeBaseChange GeneralizedEllipticCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s : Set R)
  (i : (CoefficientStage (base I t ht n s))ᵒᵖ)
  (hi : complementaryInverse I t ht ∈ s)

/-- The stage carrier is intrinsically the character source over its actual finite ring. -/
def stageCharacterIso : model (stageBase I t ht n s i) (ZMod n) ≅
    stageCarrier I t ht n s i :=
  overIso (base I t ht n s) (stageBase I t ht n s i) (ZMod n)


/-- The stage character comparison retains its literal original coefficient projection. -/
@[reassoc] theorem stageCharacterIso_fst :
    (stageCharacterIso I t ht n s i).hom.left ≫
      pullback.fst (carrier I t ht n s).hom (stageBaseMap I t ht n s i) =
        Spec.map (CommRingCat.ofHom
          (coeff (base I t ht n s) (stageBase I t ht n s i) (ZMod n)).toRingHom) :=
  overIso_fst _ _ _

/-- Recovering the stage character comparison gives the actual stage source projection. -/
theorem stageCharacterIso_recovery :
    Spec.map (CommRingCat.ofHom (coeff (stageBase I t ht n s i) R (ZMod n)).toRingHom) ≫
      (stageCharacterIso I t ht n s i).hom.left = stageSourceRecovery I t ht n s i := by
  apply pullback.hom_ext
  · rw [Category.assoc, stageCharacterIso_fst, stageSourceRecovery_fst, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (coeff_tower (base I t ht n s) (stageBase I t ht n s i) R (ZMod n))
  · change (Spec.map _ ≫ (stageCharacterIso I t ht n s i).hom.left) ≫
      (stageCarrier I t ht n s i).hom =
        stageSourceRecovery I t ht n s i ≫ (stageCarrier I t ht n s i).hom
    rw [Category.assoc, (stageCharacterIso I t ht n s i).hom.w,
      (stageSourceRecovery_isPullback I t ht n s i).w]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact (coeff (stageBase I t ht n s i) R (ZMod n)).commutes

/-- Direct source recovery agrees with successive coefficient recovery through the stage. -/
theorem stageFullSourceIso_tower :
    (stageFullSourceIso I t ht n s i).hom =
      (overIso (stageBase I t ht n s i) R (ZMod n)).hom ≫
        (Over.pullback (baseMap (stageBase I t ht n s i) R)).map
          (stageCharacterIso I t ht n s i).hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [stageFullSourceIso_fst]
    simp only [Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_fst]
    rw [← Category.assoc, overIso_fst]
    exact (stageCharacterIso_recovery I t ht n s i).symm
  · exact (Over.w _).trans (Over.w _).symm

end FLT.Mazur.OneGonAdicIndependentModel
