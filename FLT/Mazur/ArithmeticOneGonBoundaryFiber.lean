/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonFiberTorus
public import FLT.Mazur.ArithmeticOneGonOriginalFiber

/-!
# Full original pinching comparisons in arithmetic degenerations

Every field-valued zero-parameter test of the arithmetic family is the
original one-gon as a generalized elliptic curve, retaining its whole action.
The coefficient ring and the field may have different characteristics.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.ArithmeticOneGonBoundaryFiber

open OneGonSmoothing ArithmeticOneGonGeneralizedCurve

variable {R : Type} [CommRing R] (K : Type) [Field K] [Algebra R K]
  (t : R) (ht : IsUnit (1 + 432 * t)) (hzero : algebraMap R K t = 0)
local notation "E" => PolygonGeneralizedCurve.curve K 1 Nat.zero_lt_one
  (OneGonNormalization.normalizationOver K) (OneGonNormalization.nodes K)
  (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)
local notation "c" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "F" => GeneralizedEllipticCurve.baseChange (curve t ht) (c)

/-- The whole original pinching on the actual arithmetic field fiber. -/
def wholeIso : (E).curve ≅ (F).curve :=
  Over.isoMk (zeroParameterFiberIso K t hzero) (zeroParameterFiberIso_snd K t hzero)

/-- The corrected original smooth group on the actual arithmetic field fiber. -/
def smoothIso : (E).group ≅ (F).group :=
  (rootsOfUnityTorusIso K).symm ≪≫ ArithmeticOneGonFiberTorus.torusIso K t hzero

instance smoothIso_isMonHom : IsMonHom (smoothIso K t ht hzero).hom := by
  dsimp only [smoothIso, Iso.trans_hom, Iso.symm_hom]
  infer_instance

/-- Each original component retains its corrected arithmetic torus coordinate. -/
@[reassoc] theorem smoothIso_component (i : ZMod 1) :
    PolygonSplitGroup.component K 1 i ≫ (smoothIso K t ht hzero).hom =
      (ArithmeticOneGonFiberTorus.torusIso K t hzero).hom := by
  change PolygonSplitGroup.component K 1 i ≫
    (originalOneGonGroupTorusIso K).hom.hom.hom.hom ≫ _ = _
  rw [originalOneGonGroupTorusIso_component_assoc]

/-- The actual pullback inclusion retains the original smooth-open embedding. -/
@[reassoc] theorem inclusion_fst :
    (F).inclusion.left ≫ pullback.fst (family t).hom (c) =
      pullback.fst (relativeGroup t).X.hom (c) ≫ (relativeGroupInclusion t).left := by
  rw [GeneralizedEllipticCurve.baseChange_inclusion]
  change ((Over.pullback (c)).map (curve t ht).inclusion).left ≫ _ = _
  rw [curve_inclusion]
  exact pullback.lift_fst _ _ _

/-- The original torus in the whole fiber has precisely the constructed smooth projection. -/
theorem whole_torus_fst :
    OneGonGluing.torus K ≫ (zeroParameterFiberIso K t hzero).hom ≫
      pullback.fst (family t).hom (c) =
    (ArithmeticOneGonFiberTorus.torusIso K t hzero).hom.left ≫
      pullback.fst (relativeGroup t).X.hom (c) ≫ (relativeGroupInclusion t).left := by
  rw [zeroParameterFiberIso_equation_fst, torus_zeroFiberIso_group_assoc]
  exact (ArithmeticOneGonFiberTorus.torusIso_inclusion K t hzero).symm

attribute [local irreducible] ArithmeticOneGonFiberTorus.torusIso

/-- The two actual comparisons preserve the original smooth inclusion. -/
theorem inclusion :
    (E).inclusion ≫ (wholeIso K t ht hzero).hom =
      (smoothIso K t ht hzero).hom ≫ (F).inclusion := by
  apply Sigma.hom_ext
  intro i
  simp only [← Category.assoc, smoothIso_component]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change ((PolygonSplitGroup.component K 1 i ≫ (E).inclusion).left ≫
      (zeroParameterFiberIso K t hzero).hom) ≫ _ = _
    rw [originalOneGon_inclusion_component, Category.assoc]
    change OneGonGluing.torus K ≫ (zeroParameterFiberIso K t hzero).hom ≫
      pullback.fst (family t).hom (c) =
      ((ArithmeticOneGonFiberTorus.torusIso K t hzero).hom.left ≫
        (F).inclusion.left) ≫ pullback.fst (family t).hom (c)
    rw [whole_torus_fst, Category.assoc]
    exact congrArg ((ArithmeticOneGonFiberTorus.torusIso K t hzero).hom.left ≫ ·)
      (inclusion_fst K t ht).symm
  · exact (Over.w _).trans (Over.w _).symm

/-- Every arithmetic zero-parameter field fiber is the full original one-gon. -/
def curveIso : (E) ≅ (F) :=
  PolygonGeneralizedCurve.isoOfInclusion K 1 Nat.zero_lt_one
    (OneGonNormalization.normalizationOver K) (OneGonNormalization.nodes K)
    (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)
    (wholeIso K t ht hzero) (smoothIso K t ht hzero) (inclusion K t ht hzero)

/-- The generalized-curve comparison retains the original arithmetic pinching map. -/
theorem curveIso_curve :
    (curveIso K t ht hzero).hom.curve.left = (zeroParameterFiberIso K t hzero).hom := rfl

end FLT.Mazur.ArithmeticOneGonBoundaryFiber
