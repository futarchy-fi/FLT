/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryCurveTransportCoherence
public import FLT.Mazur.CyclicBoundaryAmpleBaseChange

/-!
# Curve transport commutes with actual parameter base change

The cartesian comparison is natural for full curve isomorphisms. Every label
is retained on arbitrary scheme tests, and the ample restriction preserves
the resulting square of actual parameter schemes.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (g : T ⟶ S) {E F : GeneralizedEllipticCurve S}
  [IsSeparated E.group.hom] [IsSeparated F.group.hom]
  (e : E ≅ F) (n : ℕ) [NeZero n]

local instance transportPullback_separated (D : GeneralizedEllipticCurve S)
    [IsSeparated D.group.hom] : IsSeparated (D.baseChange g).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd D.group.hom g))

local instance transportFunctor_separated (D : GeneralizedEllipticCurve S)
    [IsSeparated D.group.hom] : IsSeparated ((baseChangeFunctor g).obj D).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd D.group.hom g))

local notation "e'" => (Functor.mapIso (baseChangeFunctor g) e :
  GeneralizedEllipticCurve.baseChange E g ≅ GeneralizedEllipticCurve.baseChange F g)

/-- Scheme maps to the faithful parameter are determined by their base and all labels. -/
theorem faithfulParameter_left_ext {X : Scheme}
    (f j : X ⟶ (cyclicFaithfulParameter E.group n).left)
    (hb : f ≫ (cyclicFaithfulParameter E.group n).hom =
      j ≫ (cyclicFaithfulParameter E.group n).hom)
    (hv : ∀ a : Label n, f ≫ (cyclicFaithfulInclusion E.group n).left ≫
        (AuxiliaryLevel.value E.group (Label n) a).left =
      j ≫ (cyclicFaithfulInclusion E.group n).left ≫
        (AuxiliaryLevel.value E.group (Label n) a).left) : f = j := by
  let a : Over.mk (f ≫ (cyclicFaithfulParameter E.group n).hom) ⟶
      cyclicFaithfulParameter E.group n := Over.homMk f rfl
  let b : Over.mk (f ≫ (cyclicFaithfulParameter E.group n).hom) ⟶
      cyclicFaithfulParameter E.group n := Over.homMk j hb.symm
  suffices a = b from congrArg Over.Hom.left this
  apply (cancel_mono (cyclicFaithfulInclusion E.group n)).mp
  apply AuxiliaryLevel.homScheme_ext
  intro i
  apply Over.OverMorphism.ext
  exact hv i

/-- The actual faithful curve comparison retains each original scheme-valued label. -/
@[reassoc] theorem faithfulCurveTransportIso_value (a : Label n) :
    (faithfulCurveTransportIso e n).hom.left ≫ (cyclicFaithfulInclusion F.group n).left ≫
        (AuxiliaryLevel.value F.group (Label n) a).left =
      (cyclicFaithfulInclusion E.group n).left ≫
        (AuxiliaryLevel.value E.group (Label n) a).left ≫ e.hom.group.left := by
  simpa only [faithfulCurveTransportIso, Over.comp_left, Over.id_left, Category.id_comp]
    using congrArg Over.Hom.left (faithfulCurveTransport_value e n (𝟙 _) a)

/-- Base change and full curve transport give the same map of faithful parameter schemes. -/
@[reassoc] theorem faithfulCurveTransportIso_baseChange :
    (faithfulCurveTransportIso (e') n).hom.left ≫
        faithfulBaseChangeToOriginal g F.group n =
      faithfulBaseChangeToOriginal g E.group n ≫ (faithfulCurveTransportIso e n).hom.left := by
  apply faithfulParameter_left_ext n
  · simp only [Category.assoc, faithfulBaseChangeToOriginal_base]
    erw [← Category.assoc, (faithfulCurveTransportIso (e') n).hom.w]
    rw [(faithfulCurveTransportIso e n).hom.w, faithfulBaseChangeToOriginal_base]
    rfl
  · intro a
    simp only [Category.assoc, faithfulBaseChangeToOriginal_value,
      faithfulCurveTransportIso_value, faithfulBaseChangeToOriginal_value_assoc]
    erw [faithfulCurveTransportIso_value_assoc]
    change _ ≫ _ ≫ ((Over.pullback g).map e.hom.group).left ≫ _ = _
    simp only [Over.pullback_map_left, pullback.lift_fst]
    rfl

variable [SmoothOfRelativeDimension 1 E.group.hom] [SmoothOfRelativeDimension 1 F.group.hom]

local instance transportPullback_smooth (D : GeneralizedEllipticCurve S)
    [SmoothOfRelativeDimension 1 D.group.hom] :
    SmoothOfRelativeDimension 1 (D.baseChange g).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) D.group.hom g
    inferInstance

local instance transportFunctor_smooth (D : GeneralizedEllipticCurve S)
    [SmoothOfRelativeDimension 1 D.group.hom] :
    SmoothOfRelativeDimension 1 ((baseChangeFunctor g).obj D).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) D.group.hom g
    inferInstance

/-- The same naturality square holds after restricting to the actual ample parameter. -/
@[reassoc] theorem ampleCurveTransport_baseChange :
    ampleCurveTransport (e') n ≫
        ampleBaseChangeToOriginal g F n =
      ampleBaseChangeToOriginal g E n ≫ ampleCurveTransport e n := by
  apply (cancel_mono (ampleParameterOpen F n).ι).mp
  simp only [Category.assoc, ampleBaseChangeToOriginal_inclusion,
    ampleCurveTransport_inclusion, ampleBaseChangeToOriginal_inclusion_assoc]
  erw [ampleCurveTransport_inclusion_assoc]
  exact congrArg ((ampleParameterOpen (E.baseChange g) n).ι ≫ ·)
    (faithfulCurveTransportIso_baseChange g e n)

end FLT.Mazur.CyclicBoundaryParameter
