/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryCurveTransportBaseChange
public import FLT.Mazur.CyclicBoundaryAmpleBaseChangeTower
public import FLT.Mazur.CyclicBoundaryAmpleCurveModuli

/-!
# Ample chart transport retains the actual curve tower comparison

The full equal-composite curve isomorphism induces the inverse of the
cartesian tower comparison on ample charts. The proof keeps all original
labels and applies over arbitrary bases.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] faithfulCurveTransportIso baseChangeCompEqIso
variable {S T U : Scheme} (g : T ⟶ S) (h : U ⟶ T)
  (E : GeneralizedEllipticCurve S)
  [IsSeparated E.group.hom] [SmoothOfRelativeDimension 1 E.group.hom]
  (n : ℕ) [NeZero n]

local instance curveTowerParameter_separated {X Y : Scheme}
    (F : GeneralizedEllipticCurve X) [IsSeparated F.group.hom] (f : Y ⟶ X) :
    IsSeparated (F.baseChange f).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd F.group.hom f))

local instance curveTowerParameter_smooth {X Y : Scheme}
    (F : GeneralizedEllipticCurve X) [SmoothOfRelativeDimension 1 F.group.hom] (f : Y ⟶ X) :
    SmoothOfRelativeDimension 1 (F.baseChange f).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) F.group.hom f
    inferInstance

variable (f : U ⟶ S) (w : f = h ≫ g)
local notation "e" => GeneralizedEllipticCurve.baseChangeCompEqIso E g h f w

omit [SmoothOfRelativeDimension 1 E.group.hom] in
/-- Curve tower transport retains every original faithful parameter label and its base. -/
@[reassoc] theorem faithfulCurveTowerParameter_original :
    (faithfulCurveTransportIso (e) n).hom.left ≫
        faithfulBaseChangeToOriginal h (E.baseChange g).group n ≫
          faithfulBaseChangeToOriginal g E.group n = faithfulBaseChangeToOriginal f E.group n := by
  apply faithfulParameter_left_ext n
  · simp only [Category.assoc, faithfulBaseChangeToOriginal_base]
    erw [faithfulBaseChangeToOriginal_base_assoc h (E.baseChange g).group n]
    erw [← Category.assoc, (faithfulCurveTransportIso (e) n).hom.w]
    rw [← w]
    rfl
  · intro a
    simp only [Category.assoc, faithfulBaseChangeToOriginal_value]
    calc
      _ = (faithfulCurveTransportIso (e) n).hom.left ≫
          (cyclicFaithfulInclusion ((E.baseChange g).baseChange h).group n).left ≫
          (AuxiliaryLevel.value ((E.baseChange g).baseChange h).group (Label n) a).left ≫
          pullback.fst (E.baseChange g).group.hom h ≫ pullback.fst E.group.hom g := by
        have hc := congrArg
          (fun z ↦ (faithfulCurveTransportIso (e) n).hom.left ≫ z ≫
            pullback.fst E.group.hom g)
          (faithfulBaseChangeToOriginal_value h (E.baseChange g).group n a)
        simp only [Category.assoc] at hc
        exact hc
      _ = (cyclicFaithfulInclusion (E.baseChange f).group n).left ≫
          (AuxiliaryLevel.value (E.baseChange f).group (Label n) a).left ≫
          (e).hom.group.left ≫ pullback.fst (E.baseChange g).group.hom h ≫
            pullback.fst E.group.hom g := by
        have hc := congrArg
          (· ≫ pullback.fst (E.baseChange g).group.hom h ≫ pullback.fst E.group.hom g)
          (faithfulCurveTransportIso_value (e) n a)
        simp only [Category.assoc] at hc
        exact hc
      _ = _ := by
        rw [baseChangeCompEqIso_group_fst]
        rfl

/-- The actual full curve tower comparison retains the original ample parameter. -/
@[reassoc] theorem ampleCurveTowerParameter_original :
    ampleCurveTransport (e) n ≫ ampleBaseChangeToOriginal h (E.baseChange g) n ≫
      ampleBaseChangeToOriginal g E n = ampleBaseChangeToOriginal f E n := by
  apply (cancel_mono (ampleParameterOpen E n).ι).mp
  simp only [Category.assoc, ampleBaseChangeToOriginal_inclusion,
    ampleBaseChangeToOriginal_inclusion_assoc, ampleCurveTransport_inclusion_assoc,
    faithfulCurveTowerParameter_original]

/-- The cartesian ample tower comparison is induced by the actual full curve comparison. -/
theorem ampleBaseChangeTowerIso_inv_eq_curveTransport :
    (ampleBaseChangeTowerIso g h E n).inv =
      ampleCurveTransport (E.baseChangeCompEqIso g h (h ≫ g) rfl) n := by
  apply (ampleBaseChangeTower_isPullback g h E n).hom_ext
  · have hi := congrArg ((ampleBaseChangeTowerIso g h E n).inv ≫ ·)
      (ampleBaseChangeTowerIso_original g h E n)
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at hi
    exact hi.symm.trans (ampleCurveTowerParameter_original g h E n (h ≫ g) rfl).symm
  · have hi := congrArg ((ampleBaseChangeTowerIso g h E n).inv ≫ ·)
      (ampleBaseChangeTowerIso_base g h E n)
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at hi
    exact hi.symm.trans
      (ampleCurveTransport_base (E.baseChangeCompEqIso g h (h ≫ g) rfl) n).symm

end FLT.Mazur.CyclicBoundaryParameter
