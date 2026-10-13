/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NeronPolygonScaling
public import FLT.Mazur.PolygonSinglePointLineNormalization
public import FLT.Mazur.DivisorLineSectionCompatibility

/-!
# Original marked sections and lines under scalar translation

Scaling multiplies the original marking coordinate on the same component.
Its cartesian square supplies the Cartier ideal and positive line
comparison, retaining the actual canonical vanishing section.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonMarkedSections
open PolygonPinching PolygonSinglePointLineNormalization FCurve
open ProjectiveLineActionSpecialization
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] polygonScaling divisorLinePullbackIsoOfEq
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- Scaling multiplies the actual coordinate of a marked projective point. -/
@[reassoc] theorem markedPoint_scaling (b a : Kˣ) :
    PolygonDivisorNormalizationPullback.markedPoint K a ≫ ProjectiveLine.scaling K b =
      PolygonDivisorNormalizationPullback.markedPoint K (b * a) := by
  rw [← ProjectiveLineMarkedCharts.left_point, Category.assoc,
    ProjectiveLine.left_scaling, ← Category.assoc,
    ← ProjectiveLineMarkedCharts.left_point]
  congr 1
  rw [ProjectiveLineMarkedCharts.chartPoint, ProjectiveLine.chartScaling,
    ← Spec.map_comp, ProjectiveLineMarkedCharts.chartPoint]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    simp
  · simp

omit [NeZero n] in
/-- The scalar action retains the component and multiplies the original unit coordinate. -/
@[reassoc] theorem section_scaling (b : Kˣ) (a : Kˣ) (i : Fin n) :
    sectionMap K n p a i ≫ (polygonScaling K hn p q h b).left =
      sectionMap K n p (b * a) i := by
  have he := congrArg Over.Hom.left (componentι_polygonScaling K hn p q h b i)
  change PolygonDivisorNormalizationPullback.markedPoint K a ≫
    (componentι K n i).left ≫ p.left ≫ (polygonScaling K hn p q h b).left = _
  rw [show (componentι K n i).left ≫ p.left ≫
      (polygonScaling K hn p q h b).left = _ from he]
  change PolygonDivisorNormalizationPullback.markedPoint K a ≫
    ProjectiveLine.scaling K b ≫ (componentι K n i ≫ p).left = _
  rw [← Category.assoc, markedPoint_scaling]
  rfl

omit [NeZero n] in
/-- The scaling square of original marked sections is cartesian on the whole polygon. -/
theorem section_scaling_square (b : Kˣ) (a : Kˣ) (i : Fin n) :
    IsPullback (𝟙 (Spec (.of K))) (sectionMap K n p a i)
      (sectionMap K n p (b * a) i) (polygonScaling K hn p q h b).left := by
  let _ : IsIso (polygonScaling K hn p q h b).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (polygonScalingIso K hn p q h b).hom))
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, section_scaling]⟩

/-- Scaling retains the complete Cartier ideal, including the original multiplicity. -/
theorem section_scaling_ideal (b : Kˣ) (a : Kˣ) (i : Fin n) :
    (sectionMap K n p (b * a) i).ker.comap
      (polygonScaling K hn p q h b).left = (sectionMap K n p a i).ker := by
  let _ := PolygonSeparated.cocone K n hn p q h
  let _ := isClosedImmersion_section C.hom _ (section_base K n p (b * a) i)
  have H := (section_scaling_square K n hn p q h b a i).flip
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom, H.isoPullback_hom_fst]

/-- The actual ideal pullback comparison under scaling is invertible. -/
theorem scalingIdealComparison_isIso (b : Kˣ) (a : Kˣ) (i : Fin n) :
    IsIso (idealModulePullbackHom (sectionMap K n p (b * a) i).ker
      (polygonScaling K hn p q h b).left) := by
  apply idealModulePullbackHom_isIso_of_cartier _
    (section_cartier K n p hn q h (b * a) i).1
  rw [section_scaling_ideal]
  exact (section_cartier K n p hn q h a i).1

/-- Scaling pulls the original relabeled positive marking line back to its source line. -/
irreducible_def scalingLineIso (b : Kˣ) (a : Kˣ) (i : Fin n) :
    (Scheme.Modules.pullback (polygonScaling K hn p q h b).left).obj
      (pointLine K n hn p q h (b * a) i) ≅ pointLine K n hn p q h a i := by
  let _ := scalingIdealComparison_isIso K n hn p q h b a i
  exact divisorLinePullbackIsoOfEq _
    (section_cartier K n p hn q h (b * a) i).1
    (section_cartier K n p hn q h a i).1 (section_scaling_ideal K n hn p q h b a i)

/-- Scaling preserves the original canonical section of the marking line. -/
theorem scalingLineIso_section (b : Kˣ) (a : Kˣ) (i : Fin n) :
    DivisorLineSectionCompatible (polygonScaling K hn p q h b).left
      (section_cartier K n p hn q h (b * a) i).1
      (section_cartier K n p hn q h a i).1 (scalingLineIso K n hn p q h b a i) := by
  let _ := scalingIdealComparison_isIso K n hn p q h b a i
  rw [scalingLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

end FLT.Mazur.PolygonMarkedSections
