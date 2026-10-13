/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NeronPolygonRotationAction
public import FLT.Mazur.PolygonSinglePointLineNormalization
public import FLT.Mazur.DivisorLineSectionCompatibility

/-!
# Original marked sections and lines under full polygon rotation

Rotation carries each original marked section to the same unit on the relabeled
component. Its cartesian square supplies the Cartier ideal and positive line
comparison, retaining the actual canonical vanishing section.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonMarkedSections
open PolygonPinching PolygonSinglePointLineNormalization FCurve
open ProjectiveLineActionSpecialization
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] polygonRotation divisorLinePullbackIsoOfEq
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- The full rotation preserves the original coordinate and rotates the component label. -/
@[reassoc] theorem section_rotation (b : ZMod n) (a : Kˣ) (i : Fin n) :
    sectionMap K n p a i ≫ (polygonRotation K hn p q h b).left =
      sectionMap K n p a (rotateIndex b i) := by
  have he := congrArg Over.Hom.left (componentι_polygonRotation K hn p q h b i)
  change unitPoint K a ≫ (torusToComponent K).left ≫
    (componentι K n i).left ≫ p.left ≫ (polygonRotation K hn p q h b).left = _
  rw [show (componentι K n i).left ≫ p.left ≫
      (polygonRotation K hn p q h b).left = _ from he]
  rfl

/-- The rotation square of original marked sections is cartesian on the whole polygon. -/
theorem section_rotation_square (b : ZMod n) (a : Kˣ) (i : Fin n) :
    IsPullback (𝟙 (Spec (.of K))) (sectionMap K n p a i)
      (sectionMap K n p a (rotateIndex b i)) (polygonRotation K hn p q h b).left := by
  let _ : IsIso (polygonRotation K hn p q h b).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (polygonRotationIso K hn p q h b).hom))
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, section_rotation]⟩

/-- Rotation retains the complete Cartier ideal, including the original multiplicity. -/
theorem section_rotation_ideal (b : ZMod n) (a : Kˣ) (i : Fin n) :
    (sectionMap K n p a (rotateIndex b i)).ker.comap
      (polygonRotation K hn p q h b).left = (sectionMap K n p a i).ker := by
  let _ := PolygonSeparated.cocone K n hn p q h
  let _ := isClosedImmersion_section C.hom _ (section_base K n p a (rotateIndex b i))
  have H := (section_rotation_square K n hn p q h b a i).flip
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom, H.isoPullback_hom_fst]

/-- The actual ideal pullback comparison under rotation is invertible. -/
theorem rotationIdealComparison_isIso (b : ZMod n) (a : Kˣ) (i : Fin n) :
    IsIso (idealModulePullbackHom (sectionMap K n p a (rotateIndex b i)).ker
      (polygonRotation K hn p q h b).left) := by
  apply idealModulePullbackHom_isIso_of_cartier _
    (section_cartier K n p hn q h a (rotateIndex b i)).1
  rw [section_rotation_ideal]
  exact (section_cartier K n p hn q h a i).1

/-- Rotation pulls the original relabeled positive marking line back to its source line. -/
irreducible_def rotationLineIso (b : ZMod n) (a : Kˣ) (i : Fin n) :
    (Scheme.Modules.pullback (polygonRotation K hn p q h b).left).obj
      (pointLine K n hn p q h a (rotateIndex b i)) ≅ pointLine K n hn p q h a i := by
  let _ := rotationIdealComparison_isIso K n hn p q h b a i
  exact divisorLinePullbackIsoOfEq _
    (section_cartier K n p hn q h a (rotateIndex b i)).1
    (section_cartier K n p hn q h a i).1 (section_rotation_ideal K n hn p q h b a i)

/-- Rotation preserves the original canonical section of the marking line. -/
theorem rotationLineIso_section (b : ZMod n) (a : Kˣ) (i : Fin n) :
    DivisorLineSectionCompatible (polygonRotation K hn p q h b).left
      (section_cartier K n p hn q h a (rotateIndex b i)).1
      (section_cartier K n p hn q h a i).1 (rotationLineIso K n hn p q h b a i) := by
  let _ := rotationIdealComparison_isIso K n hn p q h b a i
  rw [rotationLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

end FLT.Mazur.PolygonMarkedSections
