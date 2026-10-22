/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingAssociator
public import FLT.Mazur.GeneralizedCurveMarkingLineCoherence
public import FLT.Mazur.SectionPointPowerTransport

/-!
# The associator on independently pulled marking lines

The comparison uses the actual iterated group section. Its section equation
allows the associator to enter the same coherence squares as base projection.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPointLineIso tensorPowerIso tensorPowerCongr
variable {S T U : Scheme} (E : GeneralizedEllipticCurve S)
  (g : T ⟶ S) (h : U ⟶ T) (s : 𝟙_ (Over S) ⟶ E.group)
local notation "D" => E.baseChange (h ≫ g)
local notation "F" => GeneralizedEllipticCurve.baseChange (E.baseChange g) h
local notation "sD" => pullSection (h ≫ g) s
local notation "sF" => pullSection h (pullSection g s)
local notation "t" => sD ≫ GeneralizedEllipticCurve.inclusion D
local notation "v" => sF ≫ GeneralizedEllipticCurve.inclusion F
local notation "hI" => And.left (smoothMarking_relativeCartier D sD)
local notation "hJ" => And.left (smoothMarking_relativeCartier F sF)
local notation "e" => E.baseChangeCompIso g h
local instance markingAssociatorLineProper : IsProper (D).curve.hom := (D).family.family.1

/-- The inverse associator retains the independently iterated whole-curve section. -/
theorem smoothMarkingAssociator_sectionSquare :
    (v).left ≫ (e).inv.curve.left = 𝟙 U ≫ (t).left := by
  have hh := smoothMarkingIso_sectionSquare (e) (sD)
  rw [smoothMarkingAssociator_group] at hh
  exact hh

/-- The canonical line comparison on the actual independently iterated marking. -/
def smoothMarkingAssociatorLineIso :
    (pullback (e).inv.curve.left).obj (divisorLineBundle (t).left.ker hI) ≅
      divisorLineBundle (v).left.ker hJ :=
  sectionPointLineIso (smoothMarkingIso_cartesian (e)) (t).left (v).left
    (t).w (v).w (smoothMarkingAssociator_sectionSquare E g h s) hI hJ

/-- The associator line comparison preserves the canonical marking section. -/
theorem smoothMarkingAssociatorLineIso_compatible :
    DivisorLineSectionCompatible (e).inv.curve.left hI hJ
      (smoothMarkingAssociatorLineIso E g h s) := by
  exact sectionPointLineIso_compatible (smoothMarkingIso_cartesian (e)) (t).left (v).left
    (t).w (v).w (smoothMarkingAssociator_sectionSquare E g h s) hI hJ

/-- The independently iterated pole comparison is the power of this same line comparison. -/
theorem smoothMarkingAssociatorPowerIso_eq (m : ℕ) :
    smoothMarkingAssociatorPowerIso E g h s m =
      tensorPowerPullbackComparison (e).inv.curve.left
        (smoothMarkingAssociatorLineIso E g h s) m := by
  apply eq_of_heq
  trans smoothMarkingFamilyPowerIso (e) (sD) m
  · unfold smoothMarkingAssociatorPowerIso
    have transport {A B : Sort _} (hAB : A = B) (x : A) : HEq (hAB.mp x) x := by
      cases hAB
      rfl
    exact transport _ _
  · exact sectionPointPowerIso_heq (smoothMarkingIso_cartesian (e)) (t).left
      (((sD ≫ (e).hom.group) ≫ (F).inclusion).left) (t).w
      (((sD ≫ (e).hom.group) ≫ (F).inclusion).w)
      (smoothMarkingIso_sectionSquare (e) (sD)) hI
      (smoothMarking_relativeCartier (F) (sD ≫ (e).hom.group)).1
      (v).w (smoothMarkingAssociator_sectionSquare E g h s) hJ
      (congrArg (fun z ↦ (z ≫ (F).inclusion).left)
        (smoothMarkingAssociator_group E g h s)) m

end FLT.Mazur.GeneralizedEllipticCurve
