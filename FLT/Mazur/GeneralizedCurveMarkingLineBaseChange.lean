/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingBaseChange
public import FLT.Mazur.SectionSumFieldLength

/-!
# The original marking line under arbitrary base change

Remove the degree-one tensor unitors from the original pole comparison.
This retains the actual divisor line for ampleness and affine-complement arguments.
Its degree on every field fiber is one, without any integrality assumption.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory Scheme.Modules
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback

variable {S T : Scheme} (E : GeneralizedEllipticCurve S) (g : T ⟶ S)
  (s : 𝟙_ (Over S) ⟶ E.group)

/-- Base change retains the actual original marking divisor line, without tensor unitors. -/
def smoothMarkingLineBaseChangeIso :
    (Scheme.Modules.pullback (pullback.fst E.curve.hom g)).obj
      (divisorLineBundle (s ≫ E.inclusion).left.ker (E.smoothMarking_relativeCartier s).1) ≅
        divisorLineBundle (pullSection g s ≫ (E.baseChange g).inclusion).left.ker
          ((E.baseChange g).smoothMarking_relativeCartier (pullSection g s)).1 :=
  (Scheme.Modules.pullback (pullback.fst E.curve.hom g)).mapIso
      (ModuleSheafTensor.rightUnitor _).symm ≪≫
    E.smoothMarkingPowerBaseChangeIso g s 1 ≪≫ ModuleSheafTensor.rightUnitor _

/-- Every original smooth marking on a field-valued generalized curve has degree one. -/
theorem smoothMarkingLine_field_degree {K : Type} [Field K]
    (F : GeneralizedEllipticCurve (Spec (.of K)))
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ F.group) :
    curveSheafDegree F.curve.hom
      (divisorLineBundle (p ≫ F.inclusion).left.ker (F.smoothMarking_relativeCartier p).1) =
        1 := by
  let _ : IsProper F.curve.hom := F.family.family.1
  let t := p ≫ F.inclusion
  let _ : IsFinite (t.left.ker.subschemeι ≫ F.curve.hom) := by
    rw [← sectionImageIso_hom F.curve.hom t.left t.w]
    infer_instance
  rw [divisor_degree_eq_fieldLength, divisorFieldLength_section F.curve.hom t.left t.w,
    Nat.cast_one]

end FLT.Mazur.GeneralizedEllipticCurve
