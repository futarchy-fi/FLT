/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeAcyclicDivisorMap
public import FLT.Mazur.ClosedIdealCartesianDegree

/-!
# Full acyclic divisors across different finite-type coefficient models

A cartesian map between two test curves transports the actual full divisor.
The proper models may live over different finite-type integer rings. This is
needed when comparing the original family with a localized coefficient model.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard ClosedIdealCover
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R']
  {X Y S X' Y' S' : Scheme} {a : X ⟶ Y} {f : X ⟶ S}
  {q : Y ⟶ Spec (.of R)} {g : S ⟶ Spec (.of R)}
  [IsProper q] [Flat q] [GeometricallyIntegral q] (h : IsPullback a f q g)
  {a' : X' ⟶ Y'} {f' : X' ⟶ S'} {q' : Y' ⟶ Spec (.of R')}
  {g' : S' ⟶ Spec (.of R')} [IsProper q'] [Flat q'] [GeometricallyIntegral q']
  (h' : IsPullback a' f' q' g') {p : X' ⟶ X} {b : S' ⟶ S}
  (H : IsPullback p f' f b)

/-- Transport an acyclic divisor between independently specified proper coefficient models. -/
def finiteTypeAcyclicDivisorCartesianMap (D : AcyclicRankOneRelativeDivisor f) :
    AcyclicRankOneRelativeDivisor f' := by
  let _ : IsProper f := MorphismProperty.of_isPullback h inferInstance
  exact finiteTypeTestClassDivisor h'
    (relativeMap f' f p b H.w.symm (abel f D.val))
    (relativeGeometricAcyclicRankOne_map _ H (finiteTypeTestAbel h D).property)

/-- The transported class is the original class pulled along the given cartesian map. -/
theorem finiteTypeAcyclicDivisorCartesianMap_class (D : AcyclicRankOneRelativeDivisor f) :
    abel f' (finiteTypeAcyclicDivisorCartesianMap h h' H D).val =
      relativeMap f' f p b H.w.symm (abel f D.val) := by
  unfold finiteTypeAcyclicDivisorCartesianMap
  exact finiteTypeTestClassDivisor_class _ _ _

/-- The entire ideal, including its nilpotent structure, is retained by transport. -/
theorem finiteTypeAcyclicDivisorCartesianMap_ideal (D : AcyclicRankOneRelativeDivisor f) :
    (finiteTypeAcyclicDivisorCartesianMap h h' H D).val.val = D.val.val.comap p := by
  let _ : IsProper f := MorphismProperty.of_isPullback h inferInstance
  have hd := finiteTypeTestClassDivisor_natural_ideal h
    (finiteTypeTestAbel h D).val (finiteTypeTestAbel h D).property h'
    _ (relativeGeometricAcyclicRankOne_map _ H (finiteTypeTestAbel h D).property) H rfl
  change (finiteTypeAcyclicDivisorCartesianMap h h' H D).val.val = _ at hd
  rw [finiteTypeTestAbel_left_inv] at hd
  exact hd

/-- Degree is preserved for the full transported closed subscheme. -/
theorem finiteTypeAcyclicDivisorCartesianMap_degree (D : AcyclicRankOneRelativeDivisor f)
    (d : ℕ) (hd : FiniteLocallyFreeDegree (D.val.val.subschemeι ≫ f) d) :
    FiniteLocallyFreeDegree
      ((finiteTypeAcyclicDivisorCartesianMap h h' H D).val.val.subschemeι ≫ f') d := by
  rw [finiteTypeAcyclicDivisorCartesianMap_ideal]
  exact restriction_degree D.val.val _ H d hd

/-- An isomorphic total-space comparison reflects equality of full divisors. -/
theorem finiteTypeAcyclicDivisorCartesianMap_injective [IsIso p] :
    Function.Injective (finiteTypeAcyclicDivisorCartesianMap h h' H) := by
  intro D E he
  apply acyclicRankOneRelativeDivisor_ext
  have hi := congrArg (fun z : AcyclicRankOneRelativeDivisor f' ↦ z.val.val.comap (inv p)) he
  simpa only [finiteTypeAcyclicDivisorCartesianMap_ideal,
    ← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id,
    Scheme.IdealSheafData.comap_id] using hi

end FLT.Mazur.CartierAbel
