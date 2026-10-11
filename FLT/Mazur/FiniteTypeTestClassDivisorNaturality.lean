/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeTestClassDivisor
public import FLT.Mazur.PointNormalizedDivisorBaseChange

/-!
# Full-ideal naturality for independent acyclic classes

The inverse is independent of the finite-type model, and commutes with
arbitrary cartesian maps between test schemes. The lines on the two tests
can be supplied independently; only equality of their relative classes is needed.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X Y S : Scheme.{0}} {a : X ⟶ Y} {f : X ⟶ S}
  {q : Y ⟶ Spec (.of R)} {g : S ⟶ Spec (.of R)}
  [IsProper q] [Flat q] [GeometricallyIntegral q] (h : IsPullback a f q g)
  (c : RelativePic f) (hc : RelativeGeometricAcyclicRankOne f c)

/-- Different original models of the same test class produce the same entire divisor. -/
theorem finiteTypeTestClassDivisor_model_independent
    {R' : Type} [CommRing R'] [Algebra.FiniteType ℤ R']
    {Y' : Scheme.{0}} {a' : X ⟶ Y'} {q' : Y' ⟶ Spec (.of R')}
    [IsProper q'] [Flat q'] [GeometricallyIntegral q']
    {g' : S ⟶ Spec (.of R')} (h' : IsPullback a' f q' g') :
    finiteTypeTestClassDivisor h c hc = finiteTypeTestClassDivisor h' c hc := by
  apply Subtype.ext
  exact (finiteTypeTestClassDivisor_unique h c hc _
    (finiteTypeTestClassDivisor h' c hc).property.1
    (finiteTypeTestClassDivisor_class h' c hc)).symm

variable {R' : Type} [CommRing R'] [Algebra.FiniteType ℤ R']
  {X' Y' S' : Scheme.{0}} {a' : X' ⟶ Y'} {f' : X' ⟶ S'}
  {q' : Y' ⟶ Spec (.of R')} {g' : S' ⟶ Spec (.of R')}
  [IsProper q'] [Flat q'] [GeometricallyIntegral q'] (h' : IsPullback a' f' q' g')
  (c' : RelativePic f') (hc' : RelativeGeometricAcyclicRankOne f' c')
  {p : X' ⟶ X} {b : S' ⟶ S} (H : IsPullback p f' f b)
  (hcc : relativeMap f' f p b H.w.symm c = c')

include hcc in
/-- The full inverse commutes with actual ideal comap for all cartesian maps of test schemes. -/
theorem finiteTypeTestClassDivisor_natural_ideal :
    (finiteTypeTestClassDivisor h' c' hc').val.val =
      (finiteTypeTestClassDivisor h c hc).val.val.comap p := by
  let D := finiteTypeTestClassDivisor h c hc
  let hD : RelativeEffectiveCartier f D.val.val := ⟨D.val.property, D.property.1⟩
  let E := pointedDivisorPullback H D.val hD
  have hE : Flat (E.val.subschemeι ≫ f') := (relativeCartier_originalSquare H D.val.val hD).2
  have hEc : abel f' E = c' := by
    dsimp only [E, pointedDivisorPullback]
    rw [abel_originalSquare H D.val hD]
    exact (congrArg (relativeMap f' f p b H.w.symm)
      (finiteTypeTestClassDivisor_class h c hc)).trans hcc
  exact (congrArg (fun z : Divisor X' ↦ z.val)
    (finiteTypeTestClassDivisor_unique h' c' hc' E hE hEc)).symm

end FLT.Mazur.CartierAbel
