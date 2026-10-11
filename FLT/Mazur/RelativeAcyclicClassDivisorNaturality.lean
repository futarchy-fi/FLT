/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeAcyclicClassDivisor
public import FLT.Mazur.PointNormalizedDivisorBaseChange

/-!
# Full-ideal naturality and model independence of class-defined divisors

The canonical full divisor commutes with arbitrary maps of cartesian tests.
Different locally Noetherian models producing the same relative class on
one test produce the same full divisor. Neither comparison assumes a
Noetherian test base or identifies only the reduced support.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {P X T S : Scheme.{0}} [IsLocallyNoetherian S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] [GeometricallyIntegral f] (h : IsPullback p q f g)
  (c : RelativePic f)
  (hc : RelativeGeometricAcyclicRankOne q (relativeMap q f p g h.w.symm c))

/-- Different geometric models giving the same test class give the same full divisor. -/
theorem relativeClassTestDivisor_model_independent
    {Y B : Scheme.{0}} [IsLocallyNoetherian B] {a : P ⟶ Y} {b : Y ⟶ B} {k : T ⟶ B}
    [IsProper b] [Flat b] [GeometricallyIntegral b] (H : IsPullback a q b k)
    (z : RelativePic b)
    (hz : RelativeGeometricAcyclicRankOne q (relativeMap q b a k H.w.symm z))
    (hcz : relativeMap q f p g h.w.symm c = relativeMap q b a k H.w.symm z) :
    relativeClassTestDivisor h c hc = relativeClassTestDivisor H z hz := by
  apply Subtype.ext
  exact (relativeClassTestDivisor_unique h c hc _
    (relativeClassTestDivisor H z hz).property.1
    ((relativeClassTestDivisor_class H z hz).trans hcz.symm)).symm

variable {Q U : Scheme.{0}} {p' : Q ⟶ X} {q' : Q ⟶ U} {g' : U ⟶ S}
  (h' : IsPullback p' q' f g')
  (hc' : RelativeGeometricAcyclicRankOne q' (relativeMap q' f p' g' h'.w.symm c))
  (k : U ⟶ T) (r : Q ⟶ P)
  (hp : r ≫ p = p') (hq : r ≫ q = q' ≫ k) (hg : k ≫ g = g')

include hp hq hg in
/-- Canonical relative-class divisors commute with the full original ideal comap. -/
theorem relativeClassTestDivisor_natural_ideal :
    (relativeClassTestDivisor h' c hc').val.val =
      (relativeClassTestDivisor h c hc).val.val.comap r := by
  let H := originalFamilyMap_isPullback h h' k r hp hq hg
  let D := relativeClassTestDivisor h c hc
  let hD : RelativeEffectiveCartier q D.val.val := ⟨D.val.property, D.property.1⟩
  let E := pointedDivisorPullback H D.val hD
  have hE : Flat (E.val.subschemeι ≫ q') :=
    (relativeCartier_originalSquare H D.val.val hD).2
  have hh : q' ≫ (k ≫ g) = (r ≫ p) ≫ f := by rw [hg, hp, h'.w]
  have hcE : abel q' E = relativeMap q' f p' g' h'.w.symm c := by
    dsimp only [E, pointedDivisorPullback]
    rw [abel_originalSquare H D.val hD]
    dsimp only [D]
    rw [relativeClassTestDivisor_class]
    have he := (relativeMap_comp q' q f r k p g hq.symm h.w.symm hh c).symm
    simpa only [hp, hg] using he
  have he := relativeClassTestDivisor_unique h' c hc' E hE hcE
  exact (congrArg (fun D : Divisor Q ↦ D.val) he).symm

end FLT.Mazur.CartierAbel
