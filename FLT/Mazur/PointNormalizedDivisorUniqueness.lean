/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointNormalizedDivisorFiber
public import FLT.Mazur.RelativeRankOneDivisorUniqueness

/-!
# Injectivity of normalized divisors on the actual rank-one locus

If the actual positive divisor bundle has a line direct image, equality of
pointed normalized classes forces equality of the full relative Cartier
ideals. This is an injectivity statement for the actual Abel map, with no
representing scheme or inverse assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
variable {X S : Scheme.{0}} (f : X ⟶ S) [Surjective f]
  (e : S ⟶ X) (he : e ≫ f = 𝟙 S)

/-- One actual rank-one direct image makes equality of pointed classes detect full divisors. -/
theorem pointedDivisor_eq_of_class_eq (D E : Divisor X)
    (hD : Flat (D.val.subschemeι ≫ f)) (hE : Flat (E.val.subschemeι ≫ f))
    (hN : LocallyFreeRankOne ((Scheme.Modules.pushforward f).obj
      (divisorLineBundle D.val D.property)))
    (hc : pointedDivisorClass f e he D = pointedDivisorClass f e he E) : D = E := by
  have ha : abel f D = abel f E := by
    apply (relativeKernelEquiv f e he).injective
    simpa only [← pointedDivisorClass_eq] using hc
  let L := divisorLineBundle D.val D.property
  have hL := D.property.divisorLineBundle_locallyFreeRankOne
  let d : RelativeFiber f L hL := ⟨⟨D, rfl⟩, hD⟩
  let a : RelativeFiber f L hL := ⟨⟨E, ha.symm⟩, hE⟩
  let _ := rankOne_relativeFiber_subsingleton f L hL hN
  exact congrArg (fun B : RelativeFiber f L hL ↦ B.val.val) (Subsingleton.elim d a)

omit [Surjective f] in
/-- Actual relative Cartier divisors whose positive divisor bundles have rank-one direct image. -/
def RankOneRelativeDivisor :=
  {D : Divisor X // Flat (D.val.subschemeι ≫ f) ∧
    LocallyFreeRankOne ((Scheme.Modules.pushforward f).obj
      (divisorLineBundle D.val D.property))}

/-- The pointed Abel map is injective on the actual direct-image rank-one divisor locus. -/
theorem rankOnePointedDivisorClass_injective :
    Function.Injective (fun D : RankOneRelativeDivisor f ↦ pointedDivisorClass f e he D.val) := by
  intro D E hc
  apply Subtype.ext
  exact pointedDivisor_eq_of_class_eq f e he D.val E.val
    D.property.1 E.property.1 D.property.2 hc

end FLT.Mazur.CartierAbel
