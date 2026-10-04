/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveCyclicSubgroup
public import FLT.Mazur.PolygonCartierGenerator
public import FLT.Mazur.PolygonCubicVeryAmple

/-!
# Relative ample subgroup divisors and the polygon example

Ampleness uses actual projective embeddings of positive powers of the divisor
line bundle on affine base opens. The exponent can vary with the base open.
The general fiberwise criterion and descent are separate proof obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur
open FCurve.ModuleLineBundleTensorPullback
namespace FCurve
open ProjectiveSpace

/-- On each affine base open, a positive tensor power admits a projective closed embedding. -/
def RelativeAmple {X S : Scheme} (f : X ⟶ S) (L : X.Modules) : Prop :=
  ∀ (U : S.Opens) (hU : IsAffineOpen U), ∃ m > 0,
    Nonempty (VeryAmplePresentation ((f ∣_ U) ≫ hU.isoSpec.hom)
      ((tensorPower L m).restrict (f ⁻¹ᵁ U).ι))

/-- A fixed positive relatively very ample power supplies the local power witnesses. -/
theorem RelativeAmple.of_power {X S : Scheme} {f : X ⟶ S} {L : X.Modules}
    {m : ℕ} (hm : 0 < m) (h : RelativeVeryAmple f (tensorPower L m)) :
    RelativeAmple f L := fun U hU ↦ ⟨m, hm, h U hU⟩

end FCurve
namespace GeneralizedEllipticCurve.FiniteSubgroup
variable {S : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ}

/-- The actual closed-subgroup divisor is Cartier and relatively ample. -/
def IsAmple (H : E.FiniteSubgroup n) : Prop :=
  ∃ hI : FCurve.EffectiveCartier H.ideal,
    FCurve.RelativeAmple E.curve.hom (FCurve.divisorLineBundle H.ideal hI)

end GeneralizedEllipticCurve.FiniteSubgroup
namespace PolygonFiniteSubgroup
open PolygonPinching
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  {C : Over (Spec (.of K))} (p : components K n ⟶ C)
  (hn : 0 < n) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- The standard polygon's actual cyclic subgroup is relatively ample, with exponent three. -/
theorem isAmple : (subgroup K n p hn q h).IsAmple := by
  refine ⟨(relativeCartier K n p hn q h).1, FCurve.RelativeAmple.of_power (by decide : 0 < 3) ?_⟩
  simpa only [subgroup_ideal, PolygonGeneralizedCurve.curve] using
    PolygonCubicSections.divisor_tensorCube_relativeVeryAmple K n hn p q h (fun _ ↦ 1)

end PolygonFiniteSubgroup
end FLT.Mazur
