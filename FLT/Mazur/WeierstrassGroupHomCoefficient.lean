/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientGroup
public import FLT.Mazur.FiniteLocallyFreeDegreeAffine

/-!
# Coefficient extension of an actual cubic group homomorphism

The coefficient group comparisons transport the actual pulled-back map to the
original mapped equations. The resulting square is Cartesian and retains its
finite locally free degree, including extension from rational to local fields.
-/

@[expose] public noncomputable section

open WeierstrassCurve CategoryTheory Limits AlgebraicGeometry MonoidalCategory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  (E V : WeierstrassCurve R) (hE : IsUnit E.Δ) (hV : IsUnit V.Δ)
  (hES : IsUnit (E.map (algebraMap R S)).Δ)
  (hVS : IsUnit (V.map (algebraMap R S)).Δ)
  (f : integralCurveGroup E hE ⟶ integralCurveGroup V hV)

local notation "F" => Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- The actual group homomorphism extended to the original mapped equations. -/
def integralGroupHomCoefficient :
    integralCurveGroup (E.map (algebraMap R S)) hES ⟶
      integralCurveGroup (V.map (algebraMap R S)) hVS :=
  (integralCurveCoefficientGroupIso E hE hES).hom ≫ (F).mapCommGrp.map f ≫
    (integralCurveCoefficientGroupIso V hV hVS).inv

/-- Its underlying scheme map fits the original coefficient square. -/
@[reassoc] theorem integralGroupHomCoefficient_square :
    (integralGroupHomCoefficient E V hE hV hES hVS f).hom.hom.hom.left ≫
        integralCoefficientMorphism V =
      integralCoefficientMorphism E ≫ f.hom.hom.hom.left := by
  change (integralCurveCoefficientBaseChangeIso E).hom ≫
    ((F).map f.hom.hom.hom).left ≫ (integralCurveCoefficientBaseChangeIso V).inv ≫
      integralCoefficientMorphism V = _
  rw [← integralCurveCoefficientBaseChangeIso_fst V, Iso.inv_hom_id_assoc]
  simp only [Over.pullback_map_left]
  erw [pullback.lift_fst]
  exact integralCurveCoefficientBaseChangeIso_fst_assoc E _

/-- The coefficient square is the actual Cartesian base change of the original map. -/
theorem integralGroupHomCoefficient_isPullback :
    IsPullback (integralCoefficientMorphism E)
      (integralGroupHomCoefficient E V hE hV hES hVS f).hom.hom.hom.left
      f.hom.hom.hom.left (integralCoefficientMorphism V) := by
  have H : IsPullback
      ((integralGroupHomCoefficient E V hE hV hES hVS f).hom.hom.hom.left ≫
        integralCurveStructure (V.map (algebraMap R S)))
      (integralCoefficientMorphism E)
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (f.hom.hom.hom.left ≫ integralCurveStructure V) := by
    erw [(integralGroupHomCoefficient E V hE hV hES hVS f).hom.hom.hom.w,
      f.hom.hom.hom.w]
    exact (integralCoefficient_isPullback E).flip
  exact (H.of_right (integralGroupHomCoefficient_square E V hE hV hES hVS f)
    (integralCoefficient_isPullback V).flip).flip

/-- Extending coefficients retains the original finite locally free degree. -/
theorem integralGroupHomCoefficient_degree (d : ℕ)
    (hd : FCurve.FiniteLocallyFreeDegree f.hom.hom.hom.left d) :
    FCurve.FiniteLocallyFreeDegree
      (integralGroupHomCoefficient E V hE hV hES hVS f).hom.hom.hom.left d :=
  FCurve.finiteLocallyFreeDegree_of_isPullback
    (integralGroupHomCoefficient_isPullback E V hE hV hES hVS f) d hd

end FLT.Mazur.WeierstrassIntegralChart
