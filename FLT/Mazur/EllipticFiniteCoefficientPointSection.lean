/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFinitePointSectionAction
public import FLT.Mazur.EllipticFiniteModificationSpecialization
public import FLT.Mazur.EllipticCoefficientSmoothSections
public import FLT.Mazur.WeierstrassDividedGlobalCoefficientAction

/-!
# Unrestricted arithmetic points after coefficient extension

Every original point gives an actual point of each coefficient model. Its
projections are prescribed by the proper integral section, and its arithmetic
E₀ translates agree with the already constructed geometric coefficient action.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (S : Type u) [CommRing S] [Algebra A S]
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap A S))
local notation "f" => finiteGlobalStructure hπ data j hj
local notation "fst" => pullback.fst q f
local notation "snd" => pullback.snd q f

/-- An arbitrary original point restricted to the actual coefficient model. -/
def finiteCoefficientPointSection (P : (W.map (algebraMap A K)).toProjective.Point) :
    Spec (.of S) ⟶ finiteGlobalTensorModel hπ data S j hj :=
  pullback.lift (𝟙 _) (q ≫ finitePointSection A hπ data j hj P)
    (by rw [Category.assoc, finitePointSection_structure, Category.comp_id, Category.id_comp])

/-- This coefficient point has the identity as its coefficient structure. -/
@[reassoc] theorem finiteCoefficientPointSection_structure
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    finiteCoefficientPointSection A hπ data j hj S P ≫ fst = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- The original projection is the actual restriction of the unique proper section. -/
@[reassoc] theorem finiteCoefficientPointSection_projection
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    finiteCoefficientPointSection A hπ data j hj S P ≫ snd =
      q ≫ finitePointSection A hπ data j hj P := pullback.lift_snd _ _ _

omit S [CommRing S] [Algebra A S] in
/-- Residue coefficients recover the original unrestricted closed specialization. -/
theorem finiteCoefficientPointSection_residue
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    finiteCoefficientPointSection A hπ data j hj (IsLocalRing.ResidueField A) P =
      finitePointSpecialization A hπ data j hj P := rfl

/-- The original smooth arithmetic parameter is compatible with every coefficient point. -/
theorem finiteCoefficientPointSection_action_condition (P : ellipticE0 A W)
    (Q : (W.map (algebraMap A K)).toProjective.Point) :
    e0SmoothCoefficientSection A W S P ≫ integralSmoothStructure (W.map (algebraMap A S)) =
      finiteCoefficientPointSection A hπ data j hj S Q ≫ fst := by
  rw [e0SmoothCoefficientSection_structure, finiteCoefficientPointSection_structure]

/-- Every coefficient restriction respects arithmetic translation by any original E₀ point. -/
theorem finiteCoefficientPointSection_add (P : ellipticE0 A W)
    (Q : (W.map (algebraMap A K)).toProjective.Point) :
    finiteGlobalCoefficientPointAction hπ data j hj S (e0SmoothCoefficientSection A W S P)
        (finiteCoefficientPointSection A hπ data j hj S Q)
        (finiteCoefficientPointSection_action_condition A hπ data j hj S P Q) =
      finiteCoefficientPointSection A hπ data j hj S (P.val + Q) := by
  apply pullback.hom_ext
  · rw [finiteGlobalCoefficientPointAction_structure, e0SmoothCoefficientSection_structure,
      finiteCoefficientPointSection_structure]
  · simp only [finiteGlobalCoefficientPointAction_projection,
      e0SmoothCoefficientSection_projection, finiteCoefficientPointSection_projection]
    rw [finiteGlobalPointAction_comp hπ data j hj q _ _
      (finitePointSection_action_condition A hπ data j hj P Q), finitePointSection_add]

/-- Equality of modified closed points is preserved by every original E₀ translation. -/
theorem finiteCoefficientPointSection_add_eq (P : ellipticE0 A W)
    (Q T : (W.map (algebraMap A K)).toProjective.Point)
    (h : finiteCoefficientPointSection A hπ data j hj S Q =
      finiteCoefficientPointSection A hπ data j hj S T) :
    finiteCoefficientPointSection A hπ data j hj S (P.val + Q) =
      finiteCoefficientPointSection A hπ data j hj S (P.val + T) := by
  rw [← finiteCoefficientPointSection_add, ← finiteCoefficientPointSection_add]
  congr 1

/-- Translating by E₀ preserves and reflects equality, even at singular specialized points. -/
theorem finiteCoefficientPointSection_add_eq_iff (P : ellipticE0 A W)
    (Q T : (W.map (algebraMap A K)).toProjective.Point) :
    finiteCoefficientPointSection A hπ data j hj S (P.val + Q) =
        finiteCoefficientPointSection A hπ data j hj S (P.val + T) ↔
      finiteCoefficientPointSection A hπ data j hj S Q =
        finiteCoefficientPointSection A hπ data j hj S T := by
  constructor
  · intro h
    have he := finiteCoefficientPointSection_add_eq A hπ data j hj S (-P) _ _ h
    simpa only [AddSubgroup.coe_neg, neg_add_cancel_left] using he
  · exact finiteCoefficientPointSection_add_eq A hπ data j hj S P Q T

end FLT.Mazur.WeierstrassDividedDepth
