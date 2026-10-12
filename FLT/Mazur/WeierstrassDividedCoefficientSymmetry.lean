/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.CartesianCoefficientSymmetry
public import FLT.Mazur.WeierstrassDividedGlobalCoefficientCartesian

/-!
# Semilinear coefficient symmetries of the actual finite model and action

Lift the coefficient operation through the original Cartesian model and
its actual smooth action domain. Naturality proves equivariance of the
constructed integral action; the action comparison is not a hypothesis.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n) (S : Type u) [CommRing S] [Algebra R S]
local notation "V" => W.map (algebraMap R S)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "fst" => pullback.fst q base
local notation "snd" => pullback.snd q base
local notation "f" => integralSmoothStructure W
local notation "fS" => integralSmoothStructure V
local notation "c" => finiteGlobalCoefficientActionProduct hπ data j hj S
local notation "a" => finiteGlobalCoefficientAction hπ data j hj S
variable (σ : Spec (.of S) ⟶ Spec (.of S))
  (hσ : σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) =
    Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- The genuine action domain is Cartesian over the original coefficient spectrum. -/
theorem finiteGlobalCoefficientDomain_isPullback :
    IsPullback c (pullback.snd fS fst ≫ fst) (pullback.snd f base ≫ base) q :=
  (finiteGlobalCoefficientActionProduct_isPullback hπ data j hj S).paste_vert
    (IsPullback.of_hasPullback q base).flip

/-- Change coefficients on the whole original finite model. -/
def finiteGlobalCoefficientSymmetry :
    finiteGlobalTensorModel hπ data S j hj ⟶ finiteGlobalTensorModel hπ data S j hj :=
  CartesianCoefficientSymmetry.map (IsPullback.of_hasPullback q base).flip σ hσ

/-- The model symmetry covers the specified coefficient operation. -/
@[reassoc] theorem finiteGlobalCoefficientSymmetry_structure :
    finiteGlobalCoefficientSymmetry hπ data j hj S σ hσ ≫ fst = fst ≫ σ :=
  CartesianCoefficientSymmetry.map_coefficient _ _ _

/-- The original integral model is fixed by coefficient symmetry. -/
@[reassoc] theorem finiteGlobalCoefficientSymmetry_projection :
    finiteGlobalCoefficientSymmetry hπ data j hj S σ hσ ≫ snd = snd :=
  CartesianCoefficientSymmetry.map_original _ _ _

/-- Change coefficients on the actual two-input action domain. -/
def finiteGlobalCoefficientDomainSymmetry : pullback fS fst ⟶ pullback fS fst :=
  CartesianCoefficientSymmetry.map
    (finiteGlobalCoefficientDomain_isPullback hπ data j hj S) σ hσ

/-- The domain symmetry retains the original action inputs. -/
@[reassoc] theorem finiteGlobalCoefficientDomainSymmetry_projection :
    finiteGlobalCoefficientDomainSymmetry hπ data j hj S σ hσ ≫ c = c :=
  CartesianCoefficientSymmetry.map_original _ _ _

/-- The domain symmetry retains the coefficient operation on the model input. -/
@[reassoc] theorem finiteGlobalCoefficientDomainSymmetry_structure :
    finiteGlobalCoefficientDomainSymmetry hπ data j hj S σ hσ ≫ pullback.snd fS fst ≫ fst =
      pullback.snd fS fst ≫ fst ≫ σ := by
  simpa only [finiteGlobalCoefficientDomainSymmetry, Category.assoc] using
    CartesianCoefficientSymmetry.map_coefficient
    (finiteGlobalCoefficientDomain_isPullback hπ data j hj S) σ hσ

/-- The actual whole finite-model action commutes with semilinear coefficient transport. -/
theorem finiteGlobalCoefficientAction_symmetry :
    finiteGlobalCoefficientDomainSymmetry hπ data j hj S σ hσ ≫ a =
      a ≫ finiteGlobalCoefficientSymmetry hπ data j hj S σ hσ := by
  apply CartesianCoefficientSymmetry.map_naturality
    (finiteGlobalCoefficientDomain_isPullback hπ data j hj S) σ hσ
    (IsPullback.of_hasPullback q base).flip a (finiteGlobalAction hπ data j hj)
  · exact finiteGlobalCoefficientAction_projection hπ data j hj S
  · rw [finiteGlobalCoefficientAction_structure, pullback.condition]

/-- An involutive coefficient operation squares to the identity on the whole finite model. -/
@[reassoc] theorem finiteGlobalCoefficientSymmetry_involutive (hσσ : σ ≫ σ = 𝟙 _) :
    finiteGlobalCoefficientSymmetry hπ data j hj S σ hσ ≫
      finiteGlobalCoefficientSymmetry hπ data j hj S σ hσ = 𝟙 _ :=
  CartesianCoefficientSymmetry.map_involutive _ _ _ hσσ

/-- The actual action-domain symmetry satisfies the same involution law. -/
@[reassoc] theorem finiteGlobalCoefficientDomainSymmetry_involutive (hσσ : σ ≫ σ = 𝟙 _) :
    finiteGlobalCoefficientDomainSymmetry hπ data j hj S σ hσ ≫
      finiteGlobalCoefficientDomainSymmetry hπ data j hj S σ hσ = 𝟙 _ :=
  CartesianCoefficientSymmetry.map_involutive _ _ _ hσσ

end FLT.Mazur.WeierstrassDividedDepth
