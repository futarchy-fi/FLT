/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCoefficientSymmetry

/-!
# Both original inputs of the semilinear finite-model symmetry

The action-domain operation changes the actual smooth parameter and the
actual model input by their coefficient symmetries. These projection laws
retain arbitrary schemes of points, before any split-fiber identification.
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

/-- Coefficient symmetry of the original extended smooth parameter scheme. -/
def finiteGlobalSmoothCoefficientSymmetry :
    (integralSmoothOpen V).toScheme ⟶ (integralSmoothOpen V).toScheme :=
  CartesianCoefficientSymmetry.map (originalSmoothCoefficientMap_isPullback S W) σ hσ

omit [IsDomain R] [IsBezout R] in
/-- The smooth symmetry covers the exact coefficient operation. -/
@[reassoc] theorem finiteGlobalSmoothCoefficientSymmetry_structure :
    finiteGlobalSmoothCoefficientSymmetry (W := W) S σ hσ ≫ fS = fS ≫ σ :=
  CartesianCoefficientSymmetry.map_coefficient _ _ _

omit [IsDomain R] [IsBezout R] in
/-- Its original smooth parameter projection is unchanged. -/
@[reassoc] theorem finiteGlobalSmoothCoefficientSymmetry_projection :
    finiteGlobalSmoothCoefficientSymmetry (W := W) S σ hσ ≫
      originalSmoothCoefficientMap S W = originalSmoothCoefficientMap S W :=
  CartesianCoefficientSymmetry.map_original _ _ _

/-- The actual first input changes by the smooth coefficient symmetry. -/
@[reassoc] theorem finiteGlobalCoefficientDomainSymmetry_fst :
    finiteGlobalCoefficientDomainSymmetry hπ data j hj S σ hσ ≫ pullback.fst fS fst =
      pullback.fst fS fst ≫ finiteGlobalSmoothCoefficientSymmetry (W := W) S σ hσ := by
  apply CartesianCoefficientSymmetry.map_naturality
    (finiteGlobalCoefficientDomain_isPullback hπ data j hj S) σ hσ
    (originalSmoothCoefficientMap_isPullback S W) (pullback.fst fS fst) (pullback.fst f base)
  · exact (finiteGlobalCoefficientActionProduct_fst hπ data j hj S).symm
  · exact pullback.condition

/-- The actual second input changes by the whole-model coefficient symmetry. -/
@[reassoc] theorem finiteGlobalCoefficientDomainSymmetry_snd :
    finiteGlobalCoefficientDomainSymmetry hπ data j hj S σ hσ ≫ pullback.snd fS fst =
      pullback.snd fS fst ≫ finiteGlobalCoefficientSymmetry hπ data j hj S σ hσ := by
  apply CartesianCoefficientSymmetry.map_naturality
    (finiteGlobalCoefficientDomain_isPullback hπ data j hj S) σ hσ
    (IsPullback.of_hasPullback q base).flip (pullback.snd fS fst) (pullback.snd f base)
  · exact (finiteGlobalCoefficientActionProduct_snd hπ data j hj S).symm
  · rfl

omit [IsDomain R] [IsBezout R] in
/-- The smooth input symmetry is involutive whenever its coefficient operation is. -/
@[reassoc] theorem finiteGlobalSmoothCoefficientSymmetry_involutive (hσσ : σ ≫ σ = 𝟙 _) :
    finiteGlobalSmoothCoefficientSymmetry (W := W) S σ hσ ≫
      finiteGlobalSmoothCoefficientSymmetry (W := W) S σ hσ = 𝟙 _ :=
  CartesianCoefficientSymmetry.map_involutive _ _ _ hσσ

end FLT.Mazur.WeierstrassDividedDepth
