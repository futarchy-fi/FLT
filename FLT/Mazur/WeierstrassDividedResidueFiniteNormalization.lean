/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedProjectiveLift
public import FLT.Mazur.WeierstrassDividedCompleteResidueNormalization

/-!
# The actual complete residue normalization in every original finite model

Lift the constructed nonsplit residue normalization through the original finite
contraction. Uniqueness proves compatibility with the actual root exchange on
the entire component, including the two node markings and infinity.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  {k : ℕ} (d : Data W π k) (hk : 0 < k) (hres : residue R π = 0)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
variable [hirr : Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "φ" => originalResidueNormalization d hk hres
local notation "q" => originalResidueCompleteNormalization d hk hres
local notation "c" => finiteGlobalContraction hπ data j hj

/-- The constructed complete normalization component in the actual original finite model. -/
def originalResidueFiniteNormalization : scheme Q ⟶ finiteGlobalModel hπ data j hj :=
  projectiveFiniteLift hπ data j hj φ (originalResidueNormalization_x_regular d hk hres) q
    (originalResidueCompleteNormalization_left d hk hres)

/-- Its whole cubic projection is the original complete root normalization. -/
@[reassoc] theorem originalResidueFiniteNormalization_contraction :
    originalResidueFiniteNormalization hπ data j hj d hk hres ≫ c = q :=
  projectiveFiniteLift_contraction hπ data j hj φ
    (originalResidueNormalization_x_regular d hk hres) q
    (originalResidueCompleteNormalization_left d hk hres)

/-- The constructed complete component retains the original residue structure map. -/
@[reassoc] theorem originalResidueFiniteNormalization_base :
    originalResidueFiniteNormalization hπ data j hj d hk hres ≫
        finiteGlobalStructure hπ data j hj =
      toBase Q ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap (ResidueField R) Q).comp (residue R))) := by
  rw [finiteGlobalStructure, originalResidueFiniteNormalization_contraction_assoc,
    originalResidueCompleteNormalization_base]

/-- A complete component map with this original cubic projection is uniquely determined. -/
theorem originalResidueFiniteNormalization_unique
    (f : scheme Q ⟶ finiteGlobalModel hπ data j hj) (hf : f ≫ c = q) :
    f = originalResidueFiniteNormalization hπ data j hj d hk hres :=
  projectiveFiniteLift_unique hπ data j hj φ
    (originalResidueNormalization_x_regular d hk hres) q
    (originalResidueCompleteNormalization_left d hk hres) f _ hf
    (originalResidueFiniteNormalization_contraction hπ data j hj d hk hres)

/-- Actual semilinear root exchange fixes the original finite-model projection everywhere. -/
@[reassoc] theorem originalResidueFiniteNormalization_conjugation :
    nodeTangentLineConjugation V ≫ originalResidueFiniteNormalization hπ data j hj d hk hres =
      originalResidueFiniteNormalization hπ data j hj d hk hres := by
  apply originalResidueFiniteNormalization_unique
  rw [Category.assoc, originalResidueFiniteNormalization_contraction,
    originalResidueCompleteNormalization_conjugation]

end FLT.Mazur.WeierstrassDividedDepth
