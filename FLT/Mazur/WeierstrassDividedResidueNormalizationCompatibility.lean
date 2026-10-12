/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidueFiniteNormalization
public import FLT.Mazur.WeierstrassDividedGlobalFiniteStep

/-!
# Original open restrictions and finite-stage compatibility

The complete constructed exterior map restricts to the actual unchanged D(x)
map, on all functions. It commutes with each original finite step contraction.
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

local notation "e" => originalResidueFiniteNormalization hπ data j hj d hk hres

/-- The complete lift retains the actual unchanged original D(x) map on its entire preimage. -/
@[reassoc] theorem originalResidueFiniteNormalization_open :
    PrincipalAffineRefinement.inclusion (φ (coord W 2 0)) ≫ left Q ≫ e =
      projectiveFiniteLiftOpen hπ data j hj φ := by
  let H := finiteOriginalXOpen_isPullback hπ data j hj
  let p := Spec.map (CommRingCat.ofHom
    (IsLocalization.Away.map (S := Localization.Away (coord W 2 0))
      («Q» := Localization.Away (φ (coord W 2 0))) φ (coord W 2 0)))
  let f := PrincipalAffineRefinement.inclusion (φ (coord W 2 0)) ≫ left Q ≫ e
  have hf : p ≫ (PrincipalAffineRefinement.inclusion (coord W 2 0) ≫
      integralCurveChart W 2) = f ≫ c := by
    simp only [f, Category.assoc, originalResidueFiniteNormalization_contraction,
      originalResidueCompleteNormalization_left]
    exact RegularPrincipalOpen.map_inclusion_assoc φ (coord W 2 0) (integralCurveChart W 2)
  have hl : H.lift p f hf = p := by simpa using H.lift_fst p f hf
  change f = p ≫ _
  rw [← hl]
  exact (H.lift_snd p f hf).symm

omit hj in
/-- Every actual finite step retains the same complete exterior normalization morphism. -/
@[reassoc] theorem originalResidueFiniteNormalization_step (hs : j + 1 ≤ n) :
    originalResidueFiniteNormalization hπ data (j + 1) hs d hk hres ≫
        finiteGlobalStep hπ data j hs =
      originalResidueFiniteNormalization hπ data j (Nat.le_of_succ_le hs) d hk hres := by
  apply originalResidueFiniteNormalization_unique
  rw [Category.assoc, finiteGlobalStep_contraction, originalResidueFiniteNormalization_contraction]

end FLT.Mazur.WeierstrassDividedDepth
