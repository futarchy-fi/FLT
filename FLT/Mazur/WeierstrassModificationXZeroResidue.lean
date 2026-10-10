/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXScaleOneTensor
public import FLT.Mazur.WeierstrassDilatationResidueDepth

/-!
# The actual initial residue fiber at starting depth zero

Positive total split depth forces all divided coefficients to vanish at
start zero, while the scale specializes to one. Thus the entire original
tensor chart is the slope line with both original tangent factors inverted.
-/

@[expose] public noncomputable section
open IsLocalRing
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hdepth : 0 < depth) (k : ℕ) (hk : k = 0) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6)
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁

include D hk h3 h4 in
/-- Both actual divided linear coefficients vanish at starting depth zero. -/
theorem zeroResidue_linear : residue R b3 = 0 ∧ residue R b4 = 0 := by
  obtain ⟨hb3, hb4⟩ := WeierstrassDilatation.divided_linear_mem D k
    (by omega) b3 b4 h3 h4
  exact ⟨(residue_eq_zero_iff _).mpr hb3, (residue_eq_zero_iff _).mpr hb4⟩

include D hdepth hk h6 in
/-- Positive total depth makes the actual divided constant vanish at start zero. -/
theorem zeroResidue_constant : residue R b6 = 0 :=
  (residue_eq_zero_iff _).mpr
    (WeierstrassDilatation.divided_constant_mem D k (by omega) b6 h6)

/-- The full start-zero tensor chart has its own scale-one normal form. -/
def zeroResidueSlopeEquiv :
    ScalarExtension W (π ^ k) b3 b4 b6 K ≃ₐ[K] SlopeOpen a :=
  scaleOneTensorEquiv W (π ^ k) b3 b4 b6 K
    (by simp only [hk, pow_zero, map_one])
    ((residue_eq_zero_iff _).mpr D.a₂_mem)
    (zeroResidue_linear D k hk b3 b4 h3 h4).1
    (zeroResidue_linear D k hk b3 b4 h3 h4).2
    (zeroResidue_constant D hdepth k hk b6 h6)

/-- The full start-zero comparison retains the original tensor incidence function. -/
theorem zeroResidueSlopeEquiv_t :
    zeroResidueSlopeEquiv D hdepth k hk b3 b4 b6 h3 h4 h6
      ((1 : K) ⊗ₜ[R] t W (π ^ k) b3 b4 b6) = slopeInv a :=
  scaleOneTensorEquiv_t W (π ^ k) b3 b4 b6 K
    (by simp only [hk, pow_zero, map_one])
    ((residue_eq_zero_iff _).mpr D.a₂_mem)
    (zeroResidue_linear D k hk b3 b4 h3 h4).1
    (zeroResidue_linear D k hk b3 b4 h3 h4).2
    (zeroResidue_constant D hdepth k hk b6 h6)

/-- The full start-zero comparison retains the original tensor slope. -/
theorem zeroResidueSlopeEquiv_v :
    zeroResidueSlopeEquiv D hdepth k hk b3 b4 b6 h3 h4 h6
      ((1 : K) ⊗ₜ[R] v W (π ^ k) b3 b4 b6) = slopeZ a :=
  scaleOneTensorEquiv_v W (π ^ k) b3 b4 b6 K
    (by simp only [hk, pow_zero, map_one])
    ((residue_eq_zero_iff _).mpr D.a₂_mem)
    (zeroResidue_linear D k hk b3 b4 h3 h4).1
    (zeroResidue_linear D k hk b3 b4 h3 h4).2
    (zeroResidue_constant D hdepth k hk b6 h6)

/-- The horizontal cubic function remains the ordered tangent product. -/
theorem zeroResidueSlopeEquiv_x :
    zeroResidueSlopeEquiv D hdepth k hk b3 b4 b6 h3 h4 h6
      ((1 : K) ⊗ₜ[R] x W (π ^ k) b3 b4 b6) =
        slopeZ a * (slopeZ a + algebraMap K (SlopeOpen a) a) :=
  scaleOneTensorEquiv_x W (π ^ k) b3 b4 b6 K
    (by simp only [hk, pow_zero, map_one])
    ((residue_eq_zero_iff _).mpr D.a₂_mem)
    (zeroResidue_linear D k hk b3 b4 h3 h4).1
    (zeroResidue_linear D k hk b3 b4 h3 h4).2
    (zeroResidue_constant D hdepth k hk b6 h6)

/-- The vertical cubic function remains that product times the original slope. -/
theorem zeroResidueSlopeEquiv_y :
    zeroResidueSlopeEquiv D hdepth k hk b3 b4 b6 h3 h4 h6
      ((1 : K) ⊗ₜ[R] y W (π ^ k) b3 b4 b6) =
        (slopeZ a * (slopeZ a + algebraMap K (SlopeOpen a) a)) * slopeZ a :=
  scaleOneTensorEquiv_y W (π ^ k) b3 b4 b6 K
    (by simp only [hk, pow_zero, map_one])
    ((residue_eq_zero_iff _).mpr D.a₂_mem)
    (zeroResidue_linear D k hk b3 b4 h3 h4).1
    (zeroResidue_linear D k hk b3 b4 h3 h4).2
    (zeroResidue_constant D hdepth k hk b6 h6)

end FLT.Mazur.WeierstrassModificationX
