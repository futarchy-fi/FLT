/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXTerminalLaurentParameters
public import FLT.Mazur.ProjectiveLineInfinityTorusCover

/-!
# The full terminal boundary in the inverse Laurent chart

The normalized horizontal denominator cuts out precisely the inverse image
of the original second parameter open 1-c*z². The whole Laurent chart is
retained, including points absent from the conic boundary.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
  (h6 : W.a₆ = (π ^ (k + 1)) ^ 2 * b6) (hp : 2 * (k + 1) = n)
local notation "K" => ResidueField R
local notation "c" => residue R b6
local notation "a" => WeierstrassDilatation.residueTangentUnit D
local notation "tx" => WeierstrassDilatation.tensorX W (π ^ (k + 1)) b3 b4 b6 K
local notation "e" => WeierstrassDilatation.residueLaurentEquiv D (k + 1)
  (Nat.zero_lt_succ k) hk b3 b4 b6 h3 h4 h6 hp
local notation "ψ" => residueLaurentConicMap D k hk b3 b4 b6 h3 h4 h6 hp
local notation "s" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))

/-- The full boundary image is the principal open of the original normalized x coordinate. -/
theorem residueLaurentConicMap_range : Set.range s =
    (PrimeSpectrum.basicOpen ((e) tx) : Set (PrimeSpectrum K[T;T⁻¹])) := by
  rw [residueLaurentConicMap_spec_boundary]
  let Q := Scheme.Spec.mapIso
    (residueDividedConicOpenEquiv D k hk b3 b4 b6 h3 h4).toRingEquiv.toCommRingCatIso.op
  let E := Q ≪≫ (PrincipalOpenNormalization.specIso e tx).symm
  change Set.range (fun z =>
    Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away ((e) tx)))) (E.hom z)) = _
  rw [show Set.range (fun z =>
    Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away ((e) tx)))) (E.hom z)) =
      Set.range (Spec.map (CommRingCat.ofHom
        (algebraMap _ (Localization.Away ((e) tx))))) from by
          simpa only [Function.comp_def, Scheme.Hom.homeomorph_apply] using
            E.hom.homeomorph.surjective.range_comp
              (Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away ((e) tx)))))]
  exact PrimeSpectrum.localization_away_comap_range _ _

/-- The horizontal denominator is a unit times the second parameter denominator. -/
theorem residueLaurentConicMap_denominator : (e) tx =
    (-LaurentPolynomial.C (↑a⁻¹ : K) * LaurentPolynomial.T 1) *
      (1 - LaurentPolynomial.C c * LaurentPolynomial.T (-1) ^ 2) := by
  rw [WeierstrassDilatation.residueLaurentEquiv_x]
  have ht : (LaurentPolynomial.T 1 : K[T;T⁻¹]) * LaurentPolynomial.T (-1) ^ 2 =
      LaurentPolynomial.T (-1) := by
    rw [pow_two, ← mul_assoc, ← LaurentPolynomial.T_add]
    simp only [show (1 : ℤ) + -1 = 0 from rfl, LaurentPolynomial.T_zero, one_mul]
  calc LaurentPolynomial.C (↑a⁻¹ : K) *
      (LaurentPolynomial.C c * LaurentPolynomial.T (-1) - LaurentPolynomial.T 1) =
      LaurentPolynomial.C (↑a⁻¹ : K) * (LaurentPolynomial.C c *
        (LaurentPolynomial.T 1 * LaurentPolynomial.T (-1) ^ 2) - LaurentPolynomial.T 1) :=
          by rw [ht]
    _ = _ := by ring

/-- The boundary is exactly the preimage of the entire original second parameter open. -/
theorem residueLaurentConicMap_range_inverseParameter : Set.range s =
    (ProjectiveLine.overlapRight K) ⁻¹'
      (PrimeSpectrum.basicOpen (conicParameterPolynomial c) : Set (PrimeSpectrum K[X])) := by
  rw [residueLaurentConicMap_range]
  ext q
  change (e) tx ∉ q.asIdeal ↔
    LaurentPolynomial.invert (Polynomial.toLaurent (conicParameterPolynomial c)) ∉ q.asIdeal
  rw [residueLaurentConicMap_denominator]
  simp only [conicParameterPolynomial, map_sub, map_one, map_mul, map_pow,
    Polynomial.toLaurent_C, Polynomial.toLaurent_X, LaurentPolynomial.invert_C,
    LaurentPolynomial.invert_T]
  exact not_congr (q.asIdeal.unit_mul_mem_iff_mem
    (((a⁻¹).isUnit.map LaurentPolynomial.C).neg.mul (LaurentPolynomial.isUnit_T 1)))

end FLT.Mazur.WeierstrassSuccessiveX
