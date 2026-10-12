/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearTerminalLaurentConic
public import FLT.Mazur.PrincipalOpenNormalization
public import FLT.Mazur.ProjectiveLineInfinityTorusCover

/-!
# The full arbitrary-root Laurent boundary as an open immersion

Normalize the genuine integral overlap to identify the complete incidence
boundary with the principal open of the original horizontal function.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct LaurentPolynomial Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (π : R)
  (k : ℕ) (b3 b4 b6 : R) (S : Type u) [Field S] [Algebra R S] (r : S)
  (hs : algebraMap R S (π ^ k) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S b6
local notation "C₀" => ConicCoordinate (U).a₁ c
local notation "B" => MiddleConicOpen U c
local notation "T₀" => ScalarExtension W (π ^ k) π b3 b4 b6 S
local notation "D" => S ⊗[R] WeierstrassDilatation.Coordinate W (π ^ (k + 1)) b3 b4 b6
local notation "x" => WeierstrassDilatation.x W (π ^ (k + 1)) b3 b4 b6
local notation "y" => WeierstrassDilatation.y W (π ^ (k + 1)) b3 b4 b6
local notation "t" => coord W (π ^ k) π b3 b4 b6 0
variable (hc : IsUnit (algebraMap R S b6))
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "hsNext" => show algebraMap R S (π ^ (k + 1)) = 0 from by
  rw [pow_succ, map_mul, hp, mul_zero]
local notation "E" => tensorShearTerminalLaurentEquiv W π k b3 b4 b6 S r hp h3 h4 hr hc a ha
local notation "φ" => tensorShearTerminalConicMap W π k b3 b4 b6 S r hs hp h3 h4 hr
local notation "v" => conicBoundaryUnit U c
local notation "tx" => (1 : S) ⊗ₜ[R] x
local notation "ty" => (1 : S) ⊗ₜ[R] y

local notation "ψ" => tensorShearTerminalLaurentConicMap W π k b3 b4 b6 S r
  hs hp h3 h4 hr hc a ha

local notation "s" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "F" => tensorShearConicOpenEquiv W (π ^ k) π b3 b4 b6 S r hs hp h3 h4 hr
local notation "A" => PrincipalOpenTensor.transition S x t (depthOverlapEquiv W π k b3 b4 b6)
/-- The actual depth overlap followed by the entire conic localization comparison. -/
irreducible_def tensorShearTerminalConicOpenEquiv : Localization.Away tx ≃ₐ[S] B :=
  (A).trans F
local notation "O" => tensorShearTerminalConicOpenEquiv W π k b3 b4 b6 S r hs hp h3 h4 hr

/-- The full open comparison restricts every original terminal function. -/
theorem tensorShearTerminalConicOpenEquiv_base (z : D) :
    O (algebraMap D _ z) = φ z := by
  rw [tensorShearTerminalConicOpenEquiv_def]
  rfl

local notation "Q" => Scheme.Spec.mapIso (O).toRingEquiv.toCommRingCatIso.op
local notation "J" => Scheme.Spec.mapIso (E).toRingEquiv.toCommRingCatIso.op
local notation "b" => Spec.map (CommRingCat.ofHom
  (algebraMap (S[T;T⁻¹]) (Localization.Away ((E) tx))))

/-- The actual conic boundary is precisely the normalized original principal inclusion. -/
theorem tensorShearTerminalLaurentConicMap_spec_boundary :
    s = ((Q) ≪≫ (PrincipalOpenNormalization.specIso E tx).symm).hom ≫ b := by
  apply (cancel_mono (J).hom).mp
  rw [Category.assoc]
  rw [← PrincipalOpenNormalization.specIso_inclusion E tx]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change φ ((E).symm ((E) z)) = O (algebraMap D _ z)
  rw [AlgEquiv.symm_apply_apply, tensorShearTerminalConicOpenEquiv_base]

/-- The whole incidence boundary embeds openly into the complete Laurent chart. -/
instance tensorShearTerminalLaurentConicMap_open : IsOpenImmersion s := by
  rw [tensorShearTerminalLaurentConicMap_spec_boundary]
  infer_instance

/-- Its image is the full principal open of the original horizontal generator. -/
theorem tensorShearTerminalLaurentConicMap_range : Set.range s =
    (PrimeSpectrum.basicOpen ((E) tx) : Set (PrimeSpectrum S[T;T⁻¹])) := by
  rw [tensorShearTerminalLaurentConicMap_spec_boundary]
  let H := Q ≪≫ (PrincipalOpenNormalization.specIso E tx).symm
  change Set.range (fun z => b (H.hom z)) = _
  rw [show Set.range (fun z => b (H.hom z)) = Set.range b from by
    simpa only [Function.comp_def, Scheme.Hom.homeomorph_apply] using
      H.hom.homeomorph.surjective.range_comp b]
  exact PrimeSpectrum.localization_away_comap_range _ _

/-- The horizontal denominator differs from the inverse parameter denominator by a unit. -/
theorem tensorShearTerminalLaurentConicMap_denominator : (E) tx =
    (-LaurentPolynomial.C (↑a⁻¹ : S) * LaurentPolynomial.T 1) *
      (1 - LaurentPolynomial.C c * LaurentPolynomial.T (-1) ^ 2) := by
  rw [tensorShearTerminalLaurent_x]
  have ht : (LaurentPolynomial.T 1 : S[T;T⁻¹]) * LaurentPolynomial.T (-1) ^ 2 =
      LaurentPolynomial.T (-1) := by
    rw [pow_two, ← mul_assoc, ← LaurentPolynomial.T_add]
    simp only [show (1 : ℤ) + -1 = 0 from rfl, LaurentPolynomial.T_zero, one_mul]
  calc LaurentPolynomial.C (↑a⁻¹ : S) *
      (LaurentPolynomial.C c * LaurentPolynomial.T (-1) - LaurentPolynomial.T 1) =
      LaurentPolynomial.C (↑a⁻¹ : S) * (LaurentPolynomial.C c *
        (LaurentPolynomial.T 1 * LaurentPolynomial.T (-1) ^ 2) - LaurentPolynomial.T 1) :=
          by rw [ht]
    _ = _ := by ring

/-- The boundary is exactly the inverse image of the full second parameter open. -/
theorem tensorShearTerminalLaurentConicMap_range_inverseParameter : Set.range s =
    (ProjectiveLine.overlapRight S) ⁻¹'
      (PrimeSpectrum.basicOpen (conicParameterPolynomial c) : Set (PrimeSpectrum S[X])) := by
  rw [tensorShearTerminalLaurentConicMap_range]
  ext q
  change (E) tx ∉ q.asIdeal ↔
    LaurentPolynomial.invert (Polynomial.toLaurent (conicParameterPolynomial c)) ∉ q.asIdeal
  rw [tensorShearTerminalLaurentConicMap_denominator]
  simp only [conicParameterPolynomial, map_sub, map_one, map_mul, map_pow,
    Polynomial.toLaurent_C, Polynomial.toLaurent_X, LaurentPolynomial.invert_C,
    LaurentPolynomial.invert_T]
  exact not_congr (q.asIdeal.unit_mul_mem_iff_mem
    (((a⁻¹).isUnit.map LaurentPolynomial.C).neg.mul (LaurentPolynomial.isUnit_T 1)))

end FLT.Mazur.WeierstrassSuccessiveX
