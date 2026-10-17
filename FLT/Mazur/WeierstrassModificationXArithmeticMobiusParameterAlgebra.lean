/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXArithmeticInitialNormalizedPuncture
public import FLT.Mazur.PolygonSmoothingPunctureGeometry

/-!
# The full initial Mobius parameter on the Laurent algebra

The exact parameter and its inverse both reduce to inversion modulo the
original arithmetic coefficient ideal. Neither full map is replaced by inversion.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages PolygonSmoothing WeierstrassSuccessiveX LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "L" => Q[T;T⁻¹]
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)
local notation "K" => Ideal.map (algebraMap Q L) J
local notation "τ" => arithmeticInitialMobiusSmoothing W ha s π m

/-- The entire algebra equivalence underlying the original Mobius puncture parameter. -/
def arithmeticInitialMobiusEquiv : L ≃ₐ[Q] L :=
  initialMobiusLaurentEquiv (W.map q) (ha.map q) (q s) τ
    (initialTangentSmoothing_factor (W.map q) (ha.map q) (q s))
    (q b3) (q b4) (q b6) J (arithmeticParameterIdeal_nilpotent π m)
    (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
    (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
    (arithmeticCoefficient_mem π m h6)

local notation "E" => arithmeticInitialMobiusEquiv π m W s b3 b4 b6 ha hs h2 h3 h4 h6

/-- The algebra construction retains the exact scheme parameter already installed. -/
theorem arithmeticInitialMobiusEquiv_spec : punctureSpecIso E =
    arithmeticInitialMobiusParameter π m W s b3 b4 b6 ha hs h2 h3 h4 h6 := rfl

/-- Every full Laurent value differs from inversion only in the base coefficient ideal. -/
theorem arithmeticInitialMobiusEquiv_sub_mem (z : L) : E z - invert z ∈ K := by
  apply LaurentNilpotentReparametrization.hom_sub_mem K (E).toAlgHom invert.toAlgHom
  change E (T 1) - invert (T 1) ∈ K
  rw [arithmeticInitialMobiusEquiv, initialMobiusLaurentEquiv_T, invert_T]
  exact initialMobiusLaurentUnit_sub_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- Inverting the full parameter preserves its reciprocal reduction on every Laurent value. -/
theorem arithmeticInitialMobiusEquiv_symm_sub_mem (z : L) :
    (E).symm z - invert z ∈ K := by
  have h := (K).neg_mem
    (arithmeticInitialMobiusEquiv_sub_mem π m W s b3 b4 b6 ha hs h2 h3 h4 h6 ((E).symm z))
  rw [AlgEquiv.apply_symm_apply, neg_sub] at h
  have hi : K ≤ Ideal.comap invert.toAlgHom.toRingHom K := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change invert (algebraMap Q L x) ∈ K
    rw [AlgEquiv.commutes]
    exact Ideal.mem_map_of_mem _ hx
  have hh := hi h
  change invert (invert ((E).symm z) - z) ∈ K at hh
  rw [map_sub, involutive_invert ((E).symm z)] at hh
  exact hh

end FLT.Mazur.WeierstrassModificationX
