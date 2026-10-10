/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleSecondNode
public import FLT.Mazur.WeierstrassSuccessiveXResidueMiddle

/-!
# Both ordered attachment nodes inside the actual tensor residue fiber

The original tensor tangent functions define a two-open cover. Each full
neighborhood is the actual node z*u=0 localized at 1-c*z², and both retain
the original horizontal tensor generator.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "c" => residue R b6
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 K
local notation "A" => Coordinate W₀ 0 0 0 0 c
local notation "e" => residueRetainedFiberEquiv D k hk0 hk b3 b4 b6 h3 h4
local notation "v" => tensorCoord W (π ^ k) π b3 b4 b6 K 1
local notation "u" => tensorCoord W (π ^ k) π b3 b4 b6 K 2

/-- The first original tensor tangent neighborhood. -/
abbrev ResidueMiddleFirstOpen := Localization.Away (v + algebraMap K T (residue R W.a₁))

/-- The second original tensor tangent neighborhood. -/
abbrev ResidueMiddleSecondOpen := Localization.Away (-v)

/-- The first entire tensor neighborhood normalizes with its original denominator. -/
def residueMiddleFirstOpenEquiv :
    ResidueMiddleFirstOpen (W := W) (π := π) k b3 b4 b6 ≃ₐ[K] MiddleFirstOpen W₀ c :=
  PrincipalOpenTransport.equiv e _ _ (by
    rw [map_add, residueRetainedFiberEquiv_coord, AlgEquiv.commutes]; rfl)

/-- The second entire tensor neighborhood retains its ordered tangent denominator. -/
def residueMiddleSecondOpenEquiv :
    ResidueMiddleSecondOpen (W := W) (π := π) k b3 b4 b6 ≃ₐ[K] MiddleSecondOpen W₀ c :=
  PrincipalOpenTransport.equiv e _ _ (by rw [map_neg, residueRetainedFiberEquiv_coord])

/-- The first full tensor attachment is the actual localized incidence node. -/
def residueMiddleFirstNodeEquiv :
    ResidueMiddleFirstOpen (W := W) (π := π) k b3 b4 b6 ≃ₐ[K] MiddleNodeOpen c :=
  (residueMiddleFirstOpenEquiv D k hk0 hk b3 b4 b6 h3 h4).trans
    (middleFirstNodeEquiv W₀ c ((residue_eq_zero_iff _).mpr D.a₂_mem)
      (D.a₁_unit.map (residue R)))

/-- The second full tensor attachment is the same node with its opposite orientation. -/
def residueMiddleSecondNodeEquiv :
    ResidueMiddleSecondOpen (W := W) (π := π) k b3 b4 b6 ≃ₐ[K] MiddleNodeOpen c :=
  (residueMiddleSecondOpenEquiv D k hk0 hk b3 b4 b6 h3 h4).trans
    (middleSecondNodeEquiv W₀ c ((residue_eq_zero_iff _).mpr D.a₂_mem)
      (D.a₁_unit.map (residue R)))

/-- The first actual node chart retains the tensor horizontal generator. -/
theorem residueMiddleFirstNodeEquiv_u :
    residueMiddleFirstNodeEquiv D k hk0 hk b3 b4 b6 h3 h4
      (algebraMap T _ u) = middleNodeU c := by
  simp only [residueMiddleFirstNodeEquiv, AlgEquiv.trans_apply,
    residueMiddleFirstOpenEquiv, PrincipalOpenTransport.equiv_base,
    residueRetainedFiberEquiv_coord, middleFirstNodeEquiv_u]

/-- The second actual node chart retains the same tensor horizontal generator. -/
theorem residueMiddleSecondNodeEquiv_u :
    residueMiddleSecondNodeEquiv D k hk0 hk b3 b4 b6 h3 h4
      (algebraMap T _ u) = middleNodeU c := by
  simp only [residueMiddleSecondNodeEquiv, AlgEquiv.trans_apply,
    residueMiddleSecondOpenEquiv, PrincipalOpenTransport.equiv_base,
    residueRetainedFiberEquiv_coord, middleSecondNodeEquiv_u]

omit [IsDomain R] in
include D in
/-- The original two ordered tangent opens cover the whole actual tensor fiber. -/
theorem residue_middle_tangent_cover (p : PrimeSpectrum T) :
    v + algebraMap K T (residue R W.a₁) ∉ p.asIdeal ∨ -v ∉ p.asIdeal := by
  by_cases hv : -v ∈ p.asIdeal
  · left
    intro hd
    have h : algebraMap K T (residue R W.a₁) ∈ p.asIdeal := by
      have he : v + algebraMap K T (residue R W.a₁) + -v =
          algebraMap K T (residue R W.a₁) := by ring
      exact he ▸ p.asIdeal.add_mem hd hv
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h
      ((D.a₁_unit.map (residue R)).map (algebraMap K T)))
  · exact Or.inr hv

end FLT.Mazur.WeierstrassSuccessiveX
