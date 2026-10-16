/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInitialMobiusLaurentReduction
public import FLT.Mazur.LaurentNilpotentReparametrization

/-!
# The full arithmetic retained Laurent coordinate is an automorphism

The original boundary parameter, including the nonconstant opposite-factor
correction and normalized smoothing translation, gives a whole Laurent isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ) (b3 b4 b6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (hs : s ∈ I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "B" => R[T;T⁻¹]
local notation "u" => initialMobiusLaurentUnit W ha s τ hτ b3 b4 b6 I hI hs h2 h3 h4 h6
local notation "G" => laurentNodeRestriction W s b3 b4 b6 I hI ha hs h2 h3 h4 h6

/-- The exact original retained boundary substitution is an algebra automorphism. -/
def initialMobiusLaurentEquiv : B ≃ₐ[R] B :=
  LaurentNilpotentReparametrization.equiv I hI u
    (initialMobiusLaurentUnit_sub_mem W ha s τ hτ b3 b4 b6 I hI hs h2 h3 h4 h6)

local notation "e" => initialMobiusLaurentEquiv W ha s τ hτ b3 b4 b6 I hI hs h2 h3 h4 h6

/-- The constructed equivalence uses the entire arithmetic unit, without truncation. -/
theorem initialMobiusLaurentEquiv_toAlgHom : (e).toAlgHom = LaurentUnitPoints.evalUnit u := rfl

/-- The positive Laurent generator maps to the actual fractional boundary parameter. -/
theorem initialMobiusLaurentEquiv_T : e (LaurentPolynomial.T 1) = (u : B) := by
  change LaurentUnitPoints.evalUnit u (LaurentPolynomial.T 1) = _
  rw [LaurentUnitPoints.evalUnit_T, zpow_one]

/-- The full retained Laurent scheme is reparametrized isomorphically. -/
def initialMobiusLaurentIso : Spec (.of B) ≅ Spec (.of B) :=
  Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op

local notation "E" => initialMobiusLaurentIso W ha s τ hτ b3 b4 b6 I hI hs h2 h3 h4 h6

/-- The exact original boundary factors through the constructed full Laurent isomorphism. -/
@[reassoc] theorem initialMobiusLaurentIso_boundary :
    Spec.map (CommRingCat.ofHom (G).toRingHom) ≫ initialMobiusChart W ha s τ hτ =
      (E).hom ≫ PolygonSmoothing.leftBranchOpen R τ :=
  initialMobiusChart_laurent_boundary W ha s τ hτ b3 b4 b6 I hI hs h2 h3 h4 h6

/-- Reparametrizing the whole original retained boundary recovers the standard polygon edge. -/
@[reassoc] theorem initialMobiusLaurentIso_inv_boundary :
    (E).inv ≫ Spec.map (CommRingCat.ofHom (G).toRingHom) ≫
      initialMobiusChart W ha s τ hτ = PolygonSmoothing.leftBranchOpen R τ := by
  rw [initialMobiusLaurentIso_boundary, Iso.inv_hom_id_assoc]

/-- The original and standard full boundary morphisms have exactly the same scheme points. -/
theorem initialMobiusLaurent_boundary_range :
    Set.range (Spec.map (CommRingCat.ofHom (G).toRingHom) ≫
      initialMobiusChart W ha s τ hτ) = Set.range (PolygonSmoothing.leftBranchOpen R τ) := by
  rw [initialMobiusLaurentIso_boundary]
  change Set.range ((PolygonSmoothing.leftBranchOpen R τ) ∘ (E).hom) = _
  exact (E).hom.homeomorph.surjective.range_comp _

end FLT.Mazur.WeierstrassModificationX
