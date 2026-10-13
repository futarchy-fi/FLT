/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationIsoInvariants

/-!
# The affine target of the original invariant coefficients

Construct the spectrum and its source map directly from the full relation.
The map coequalizes both original scheme arrows and has exactly the expected
invariant principal preimages. No effective quotient hypothesis is made.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationInvariantSpectrum
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme.{u}} (p q : D ⟶ A)

/-- The affine scheme of functions invariant under the complete original relation. -/
def target : Scheme.{u} := Spec (.of (compatibleFunctions p q))

/-- The original inclusion of invariant regular functions. -/
def inclusion : CommRingCat.of (compatibleFunctions p q) ⟶ Γ(A, ⊤) :=
  CommRingCat.ofHom (compatibleFunctions p q).subtype

/-- The canonical map to the actual spectrum of full invariant coefficients. -/
def projection : A ⟶ target p q := A.toSpecΓ ≫ Spec.map (inclusion p q)

/-- Both original arrows have the same induced coefficient map on full invariants. -/
theorem inclusion_condition : inclusion p q ≫ p.appTop = inclusion p q ≫ q.appTop := by
  ext s
  exact s.property

/-- The constructed map coequalizes complete scheme morphisms, including their sheaf maps. -/
@[reassoc]
theorem projection_condition : p ≫ projection p q = q ≫ projection p q := by
  unfold projection
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp,
    inclusion_condition, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
    Category.assoc]

/-- Normalized global pullback is precisely the original invariant inclusion. -/
theorem projection_coefficients :
    (Scheme.ΓSpecIso (.of (compatibleFunctions p q))).inv ≫ (projection p q).appTop =
      inclusion p q :=
  ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (inclusion p q)

/-- Invariant principal opens pull back to their original source principal opens. -/
theorem projection_preimage_basicOpen (s : compatibleFunctions p q) :
    projection p q ⁻¹ᵁ PrimeSpectrum.basicOpen s = A.basicOpen s.val := by
  rw [projection, Scheme.Hom.comp_preimage]
  change A.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen s.val = _
  exact A.toSpecΓ_preimage_basicOpen s.val

/-- These actual source opens are invariant under the entire relation. -/
theorem projection_basicOpen_invariant (s : compatibleFunctions p q) :
    p ⁻¹ᵁ (projection p q ⁻¹ᵁ PrimeSpectrum.basicOpen s) =
      q ⁻¹ᵁ (projection p q ⁻¹ᵁ PrimeSpectrum.basicOpen s) := by
  rw [projection_preimage_basicOpen]
  exact compatibleFunctions_basicOpen p q s

/-- On an affine source these are actual affine invariant principal neighborhoods. -/
theorem projection_basicOpen_affine [IsAffine A] (s : compatibleFunctions p q) :
    IsAffineOpen (projection p q ⁻¹ᵁ PrimeSpectrum.basicOpen s) := by
  rw [projection_preimage_basicOpen]
  exact compatibleFunctions_basicOpen_affine p q s

end FLT.Mazur.SchemeRelationInvariantSpectrum
