/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupFiniteFiberTests

/-!
# Evaluate the fixed invariant tests on actual source characters

Realize a character of the original affine coordinate ring as a scheme
point. A point on the stable closed locus annihilates every fixed test;
a nonzero test gives a point outside that locus over the very same field.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type} [Group G] [Finite G] {X : Scheme} [IsAffine X]
  [TopologicalSpace.NoetherianSpace X] (ρ : G →* Aut X)
  (Z : Set X) (hZ : IsClosed Z)
  (hstable : ∀ (g : G) (x : X), x ∈ Z → (ρ g).hom x ∈ Z)
  {K : Type} [Field K]

omit [Finite G] [TopologicalSpace.NoetherianSpace X] in
/-- Realize an original coordinate character without changing its coefficient field. -/
def sourceCharacterMap (w : Γ(X, ⊤) →+* K) : Spec (.of K) ⟶ X :=
  Spec.map (CommRingCat.ofHom w) ≫ X.isoSpec.inv

omit [Finite G] [TopologicalSpace.NoetherianSpace X] in
/-- The realized point has exactly the restricted invariant character. -/
theorem sourceCharacterMap_quotient (w : Γ(X, ⊤) →+* K) :
    sourceCharacterMap w ≫ quotientMap ρ =
      Spec.map (CommRingCat.ofHom (w.comp
        (show invariantCoordinates ρ →+* Γ(X, ⊤) from
          { toFun := fun t ↦ t.val
            map_one' := rfl
            map_mul' := fun _ _ ↦ rfl
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }))) := by
  let _ := SchemeCoordinateAction.coordinateAction ρ
  change (Spec.map (CommRingCat.ofHom w) ≫ X.isoSpec.inv) ≫
    X.isoSpec.hom ≫ FiniteGroupQuotient.quotientMap G Γ(X, ⊤) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  exact (Spec.map_comp _ _).symm

include hstable in
/-- Geometry on the source proves zero values of every fixed invariant test. -/
theorem source_character_tests_vanish (w : Γ(X, ⊤) →+* K)
    (hw : sourceCharacterMap w default ∈ Z) :
    ∀ t ∈ closedOrbitTests ρ Z hZ, w t.val = 0 := by
  have hq : quotientMap ρ (sourceCharacterMap w default) ∈ closedOrbitImage ρ Z hZ := by
    rw [← closedOrbitImage_preimage ρ Z hZ hstable] at hw
    exact hw
  intro t ht
  have hz := (mem_closedOrbitImage_iff_tests ρ Z hZ _).mp hq t ht
  rw [← Scheme.Hom.comp_apply, sourceCharacterMap_quotient] at hz
  change w t.val ∈ (default : Spec (.of K)).asIdeal at hz
  exact hz

include hstable in
/-- A surviving test constructs a geometric source point outside the stable closed locus. -/
theorem source_character_outside_of_test (w : Γ(X, ⊤) →+* K)
    (t : invariantCoordinates ρ) (ht : t ∈ closedOrbitTests ρ Z hZ) (hnt : w t.val ≠ 0) :
    sourceCharacterMap w default ∉ Z :=
  fun hw ↦ hnt (source_character_tests_vanish ρ Z hZ hstable w hw t ht)

end FLT.Mazur.SchemeFiniteGroupQuotient
