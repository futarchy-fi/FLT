/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryInvariantOrbitTests
public import FLT.Mazur.SchemeScalarOrbitEndpointTests

/-!
# Original boundary arrows from the two actual coefficient characters

The tensor test is constructed from the supplied endpoint characters over the
original relation scalar ring. Full invariant agreement then gives the unique
original boundary arrow, keeping both prescribed endpoints on the entire
coefficient spectrum. Test nilpotents are never discarded.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeScalarOrbitComparison
open EquivalenceRelationOrderedFrames RingPairInvariantFlatScalars
open SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction tensorFirst tensorSecond
  orbitMap tensorTest
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (n : ℕ) (o : Fin n)
  (U : (source p q (Fin n) o).Opens)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme] (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
attribute [local instance] RingPairInvariantFlatScalars.sourceAlgebra
  targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU
local notation "s" => originalChartScalars e (Fin n) o U hU
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
attribute [local irreducible] scalarMorphism

/-- Construct the original scalar tensor test and its boundary arrow from actual characters. -/
theorem originalBoundary_of_coefficient_characters {B : Type} [CommRing B]
    [Algebra (invariants p.appTop.hom q.appTop.hom) B] :
    let _ := SchemeScalarOrbitComparison.sourceAlgebra ρ s
    ∀ (u v : Γ(U.toScheme, ⊤) →ₐ[R₀] B)
      (_ : ∀ a : invariantCoordinates ρ, u a.val = v a.val)
      (z : Spec (.of B) ⟶ pullback f f),
      (Spec.map (CommRingCat.ofHom u.toRingHom) ≫ U.toScheme.isoSpec.inv ≫
        U.ι ≫ first p q (Fin n) o = z ≫ pullback.fst f f ≫ J.subschemeι) →
      (Spec.map (CommRingCat.ofHom v.toRingHom) ≫ U.toScheme.isoSpec.inv ≫
        U.ι ≫ first p q (Fin n) o = z ≫ pullback.snd f f ≫ J.subschemeι) →
      ∃! d : Spec (.of B) ⟶ pullback p J.subschemeι, d ≫ c = z := by
  let _ := SchemeScalarOrbitComparison.sourceAlgebra ρ s
  dsimp only
  intro u v huv z hx hy
  apply originalBoundary_of_invariant_orbit_test e n o U hU J hJ
    (Algebra.TensorProduct.productMap u v).toRingHom ?_ z ?_ ?_
  · dsimp only
    intro a
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one, one_mul] using huv a
  · rw [← Category.assoc, tensorTest_productMap_first, Category.assoc]
    exact hx
  · rw [← Category.assoc, tensorTest_productMap_second, Category.assoc]
    exact hy

end FLT.Mazur.EquivalenceRelationNormalizedFrames
