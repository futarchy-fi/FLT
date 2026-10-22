/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryOrbitTestComparison
public import FLT.Mazur.SchemeScalarOrbitTestLifts

/-!
# Full invariant equations give original boundary arrows over arbitrary rings

Actual normalized-chart freeness and the prescribed original scalar map
construct the orbit lift. Both endpoint equations then identify its original
boundary comparison. No field or reducedness hypothesis is imposed on the test.
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

/-- Full invariant equations construct the full boundary arrow with both original endpoints. -/
theorem originalBoundary_of_invariant_orbit_test {B : Type} [CommRing B]
    (t : tensorCoordinates ρ s →+* B)
    (ht : let _ := SchemeScalarOrbitComparison.sourceAlgebra ρ s
      ∀ a : invariantCoordinates ρ,
        t (a.val ⊗ₜ[R₀] (1 : Γ(U.toScheme, ⊤))) = t (1 ⊗ₜ[R₀] a.val))
    (z : Spec (.of B) ⟶ pullback f f)
    (hx : tensorTest ρ s t ≫ tensorFirst ρ s ≫ U.ι ≫ first p q (Fin n) o =
      z ≫ pullback.fst f f ≫ J.subschemeι)
    (hy : tensorTest ρ s t ≫ tensorSecond ρ s ≫ U.ι ≫ first p q (Fin n) o =
      z ≫ pullback.snd f f ≫ J.subschemeι) :
    ∃! d : Spec (.of B) ⟶ pullback p J.subschemeι, d ≫ c = z := by
  obtain ⟨w, hw, _⟩ := existsUnique_orbit_test_lift ρ s
    (boundaryChart_action_free n o U e hU) t ht
  exact originalBoundary_of_orbit_test e (Fin n) o U hU J hJ z
    (tensorTest ρ s t) w hw hx hy

omit [IsAffine U.toScheme] in
/-- Proved original scalar fullness supplies every full invariant equation on an arbitrary test. -/
theorem originalChart_full_invariant_test {B : Type} [CommRing B]
    (hfull : Function.Surjective (originalChartScalars e (Fin n) o U hU))
    (t : tensorCoordinates ρ s →+* B) :
    let _ := SchemeScalarOrbitComparison.sourceAlgebra ρ s
    ∀ a : invariantCoordinates ρ,
      t (a.val ⊗ₜ[R₀] (1 : Γ(U.toScheme, ⊤))) = t (1 ⊗ₜ[R₀] a.val) := by
  let _ := SchemeScalarOrbitComparison.sourceAlgebra ρ s
  dsimp only
  intro a
  obtain ⟨r, rfl⟩ := hfull a
  apply congrArg t
  have h := TensorProduct.smul_tmul (R := R₀) r (1 : Γ(U.toScheme, ⊤))
    (1 : Γ(U.toScheme, ⊤))
  have hr : algebraMap R₀ Γ(U.toScheme, ⊤) r = (s r).val := rfl
  simpa only [Algebra.smul_def, mul_one, hr] using h

/-- Scalar fullness constructs original comparison arrows on matching coefficient tests. -/
theorem originalBoundary_of_full_orbit_test {B : Type} [CommRing B]
    (hfull : Function.Surjective (originalChartScalars e (Fin n) o U hU))
    (t : tensorCoordinates ρ s →+* B) (z : Spec (.of B) ⟶ pullback f f)
    (hx : tensorTest ρ s t ≫ tensorFirst ρ s ≫ U.ι ≫ first p q (Fin n) o =
      z ≫ pullback.fst f f ≫ J.subschemeι)
    (hy : tensorTest ρ s t ≫ tensorSecond ρ s ≫ U.ι ≫ first p q (Fin n) o =
      z ≫ pullback.snd f f ≫ J.subschemeι) :
    ∃! d : Spec (.of B) ⟶ pullback p J.subschemeι, d ≫ c = z :=
  originalBoundary_of_invariant_orbit_test e n o U hU J hJ t
    (originalChart_full_invariant_test e n o U hU hfull t) z hx hy

end FLT.Mazur.EquivalenceRelationNormalizedFrames
