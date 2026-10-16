/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormalizedOrbitBoundaryCoefficients
public import FLT.Mazur.HilbertNormalizedCompleteOrbits
public import FLT.Mazur.EquivalenceRelationCompleteInterior

/-!
# Complete stable affine charts inside an original orbit domain

Interior completeness constructs charts whose EVERY point is complete, rather
than only their chosen geometric lift. These charts retain the original domain
and the endpoint-moving action. Coverage outside this interior is not asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (AffineRestriction.fst f hL d V c k)
local notation "q" => Over.Hom.left (AffineRestriction.snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
local notation "eo" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W

/-- Every interior complete point has an actual complete chart inside its original domain. -/
theorem exists_completeInterior_orbit_chart (n : ℕ) (o : Fin n)
    (x : normalizedFullRelationFrames f hL d V c k n o)
    (hx : normalizedFullRelationFirst f hL d V c k n o x ∈ (pullOpen eo W).val)
    (hc : x ∈ completeInterior («p» := p) («q» := q) (Fin n) o) :
    ∃ (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
      (_hU : ∀ σ : Equiv.Perm (Fin n),
        (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)
      (_hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val),
      IsAffineOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) ∧
      Etale (U.ι ≫ normalizedFullRelationFirst f hL d V c k n o) := by
  let Q := completeInterior («p» := p) («q» := q) (Fin n) o ⊓
    normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val
  have hQ : ∀ σ : Equiv.Perm (Fin n),
      (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ Q = Q := by
    intro σ
    change (action e (Fin n) o σ).hom ⁻¹ᵁ
      (completeInterior (Fin n) o ⊓ first p q (Fin n) o ⁻¹ᵁ (pullOpen eo W).val) = _
    rw [Scheme.Hom.preimage_inf, completeInterior_action_invariant,
      first_preimage_stable e (Fin n) o (pullOpen eo W).val (pullOpen_preimage_eq eo W)]
    rfl
  obtain ⟨U, ha, hxU, hUQ, hU, he⟩ :=
    exists_normalized_affine_refinement f hL d V c k n o Q hQ x ⟨hc, hx⟩
  refine ⟨U, hU, hUQ.trans inf_le_right, ha, hxU, ?_, he⟩
  intro y hy
  exact completeInterior_subset (Fin n) o (hUQ hy).1

end FLT.Mazur.HilbertChart.AffineRestriction
