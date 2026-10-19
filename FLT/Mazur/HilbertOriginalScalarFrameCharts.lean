/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPrescribedScalarMorphism
public import FLT.Mazur.HilbertNormalizedOrbitBoundaryCharts

/-!
# Stable affine charts preserve the original scalar character

Any normalized geometric frame over the prescribed orbit domain lies in an
actual stable affine chart. The chart factorization retains its endpoint and
hence its entire original scalar map, even at incomplete boundary points.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeOpenEnvelope
open RelativeRelationOrbit SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
attribute [local irreducible] relation fst snd equivalence

local notation "eo" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen eo W).val
local notation "Ω" => (invariantSheaf eo).obj.obj (op W)
local notation "s" => orbitScalarCoordinates eo W

attribute [local irreducible] invariantSheaf orbitScalarCoordinates
  EquivalenceRelationNormalizedFrames.source first completeInterior Complete
  scalarMorphism finiteTargetOpen

/-- A given normalized frame has an affine chart with its exact original scalar map. -/
theorem exists_original_scalar_frame_chart {F : Type} [Field F]
    (b : Spec (.of F) ⟶ (E).toScheme) (n : ℕ) (o : Fin n)
    (u : Spec (.of F) ⟶ normalizedFullRelationFrames f hL d V c k n o)
    (hu : u ≫ normalizedFullRelationFirst f hL d V c k n o = b ≫ (E).ι) :
    ∃ (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
      (hU : ∀ g : Equiv.Perm (Fin n),
        (normalizedFullRelationAction f hL d V c k n o g).hom ⁻¹ᵁ U = U)
      (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ E)
      (z : Spec (.of F) ⟶ U.toScheme),
      IsAffineOpen U ∧ z ≫ U.ι = u ∧
      z ≫ scalarMorphism
        (invariantScalarCoordinates
          (restrictedAction (normalizedFullRelationAction f hL d V c k n o) U hU)
          (normalizedOriginalScalarMap f hL d V c k n o W U hU hUW)) =
        b ≫ scalarMorphism s := by
  have hx : normalizedFullRelationFirst f hL d V c k n o (u default) ∈ E := by
    change (u ≫ normalizedFullRelationFirst f hL d V c k n o) default ∈ E
    rw [hu]
    exact (b default).property
  obtain ⟨U, hU, hUW, ha, hxU, _, _⟩ :=
    exists_normalized_orbit_boundary_chart f hL d V c k W n o (u default) hx
  have hr : Set.range u ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y default]
    exact hxU
  let z := IsOpenImmersion.lift U.ι u hr
  have hz : z ≫ U.ι = u := IsOpenImmersion.lift_fac _ _ _
  have he : z ≫ (normalizedFullRelationFirst f hL d V c k n o).resLE E U hUW = b := by
    apply (cancel_mono (E).ι).mp
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, hz]
    exact hu
  refine ⟨U, hU, hUW, z, ha, hz, ?_⟩
  rw [normalizedSource_scalarMorphism_factor, ← Category.assoc, he]

end FLT.Mazur.HilbertChart.AffineRestriction
