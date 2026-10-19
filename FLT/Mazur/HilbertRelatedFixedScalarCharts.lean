/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPrescribedScalarMorphism
public import FLT.Mazur.HilbertFixedCompleteRefinement
public import FLT.Mazur.RelativeRelationScalarMorphismInvariant

/-!
# Prescribed scalar characters in independently fixed related charts

An original arrow from a complete interior frame constructs a complete affine
refinement inside the independently fixed chart. The size, second label,
original domain and full scalar character remain unchanged.
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
  EquivalenceRelationNormalizedFrames.source first completeInterior Complete scalarMorphism

/-- Refine a related fixed chart while preserving the exact prescribed original scalar map. -/
theorem exists_related_fixed_scalar_chart {K : Type} [Field K]
    (κ : Ω →+* K) (b : Spec (.of K) ⟶ (E).toScheme)
    (hκ : b ≫ scalarMorphism s = Spec.map (CommRingCat.ofHom κ))
    (n : ℕ) (o o' : Fin n)
    (u : Spec (.of K) ⟶ normalizedFullRelationFrames f hL d V c k n o)
    (hu : u ≫ normalizedFullRelationFirst f hL d V c k n o = b ≫ (E).ι)
    (hi : u default ∈ completeInterior («p» := p) («q» := q) (Fin n) o)
    (B : (normalizedFullRelationFrames f hL d V c k n o').Opens)
    (hB : ∀ g : Equiv.Perm (Fin n),
      (normalizedFullRelationAction f hL d V c k n o' g).hom ⁻¹ᵁ B = B)
    (hBW : B ≤ normalizedFullRelationFirst f hL d V c k n o' ⁻¹ᵁ E)
    (v : Spec (.of K) ⟶ B.toScheme) (a : Spec (.of K) ⟶ (relation f hL d V c k).left)
    (ha : a ≫ p = u ≫ normalizedFullRelationFirst f hL d V c k n o)
    (hb : a ≫ q = (v ≫ B.ι) ≫ normalizedFullRelationFirst f hL d V c k n o') :
    ∃ (U : (normalizedFullRelationFrames f hL d V c k n o').Opens)
      (hU : ∀ g : Equiv.Perm (Fin n),
        (normalizedFullRelationAction f hL d V c k n o' g).hom ⁻¹ᵁ U = U)
      (hUB : U ≤ B) (z : Spec (.of K) ⟶ U.toScheme),
      IsAffineOpen U ∧ z ≫ U.ι = v ≫ B.ι ∧
      z ≫ scalarMorphism
        (invariantScalarCoordinates
          (restrictedAction (normalizedFullRelationAction f hL d V c k n o') U hU)
          (normalizedOriginalScalarMap f hL d V c k n o' W U hU (hUB.trans hBW))) =
        Spec.map (CommRingCat.ofHom κ) ∧
      ∀ y ∈ U, y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o' := by
  have hv : (v ≫ B.ι) default ∈ completeInterior («p» := p) («q» := q) (Fin n) o' :=
    (mixed_original_arrow_interior_iff e (Fin n) o o' u (v ≫ B.ι) a ha hb).mp hi
  obtain ⟨U, hU, hUB, z, hA, hz, hC⟩ :=
    exists_fixed_complete_geometric_refinement f hL d V c k n o' B hB v hv
  let b' := v ≫ (normalizedFullRelationFirst f hL d V c k n o').resLE E B hBW
  have hb' : b' ≫ (E).ι = (v ≫ B.ι) ≫
      normalizedFullRelationFirst f hL d V c k n o' := by
    dsimp only [b']
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
  have hκ' : b' ≫ scalarMorphism s = Spec.map (CommRingCat.ofHom κ) := by
    rw [← orbitScalarMorphism_original_arrow eo W b b' a (ha.trans hu) (hb.trans hb'.symm)]
    exact hκ
  have he : z ≫ (normalizedFullRelationFirst f hL d V c k n o').resLE E U
      (hUB.trans hBW) = b' := by
    apply (cancel_mono (E).ι).mp
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, hz, hb']
  refine ⟨U, hU, hUB, z, hA, hz, ?_, hC⟩
  rw [normalizedSource_scalarMorphism_factor, ← Category.assoc, he]
  exact hκ'

end FLT.Mazur.HilbertChart.AffineRestriction
