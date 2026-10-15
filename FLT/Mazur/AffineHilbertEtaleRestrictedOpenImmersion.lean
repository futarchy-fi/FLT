/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertEtaleRestrictedSheaf
public import FLT.Mazur.AffineHilbertRestrictedOpenImmersion

/-!
# Etale source refinements give original locally ringed open immersions

The full original quotient morphism for an etale source has invertible sheaf comparisons.
This upgrades its known open embedding to an LRS open immersion. It does not
assert that either invariant locally ringed space is represented by a scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "e" => variableChartEquivalenceRelation f hL d V c
local notation "a" => equivalence f hL d V c k

local notation "m" => restrictedInvariantQuotientMap f hL d V c k
variable [Etale V.hom] [Etale k.left]

/-- An open contained in the quotient image is exactly the image of its actual inverse image. -/
theorem etaleQuotientPreimageOpen_image (O : TopologicalSpace.Opens (Orbit e))
    (hO : O ≤ orbitImageOpen e (variableChartRelationSnd f hL d V c).left.isOpenMap
      (etaleSourceImage k.left)) :
    etaleRestrictedSectionImageOpen f hL d V c k (quotientPreimageOpen f hL d V c k O) = O := by
  ext z
  change (∃ w ∈ quotientPreimageOpen f hL d V c k O,
    restrictedOrbitMap f hL d V c k w = z) ↔ z ∈ O
  constructor
  · rintro ⟨w, hw, rfl⟩
    change (m).base w ∈ O at hw
    rwa [restrictedInvariantQuotientMap_apply] at hw
  · intro hz
    have hz' := hO hz
    change ∃ x, (∃ y, k.left y = x) ∧ projection e x = z at hz'
    obtain ⟨_, ⟨y, rfl⟩, hy⟩ := hz'
    refine ⟨projection a y, ?_, ?_⟩
    · change (m).base (projection a y) ∈ O
      rw [restrictedInvariantQuotientMap_apply, restrictedOrbitMap_projection, hy]
      exact hz
    · exact hy

/-- The actual quotient morphism's sheaf component is the constructed descent equivalence. -/
theorem etaleQuotientSheafMap_eq_equiv (O : TopologicalSpace.Opens (Orbit e))
    (hO : O ≤ orbitImageOpen e (variableChartRelationSnd f hL d V c).left.isOpenMap
      (etaleSourceImage k.left)) (t : (invariantSheaf e).obj.obj (op O)) :
    (m).c.app (op O) t = etaleRestrictedSheafImageEquivOn f hL d V c k
      (quotientPreimageOpen f hL d V c k O) O
      (etaleQuotientPreimageOpen_image f hL d V c k O hO) t := by
  apply (fullSectionFunctionEquiv a (quotientPreimageOpen f hL d V c k O)).injective
  apply Subtype.ext
  exact (quotientSheafMap_fullSection f hL d V c k O t).trans
    (etaleRestrictedSheafImageEquivOn_val f hL d V c k
      (quotientPreimageOpen f hL d V c k O) O (etaleQuotientPreimageOpen_image f hL d V c k O hO)
      t (quotientPreimageSource_le f hL d V c k O)).symm

/-- Every sheaf component over the original image is an isomorphism. -/
theorem etaleQuotientSheafMap_isIso (O : TopologicalSpace.Opens (Orbit e))
    (hO : O ≤ orbitImageOpen e (variableChartRelationSnd f hL d V c).left.isOpenMap
      (etaleSourceImage k.left)) : IsIso ((m).c.app (op O)) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have h : ⇑((m).c.app (op O)) = etaleRestrictedSheafImageEquivOn f hL d V c k
      (quotientPreimageOpen f hL d V c k O) O
        (etaleQuotientPreimageOpen_image f hL d V c k O hO) :=
    funext (etaleQuotientSheafMap_eq_equiv f hL d V c k O hO)
  rw [h]
  exact (etaleRestrictedSheafImageEquivOn f hL d V c k _ _ _).bijective

/-- The existing original invariant quotient comparison is an LRS open immersion. -/
theorem etaleRestrictedInvariantQuotientMap_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (m) where
  base_open := by
    change IsOpenEmbedding (m).base
    have he : ⇑(m).base = restrictedOrbitMap f hL d V c k :=
      funext (restrictedInvariantQuotientMap_apply f hL d V c k)
    rw [he]
    exact etaleRestrictedOrbitMap_isOpenEmbedding f hL d V c k
  c_iso B := by
    apply etaleQuotientSheafMap_isIso f hL d V c k
    rintro z ⟨w, _, rfl⟩
    obtain ⟨x, rfl⟩ := projection_surjective a w
    refine ⟨k.left x, ⟨x, rfl⟩, ?_⟩
    exact ((restrictedInvariantQuotientMap_apply f hL d V c k (projection a x)).trans
      (restrictedOrbitMap_projection f hL d V c k x)).symm

end FLT.Mazur.HilbertChart.AffineRestriction
