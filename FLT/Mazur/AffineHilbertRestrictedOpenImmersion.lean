/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertRestrictedSheafEquiv
public import FLT.Mazur.AffineHilbertRestrictedSheafPullback

/-!
# The actual restricted Hilbert quotient is an open locally ringed subspace

The original quotient morphism has invertible sheaf comparisons on its image.
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
variable [Etale V.hom] [IsOpenImmersion k.left]

/-- The actual quotient-map inverse image of an original quotient open. -/
def quotientPreimageOpen (O : TopologicalSpace.Opens (Orbit e)) :
    TopologicalSpace.Opens (Orbit a) := (TopologicalSpace.Opens.map (m).base).obj O

/-- An open contained in the quotient image is exactly the image of its actual inverse image. -/
theorem quotientPreimageOpen_image (O : TopologicalSpace.Opens (Orbit e))
    (hO : O ≤ orbitImageOpen e (variableChartRelationSnd f hL d V c).left.isOpenMap
      k.left.opensRange) :
    restrictedSectionImageOpen f hL d V c k (quotientPreimageOpen f hL d V c k O) = O := by
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

omit [Etale V.hom] [IsOpenImmersion k.left] in
/-- The composite source over an actual inverse image maps into the original source open. -/
theorem quotientPreimageSource_le (O : TopologicalSpace.Opens (Orbit e)) :
    ⊤ ≤ (restrictedSectionSource f hL d V c k
      (quotientPreimageOpen f hL d V c k O)) ⁻¹ᵁ (pullOpen e O).val := by
  intro x _
  apply restrictedQuotientSourceOpen_le f hL d V c k O
  exact (mem_fullSectionSourceOpen a (quotientPreimageOpen f hL d V c k O) x.val).mp
    x.property

omit [Etale V.hom] [IsOpenImmersion k.left] in
/-- The actual sheaf map computes the same full source function as effective descent. -/
theorem quotientSheafMap_fullSection (O : TopologicalSpace.Opens (Orbit e))
    (t : (invariantSheaf e).obj.obj (op O)) :
    (fullSectionFunctionEquiv a (quotientPreimageOpen f hL d V c k O)
      ((m).c.app (op O) t)).val =
      (restrictedSectionSource f hL d V c k (quotientPreimageOpen f hL d V c k O)).appLE
        _ ⊤ (quotientPreimageSource_le f hL d V c k O)
        ((invariantInclusion e).hom.app (op O) t) := by
  rw [fullSectionFunctionEquiv_val]
  refine (congrArg (fun v ↦
    (fullSectionSourceOpen a (quotientPreimageOpen f hL d V c k O)).topIso.inv
      (A.left.presheaf.map (eqToHom (congrArg op
        (fullSectionSourceOpen_eq a (quotientPreimageOpen f hL d V c k O)).symm)) v))
    (restrictedInvariantQuotientMap_source_apply f hL d V c k O t)).trans ?_
  change (fullSectionSourceOpen a (quotientPreimageOpen f hL d V c k O)).topIso.inv
    ((k.left.appLE _ _ _ ≫ A.left.presheaf.map (eqToHom _)) _) = _
  rw [Scheme.Hom.appLE_map]
  exact openComposite_appLE k.left _ _ _ _ _

/-- The actual quotient morphism's sheaf component is the constructed descent equivalence. -/
theorem quotientSheafMap_eq_equiv (O : TopologicalSpace.Opens (Orbit e))
    (hO : O ≤ orbitImageOpen e (variableChartRelationSnd f hL d V c).left.isOpenMap
      k.left.opensRange) (t : (invariantSheaf e).obj.obj (op O)) :
    (m).c.app (op O) t = restrictedSheafImageEquivOn f hL d V c k
      (quotientPreimageOpen f hL d V c k O) O (quotientPreimageOpen_image f hL d V c k O hO) t := by
  apply (fullSectionFunctionEquiv a (quotientPreimageOpen f hL d V c k O)).injective
  apply Subtype.ext
  exact (quotientSheafMap_fullSection f hL d V c k O t).trans
    (restrictedSheafImageEquivOn_val f hL d V c k
      (quotientPreimageOpen f hL d V c k O) O (quotientPreimageOpen_image f hL d V c k O hO)
      t (quotientPreimageSource_le f hL d V c k O)).symm

/-- Every sheaf component over the original image is an isomorphism. -/
theorem quotientSheafMap_isIso (O : TopologicalSpace.Opens (Orbit e))
    (hO : O ≤ orbitImageOpen e (variableChartRelationSnd f hL d V c).left.isOpenMap
      k.left.opensRange) : IsIso ((m).c.app (op O)) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have h : ⇑((m).c.app (op O)) = restrictedSheafImageEquivOn f hL d V c k
      (quotientPreimageOpen f hL d V c k O) O
        (quotientPreimageOpen_image f hL d V c k O hO) :=
    funext (quotientSheafMap_eq_equiv f hL d V c k O hO)
  rw [h]
  exact (restrictedSheafImageEquivOn f hL d V c k _ _ _).bijective

/-- The existing original invariant quotient comparison is an LRS open immersion. -/
theorem restrictedInvariantQuotientMap_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (m) where
  base_open := restrictedInvariantQuotientMap_base_isOpenEmbedding f hL d V c k
  c_iso B := by
    apply quotientSheafMap_isIso f hL d V c k
    rintro z ⟨w, _, rfl⟩
    obtain ⟨x, rfl⟩ := projection_surjective a w
    refine ⟨k.left x, ⟨x, rfl⟩, ?_⟩
    exact ((restrictedInvariantQuotientMap_apply f hL d V c k (projection a x)).trans
      (restrictedOrbitMap_projection f hL d V c k x)).symm

end FLT.Mazur.HilbertChart.AffineRestriction
