/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertRestrictedOrbits
public import FLT.Mazur.RelativeRelationInvariantLocallyRinged

/-!
# The original invariant locally ringed quotient on a restricted source

Restriction induces an actual locally ringed morphism of invariant quotients.
Its underlying map is the exact orbit-open embedding constructed from the full
relation. The remaining sheaf-isomorphism and scheme-effectivity requirements
are not replaced by this topological identification.
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

/-- The original locally ringed projection identifies both full restricted endpoints. -/
theorem restrictedInvariant_condition :
    (fst f hL d V c k).left.toLRSHom ≫ k.left.toLRSHom ≫
        invariantLocallyRingedProjection e =
      (snd f hL d V c k).left.toLRSHom ≫ k.left.toLRSHom ≫
        invariantLocallyRingedProjection e := by
  have h₁ := congrArg (fun g ↦ g.left.toLRSHom) (toFullRelation_fst f hL d V c k)
  have h₂ := congrArg (fun g ↦ g.left.toLRSHom) (toFullRelation_snd f hL d V c k)
  simp only [Over.comp_left, Scheme.Hom.comp_toLRSHom] at h₁ h₂
  change _ ≫ _ ≫ (locallyRingedProjection ≫ (invariantLocallyRingedIso e).hom) =
    _ ≫ _ ≫ (locallyRingedProjection ≫ (invariantLocallyRingedIso e).hom)
  rw [← Category.assoc, ← h₁, ← Category.assoc _ k.left.toLRSHom, ← h₂]
  simp only [Category.assoc, locallyRingedProjection, coequalizer.condition_assoc]

/-- The full restricted invariant quotient maps to the original invariant quotient. -/
def restrictedInvariantQuotientMap :
    invariantLocallyRingedSpace a ⟶ invariantLocallyRingedSpace e :=
  (invariantLocallyRingedIso a).inv ≫ coequalizer.desc
    (k.left.toLRSHom ≫ invariantLocallyRingedProjection e)
    (restrictedInvariant_condition f hL d V c k)

/-- The comparison preserves the original source map, including its regular functions. -/
@[reassoc]
theorem restrictedInvariantQuotientMap_projection :
    invariantLocallyRingedProjection a ≫ restrictedInvariantQuotientMap f hL d V c k =
      k.left.toLRSHom ≫ invariantLocallyRingedProjection e := by
  dsimp only [restrictedInvariantQuotientMap, invariantLocallyRingedProjection]
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact coequalizer.π_desc _ _

/-- Its point map is precisely the full-relation orbit comparison. -/
theorem restrictedInvariantQuotientMap_apply (z : Orbit a) :
    (restrictedInvariantQuotientMap f hL d V c k).base z =
      restrictedOrbitMap f hL d V c k z := by
  obtain ⟨x, rfl⟩ := projection_surjective a z
  have h := congrArg (fun g ↦ g.base)
    (restrictedInvariantQuotientMap_projection f hL d V c k)
  rw [LocallyRingedSpace.comp_base, LocallyRingedSpace.comp_base,
    invariantLocallyRingedProjection_base, invariantLocallyRingedProjection_base] at h
  exact congrArg (fun g ↦ g x) h

/-- The underlying map embeds openly, without assuming the restricted quotient is a scheme. -/
theorem restrictedInvariantQuotientMap_base_isOpenEmbedding
    [Etale V.hom] [IsOpenImmersion k.left] :
    IsOpenEmbedding (restrictedInvariantQuotientMap f hL d V c k).base := by
  have h : ⇑(restrictedInvariantQuotientMap f hL d V c k).base =
      restrictedOrbitMap f hL d V c k := funext (restrictedInvariantQuotientMap_apply f hL d V c k)
  rw [h]
  exact restrictedOrbitMap_isOpenEmbedding f hL d V c k

end FLT.Mazur.HilbertChart.AffineRestriction
