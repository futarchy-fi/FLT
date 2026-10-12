/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertRestrictedQuotient
public import FLT.Mazur.RelativeRelationInvariantSections

/-!
# The actual restricted quotient sheaf map in original source coordinates

The existing locally ringed quotient morphism pulls sections back through the
original source immersion. Domain transports are retained as actual `appLE`
maps, so the formula compares the constructed geometric morphism itself.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.RelativeRelationOrbit

/-- Pullback to an open subscheme uses the original section map in global coordinates. -/
theorem openComposite_appLE {X Y : Scheme} (k : X ⟶ Y) (W : X.Opens) (D : Y.Opens)
    (h : W ≤ k ⁻¹ᵁ D) (h' : ⊤ ≤ (W.ι ≫ k) ⁻¹ᵁ D) (v : Γ(Y, D)) :
    W.topIso.inv (k.appLE D W h v) = (W.ι ≫ k).appLE D ⊤ h' v := by
  have ht : W.topIso.inv = W.ι.appLE W ⊤ W.ι_preimage_self.ge := by
    simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE]
    congr 1
  rw [ht]
  exact congrArg (fun g ↦ g v)
    (Scheme.Hom.appLE_comp_appLE W.ι k D W ⊤ h W.ι_preimage_self.ge)

end FLT.Mazur.RelativeRelationOrbit

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

/-- Forgetting local rings preserves the original source square. -/
theorem restrictedInvariantQuotientMap_ringed_projection :
    toRingedSpace a ≫ (restrictedInvariantQuotientMap f hL d V c k).toShHom =
      k.left.toShHom ≫ toRingedSpace e := by
  have h := congrArg (fun g ↦ g.toShHom)
    (restrictedInvariantQuotientMap_projection f hL d V c k)
  simpa only [LocallyRingedSpace.comp_toShHom,
    invariantLocallyRingedProjection_toShHom] using h

/-- The actual quotient-map inverse image lies over the original source inverse image. -/
theorem restrictedQuotientSourceOpen_le
    (O : TopologicalSpace.Opens (Orbit e)) :
    (pullOpen a ((TopologicalSpace.Opens.map
      (restrictedInvariantQuotientMap f hL d V c k).base).obj O)).val ≤
        k.left ⁻¹ᵁ (pullOpen e O).val := by
  intro x hx
  change (restrictedInvariantQuotientMap f hL d V c k).base (projection a x) ∈ O at hx
  rw [restrictedInvariantQuotientMap_apply, restrictedOrbitMap_projection] at hx
  exact hx

/-- The existing quotient sheaf comparison is exactly original source pullback. -/
theorem restrictedInvariantQuotientMap_source_app
    (O : TopologicalSpace.Opens (Orbit e)) :
    (restrictedInvariantQuotientMap f hL d V c k).c.app (op O) ≫
      (invariantInclusion a).hom.app (op ((TopologicalSpace.Opens.map
        (restrictedInvariantQuotientMap f hL d V c k).base).obj O)) =
    (invariantInclusion e).hom.app (op O) ≫ k.left.appLE _ _
      (restrictedQuotientSourceOpen_le f hL d V c k O) := by
  have h := PresheafedSpace.congr_app
    (congrArg (fun g ↦ g.hom)
      (restrictedInvariantQuotientMap_ringed_projection f hL d V c k)) (op O)
  change (restrictedInvariantQuotientMap f hL d V c k).c.app (op O) ≫
    (invariantInclusion a).hom.app _ = (invariantInclusion e).hom.app (op O) ≫
      k.left.app _ ≫ A.left.presheaf.map (eqToHom _) at h
  refine h.trans ?_
  dsimp only [Scheme.Hom.appLE]
  congr 2

/-- The formula evaluates on every original invariant section. -/
theorem restrictedInvariantQuotientMap_source_apply
    (O : TopologicalSpace.Opens (Orbit e)) (t : (invariantSheaf e).obj.obj (op O)) :
    (invariantInclusion a).hom.app (op ((TopologicalSpace.Opens.map
      (restrictedInvariantQuotientMap f hL d V c k).base).obj O))
        ((restrictedInvariantQuotientMap f hL d V c k).c.app (op O) t) =
      k.left.appLE _ _ (restrictedQuotientSourceOpen_le f hL d V c k O)
        ((invariantInclusion e).hom.app (op O) t) :=
  congrArg (fun g ↦ g t) (restrictedInvariantQuotientMap_source_app f hL d V c k O)

end FLT.Mazur.HilbertChart.AffineRestriction
