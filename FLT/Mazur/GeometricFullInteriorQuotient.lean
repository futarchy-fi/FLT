/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFullInteriorQuotientChart

/-!
# Whole geometric quotient morphisms in constructed affine open charts

The constructed invariant norm chart contains the whole geometric quotient
map. Lift in locally ringed spaces and use full faithfulness to obtain an
actual scheme morphism, with the original quotient morphism unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Module
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R K : Type} [CommRing R] [Algebra.FiniteType ℤ R] [Field K]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom] [Surjective V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
/-- The norm basis uses the original translation structural algebra. -/
local instance geometricQuotientTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom
variable {ι : Type} [Finite ι] (e : Basis ι R Γ(V.left, ⊤))
  {t : Spec (.of K) ⟶ Spec (.of R)} (b : Over.mk t ⟶ A)
local notation "η" => (default : Spec (CommRingCat.of K))
local notation "E" => variableChartEquivalenceRelation f hL d V c

include e in
/-- The whole original geometric quotient map factors through a constructed affine scheme open. -/
theorem exists_geometric_fullInterior_quotient
    (hx : b.left η ∈ fullEnvelopeInterior f hL d V c k) :
    ∃ (Q : Scheme) (j : Q.toLocallyRingedSpace ⟶ invariantLocallyRingedSpace E)
      (z : Spec (.of K) ⟶ Q), IsAffine Q ∧ LocallyRingedSpace.IsOpenImmersion j ∧
      z.toLRSHom ≫ j = (b ≫ k).left.toLRSHom ≫ invariantLocallyRingedProjection E := by
  obtain ⟨Q, j, hQ, hj, hp⟩ :=
    exists_fullInterior_affine_quotient_chart f hL d V c k e (b.left η) hx
  let _ := hj
  let g : (Spec (.of K)).toLocallyRingedSpace ⟶ invariantLocallyRingedSpace E :=
    (b ≫ k).left.toLRSHom ≫ invariantLocallyRingedProjection E
  have hr : Set.range g.base ⊆ Set.range j.base := by
    rintro _ ⟨x, rfl⟩
    have hxη : x = η := Subsingleton.elim (α := Spec (.of K)) _ _
    subst x
    dsimp only [g]
    rw [LocallyRingedSpace.comp_base, invariantLocallyRingedProjection_base]
    exact hp
  let z₀ := LocallyRingedSpace.IsOpenImmersion.lift j g hr
  obtain ⟨z, hz⟩ := Scheme.fullyFaithfulForgetToLocallyRingedSpace.map_surjective
    (X := Spec (.of K)) (Y := Q) z₀
  refine ⟨Q, j, z, hQ, hj, ?_⟩
  change Scheme.forgetToLocallyRingedSpace.map z ≫ j = g
  rw [hz]
  exact LocallyRingedSpace.IsOpenImmersion.lift_fac j g hr

end FLT.Mazur.HilbertChart.AffineRestriction
