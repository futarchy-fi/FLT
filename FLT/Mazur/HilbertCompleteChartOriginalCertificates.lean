/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertCompleteChartBoundaryDescent
public import FLT.Mazur.HilbertBoundaryCertifiedAlgebra

/-!
# Original finite certificates on complete chart orbit images

Every original boundary section on a complete affine chart's orbit image has
an actual finite lifting-multiplier identity in the unchanged closed source.
This statement concerns those orbit images; it does not cover arbitrary boundary points.
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
variable (n : ℕ) (o : Fin n)
  (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ σ : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)
attribute [local irreducible] relation AffineRestriction.fst AffineRestriction.snd equivalence
  EquivalenceRelationNormalizedFrames.source relativeFppfSheaf AmpleLineBundle
set_option quotPrecheck false
local notation "j" => U.ι ≫ normalizedFullRelationFirst f hL d V c k n o
local notation "O" => orbitImageOpen eo (q).isOpenMap (etaleSourceImage j)
local notation "Oc" => (TopologicalSpace.Opens.map (m).base).obj O

include hU in
/-- Complete affine chart orbit images have finite certificates on the original closed source. -/
theorem completeChart_original_boundary_certificate
    (hc : ∀ y : normalizedFullRelationFrames f hL d V c k n o,
      y ∈ U → y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o)
    (ha : IsAffineOpen U) (t : (invariantSheaf ec).obj.obj (op Oc)) :
    ∃ a : originalBoundaryLiftIdeal f hL d V c k O t →₀
        (sourceSheaf ec).obj.obj (op Oc),
      a.sum (fun v b ↦ b * (invariantInclusion ec).hom.app (op Oc)
        ((m).c.app (op O) v.val)) = 1 := by
  apply (mem_originalBoundaryCertifiedSections_iff f hL d V c k O t).mp
  obtain ⟨b, hb⟩ := completeChart_original_boundary_surjective f hL d V c k n o U hU hc ha t
  rw [← hb]
  exact image_mem_sourceCertifiedSections _ _ b

include hU in
/-- On an affine original source image, every boundary point lies in its actual lifting locus. -/
theorem completeChart_original_boundary_cover
    (hc : ∀ y : normalizedFullRelationFrames f hL d V c k n o,
      y ∈ U → y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o)
    (ha : IsAffineOpen U) (hO : IsAffineOpen (pullOpen eo O).val)
    (t : (invariantSheaf ec).obj.obj (op Oc)) :
    (TopologicalSpace.Opens.map (m).base).obj
      (originalBoundaryLiftOpen f hL d V c k O t) = Oc :=
  (originalBoundaryLift_boundary_cover_iff_certificate f hL d V c k O t hO).mpr
    (completeChart_original_boundary_certificate f hL d V c k n o U hU hc ha t)

end FLT.Mazur.HilbertChart.AffineRestriction
