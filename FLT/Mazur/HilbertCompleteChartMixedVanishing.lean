/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertCompleteChartBoundaryDescent
public import FLT.Mazur.HilbertOrbitRelativeMixedError

/-!
# Actual local error vanishing on complete chart orbit images

A complete affine normalized chart supplies genuine original boundary lifts.
Consequently the actual local scalar error vanishes at every source prime
over this orbit image. No coverage beyond these images
is asserted.
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

open OrbitBoundaryAtlas.FiniteAtlas TensorProduct
attribute [local irreducible] invariantSheaf sourceSheaf invariantInclusion
  originalClosedEquivalence originalClosedInvariantMap originalBoundarySource
  originalBoundarySourceMap originalClosedRelation originalClosedFst originalClosedSnd
  originalClosedArrow
local notation "Ω" => (invariantSheaf eo).obj.obj (op O)
local notation "D" => (invariantSheaf ec).obj.obj (op Oc)
local notation "T" => (sourceSheaf ec).obj.obj (op Oc)
local notation "ρ" => originalClosedSectionPullback f hL d V c k O
local notation "κ" => ((invariantInclusion ec).hom.app (op Oc)).hom.comp ρ
variable (hc : ∀ y : normalizedFullRelationFrames f hL d V c k n o,
    y ∈ U → y ∈ completePointLocus
      («p» := Over.Hom.left (AffineRestriction.fst f hL d V c k))
      («q» := Over.Hom.left (AffineRestriction.snd f hL d V c k)) (Fin n) o)
  (ha : IsAffineOpen U)
  (hO : IsAffineOpen (pullOpen (equivalence f hL d V c k)
    (orbitImageOpen (equivalence f hL d V c k)
      (Over.Hom.left (AffineRestriction.snd f hL d V c k)).isOpenMap
      (etaleSourceImage (U.ι ≫ normalizedFullRelationFirst f hL d V c k n o)))).val)
  (P : Ideal ((sourceSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
    (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj
      (orbitImageOpen (equivalence f hL d V c k)
        (Over.Hom.left (AffineRestriction.snd f hL d V c k)).isOpenMap
        (etaleSourceImage (U.ι ≫ normalizedFullRelationFirst f hL d V c k n o)))))))
  [P.IsPrime]
  (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
    (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj
      (orbitImageOpen (equivalence f hL d V c k)
        (Over.Hom.left (AffineRestriction.snd f hL d V c k)).isOpenMap
        (etaleSourceImage (U.ι ≫ normalizedFullRelationFirst f hL d V c k n o))))))
local notation "S" => Localization.AtPrime (P.comap κ)
attribute [local irreducible] originalBoundaryExtendedCokernelAddCommGroup
  originalBoundaryExtendedCokernelModule originalBoundaryLiftErrorClass
  originalRelativeMixedError
attribute [local instance] originalBoundarySectionAlgebra

include hU hc ha in
/-- Every original source prime over a complete chart image has zero actual local scalar error. -/
theorem completeChart_original_local_error_eq_zero :
    originalBoundaryLiftErrorClass f hL d V c k O hO S t = 0 := by
  obtain ⟨b, hb⟩ := completeChart_original_boundary_surjective f hL d V c k n o U hU hc ha t
  apply (originalBoundarySourceError_eq_zero_iff f hL d V c k O hO P t).mpr
  refine ⟨1, ?_, b, ?_⟩
  · simpa only [map_one] using Ideal.one_notMem P
  · have he : ρ = ((m).c.app (op O)).hom := by
      unfold originalClosedSectionPullback invariantSectionPullback originalClosedInvariantMap
      rfl
    rw [he, one_smul]
    exact hb

end FLT.Mazur.HilbertChart.AffineRestriction
