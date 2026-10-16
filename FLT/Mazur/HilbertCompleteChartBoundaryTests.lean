/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertCompleteChartOriginalSections
public import FLT.Mazur.EquivalenceRelationCompleteChartImage
public import FLT.Mazur.RelativeRelationEtaleOrbitImageMap
public import FLT.Mazur.EquivalenceRelationBoundaryChartTests

/-!
# Complete chart covers and exact original boundary tests

A complete stable chart covers the source of its actual original orbit image.
Its boundary coefficient equation holds on every test over the original boundary.
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
local notation "E" => (pullOpen eo O).val
local notation "Oc" => (TopologicalSpace.Opens.map (m).base).obj O
local notation "Ec" => (pullOpen ec Oc).val
local notation "i" => originalBoundarySourceMap f hL d V c k
local notation "z" => originalClosedArrow f hL d V c k
local notation "hp" => originalClosedArrow_fst f hL d V c k
local notation "hq" => originalClosedArrow_snd f hL d V c k
local notation "g" => (openSourceMap eo ec i z hp hq O).left
attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence InvariantBoundary.boundary

/-- The whole normalized chart lies over its actual original orbit image. -/
theorem completeChart_le_orbitSource :
    U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ E := by
  intro x hx
  exact le_saturateOpen eo (q).isOpenMap (etaleSourceImage j) ⟨⟨x, hx⟩, rfl⟩

include hU in
/-- Completeness makes the actual chart a surjective etale cover of the orbit source. -/
theorem completeChart_orbitSource_surjective
    (hc : ∀ y : normalizedFullRelationFrames f hL d V c k n o,
      y ∈ U → y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) :
    Surjective (etaleOrbitImageMap eo (q).isOpenMap j) := by
  apply etaleOrbitImageMap_surjective
  exact completeChartImage_invariant e (Fin n) o U hU hc

/-- Exact chart boundary data hold on every original-boundary scheme test. -/
theorem completeChart_boundary_test
    (v : invariantCoordinates (restrictedAction
      (normalizedFullRelationAction f hL d V c k n o) U hU))
    (t : (invariantSheaf ec).obj.obj (op Oc))
    (hv : normalizedBoundaryChartMap f hL d V c k n o U hU v =
      normalizedOrbitBoundaryCoefficient f hL d V c k n o O U hU
        (completeChart_le_orbitSource f hL d V c k n o U) t)
    {T : Scheme} (a : T ⟶ U.toScheme) (b : T ⟶ (Ec).toScheme)
    (hab : a ≫ etaleOrbitImageMap eo (q).isOpenMap j = b ≫ g) :
    a.appTop v.val = b.appTop (orbitFunctions ec Oc t).val := by
  have hg : (g) ≫ (E).ι = (Ec).ι ≫ (i).left := Scheme.Hom.resLE_comp_ι _ _
  have hw : a ≫ U.ι ≫ first p q (Fin n) o = b ≫ (Ec).ι ≫ (i).left := by
    change a ≫ j = b ≫ (Ec).ι ≫ (i).left
    calc
      a ≫ j = (a ≫ etaleOrbitImageMap eo (q).isOpenMap j) ≫ (E).ι := by
        rw [Category.assoc, etaleOrbitImageMap_ι]
      _ = (b ≫ g) ≫ (E).ι := congrArg (fun φ ↦ φ ≫ (E).ι) hab
      _ = _ := by rw [Category.assoc, hg]
  apply InvariantBoundary.boundary_coefficient_test o (i).left U Ec a b hw
    (normalizedOrbitBoundary_domain_le f hL d V c k n o O U
      (completeChart_le_orbitSource f hL d V c k n o U)) v.val (orbitFunctions ec Oc t).val
  simpa only [normalizedBoundaryChartMap, invariantMap_val,
    normalizedOrbitBoundaryCoefficient_val, normalizedOriginalBoundaryInclusion,
    normalizedOriginalBoundaryEndpoint] using congrArg Subtype.val hv

end FLT.Mazur.HilbertChart.AffineRestriction
