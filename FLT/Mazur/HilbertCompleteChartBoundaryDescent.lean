/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertCompleteChartBoundaryTests
public import FLT.Mazur.SchemeEtaleBoundaryTests

/-!
# Lifting original boundary sections on complete chart orbit images

The descended invariant section has the prescribed boundary value on the ENTIRE
original orbit-image boundary. The comparison is detected by an actual etale
cover of the original source, so it retains all regular functions and nilpotents.
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

attribute [local irreducible] RelativeRelationOrbit.openSourceMap
  InvariantOpenRelationDiagram.sourceMap InvariantOpenRelationDiagram.orbitFunctions

/-- Exact complete-chart coefficients imply equality on the entire original boundary. -/
theorem completeChart_original_boundary_eq
    (hc : ∀ y : normalizedFullRelationFrames f hL d V c k n o,
      y ∈ U → y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o)
    (v : invariantCoordinates (restrictedAction
      (normalizedFullRelationAction f hL d V c k n o) U hU))
    (b : (invariantSheaf eo).obj.obj (op O))
    (t : (invariantSheaf ec).obj.obj (op Oc))
    (hb : (etaleSourceFunctionEquiv eo (q).isOpenMap j b).val = v.val)
    (hv : normalizedBoundaryChartMap f hL d V c k n o U hU v =
      normalizedOrbitBoundaryCoefficient f hL d V c k n o O U hU
        (completeChart_le_orbitSource f hL d V c k n o U) t) :
    (m).c.app (op O) b = t := by
  let _ := completeChart_orbitSource_surjective f hL d V c k n o U hU hc
  have hs : (etaleOrbitImageMap eo (q).isOpenMap j).appTop
      (orbitFunctions eo O b).val = v.val :=
    (etaleOrbitImageMap_appTop eo (q).isOpenMap j b).trans hb
  have he : (g).appTop (orbitFunctions eo O b).val = (orbitFunctions ec Oc t).val := by
    apply SchemeEffectiveEpiSections.boundary_eq_of_etale_tests
      (etaleOrbitImageMap eo (q).isOpenMap j)
    intro T a w hw
    exact (congrArg (fun x ↦ a.appTop x) hs).trans
      (completeChart_boundary_test f hL d V c k n o U hU v t hv a w hw)
  apply (orbitFunctions ec Oc).injective
  apply Subtype.ext
  have hn := congrArg Subtype.val (openFunctionMap_natural eo ec i z hp hq O b)
  exact hn.symm.trans he

include hU in
/-- Every boundary section lifts on the whole actual orbit image of a complete affine chart. -/
theorem completeChart_original_boundary_surjective
    (hc : ∀ y : normalizedFullRelationFrames f hL d V c k n o,
      y ∈ U → y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o)
    (ha : IsAffineOpen U) : Function.Surjective ((m).c.app (op O)) := by
  intro t
  obtain ⟨b, v, hb, hv⟩ := completeChart_original_boundary_section
    f hL d V c k n o U hU hc ha O (completeChart_le_orbitSource f hL d V c k n o U) t
  exact ⟨b, completeChart_original_boundary_eq f hL d V c k n o U hU hc v b t hb hv⟩

end FLT.Mazur.HilbertChart.AffineRestriction
