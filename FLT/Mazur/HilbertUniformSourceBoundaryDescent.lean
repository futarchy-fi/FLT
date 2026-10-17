/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertUniformSourceOriginalSections
public import FLT.Mazur.EquivalenceRelationUniformSourceOpen
public import FLT.Mazur.HilbertNormalizedChartBoundaryTests
public import FLT.Mazur.ClosedRelationGeneratorBoundaryEquality
public import FLT.Mazur.RelativeRelationOrbitFunctionRestriction

/-!
# Exact original boundary descent on uniform source orbit images

A boundary lift on the affine normalized chart descends to the constructed
uniform source orbit image. Its restriction equals the original boundary
section on the entire boundary orbit domain, detected by the actual boundary
generator. No source coverage or fixed-domain multiplier extension is assumed.
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
attribute [local irreducible] RelativeRelationOrbit.orbitSetoid
  uniformSourceOpen orbitImageOpen etaleSourceImage
  EquivalenceRelationNormalizedFrames.action
set_option quotPrecheck false
local notation "B" => uniformSourceOpen e (Fin n) o U hU
local notation "j" => (B).ι ≫ U.ι ≫ normalizedFullRelationFirst f hL d V c k n o
local notation "r" => SchemeRelationRestriction.fst p q j
local notation "s" => SchemeRelationRestriction.snd p q j
local notation "O" => orbitImageOpen eo (q).isOpenMap (etaleSourceImage j)

local notation "Oc" => (TopologicalSpace.Opens.map (m).base).obj O
local notation "E" => (pullOpen eo O).val
local notation "Ec" => (pullOpen ec Oc).val
local notation "i" => originalBoundarySourceMap f hL d V c k
local notation "z" => originalClosedArrow f hL d V c k
local notation "hp" => originalClosedArrow_fst f hL d V c k
local notation "hq" => originalClosedArrow_snd f hL d V c k
local notation "g" => (openSourceMap eo ec i z hp hq O).left
attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence InvariantBoundary.boundary
  RelativeRelationOrbit.openSourceMap InvariantOpenRelationDiagram.sourceMap
  InvariantOpenRelationDiagram.orbitFunctions
  normalizedOrbitBoundaryCoefficient normalizedBoundaryChartMap
local notation "Wc" w:max => (TopologicalSpace.Opens.map (m).base).obj w
local notation "hOcWc" w:max hw:max => show Oc ≤ Wc w from fun _ hx ↦
  uniformSource_orbitImage_le f hL d V c k n o U hU w hw hx

/-- Uniform-source tests retain the whole original boundary value after restriction. -/
theorem uniformSource_original_boundary_test
    (W : TopologicalSpace.Opens (Orbit eo))
    (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val)
    (v : invariantCoordinates (restrictedAction
      (normalizedFullRelationAction f hL d V c k n o) U hU))
    (t : (invariantSheaf ec).obj.obj (op (Wc W)))
    (hv : normalizedBoundaryChartMap f hL d V c k n o U hU v =
      normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t)
    {T : Scheme} (a : T ⟶ (B).toScheme) (w : T ⟶ (Ec).toScheme)
    (hw : a ≫ j = w ≫ (Ec).ι ≫ (i).left) :
    a.appTop ((B).ι.appTop v.val) = w.appTop (orbitFunctions ec Oc
      ((invariantSheaf ec).obj.map (homOfLE (hOcWc W hUW)).op t)).val := by
  let l := Scheme.homOfLE _
    (show Ec ≤ (pullOpen ec (Wc W)).val from fun _ hx ↦ (hOcWc W hUW) hx)
  have ht := normalizedChart_original_boundary_test f hL d V c k n o U hU W hUW
    v t hv (a ≫ (B).ι) (w ≫ l) (by
      simpa only [l, Category.assoc, Scheme.homOfLE_ι_assoc] using hw)
  exact ht.trans (orbitFunctions_restriction_test ec (hOcWc W hUW) t w)

/-- Chart equality determines the entire original boundary restriction of a descended section. -/
theorem uniformSource_original_boundary_eq
    (W : TopologicalSpace.Opens (Orbit eo))
    (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val)
    (v : invariantCoordinates (restrictedAction
      (normalizedFullRelationAction f hL d V c k n o) U hU))
    (b : (invariantSheaf eo).obj.obj (op O))
    (t : (invariantSheaf ec).obj.obj (op (Wc W)))
    (hb : (etaleSourceFunctionEquiv eo (q).isOpenMap j b).val = (B).ι.appTop v.val)
    (hv : normalizedBoundaryChartMap f hL d V c k n o U hU v =
      normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t) :
    (m).c.app (op O) b = (invariantSheaf ec).obj.map (homOfLE (hOcWc W hUW)).op t := by
  exact closedBoundary_eq_of_etale_tests eo ec i z hp hq
    (originalClosedFst_isPullback f hL d V c k) (q).isOpenMap
    (originalClosedSnd f hL d V c k).left.isOpenMap j b _ (fun T a w hw ↦
      (congrArg a.appTop hb).trans
        (uniformSource_original_boundary_test f hL d V c k n o U hU W hUW v t hv a w hw))

/-- Every original boundary section lifts exactly on the constructed uniform orbit neighborhood. -/
theorem uniformSource_original_boundary_lift
    (W : TopologicalSpace.Opens (Orbit eo))
    (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val)
    (ha : IsAffineOpen U)
    (t : (invariantSheaf ec).obj.obj (op (Wc W))) :
    ∃ b : (invariantSheaf eo).obj.obj (op O),
      (m).c.app (op O) b = (invariantSheaf ec).obj.map (homOfLE (hOcWc W hUW)).op t := by
  obtain ⟨b, v, hb, hv⟩ := uniformSource_original_boundary_section
    f hL d V c k n o U hU ha W hUW t
  exact ⟨b, uniformSource_original_boundary_eq f hL d V c k n o U hU W hUW v b t hb hv⟩

end FLT.Mazur.HilbertChart.AffineRestriction
