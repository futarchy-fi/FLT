/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormalizedOrbitBoundaryCoefficients
public import FLT.Mazur.EquivalenceRelationJointChartLiftDifference

/-!
# Actual original Hilbert orbit-section lifts on independent common-frame overlaps

Any pair of the constructed invariant chart lifts has difference in the exact
boundary ideal on every common-frame overlap. This uses the original section
on its full orbit domain, with no completeness or global extension assumption.
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
local notation "i" => Over.Hom.left (originalBoundarySourceMap f hL d V c k)
local notation "r" => Over.Hom.left (originalClosedFst f hL d V c k)
local notation "s" => Over.Hom.left (originalClosedSnd f hL d V c k)
local notation "z" => Over.Hom.left (originalClosedArrow f hL d V c k)
local notation "hr" => originalClosedFst_isPullback f hL d V c k
local notation "hs" => congrArg Over.Hom.left (originalClosedArrow_snd f hL d V c k)
local notation "m" => originalClosedInvariantMap f hL d V c k
attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation AffineRestriction.fst AffineRestriction.snd equivalence
attribute [local irreducible] EquivalenceRelationNormalizedFrames.source
  EquivalenceRelationNormalizedFrames.InvariantBoundary.boundary
variable (n n' : ℕ) (o : Fin n) (o' : Fin n')
  (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
  (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (U' : (normalizedFullRelationFrames f hL d V c k n' o').Opens)
  (hU : ∀ σ : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)
  (hU' : ∀ σ : Equiv.Perm (Fin n'),
    (normalizedFullRelationAction f hL d V c k n' o' σ).hom ⁻¹ᵁ U' = U')
  (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)
  (hU'W : U' ≤ normalizedFullRelationFirst f hL d V c k n' o' ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)
set_option quotPrecheck false
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "Uc" => (pullOpen ec Wc).val
variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

omit [IsAffine V.left] in
/-- The exact original orbit section is equalized on its full open closed relation. -/
theorem jointOrbitBoundaryFunction_equalized :
    ((r) ∣_ Uc).appTop (orbitFunctions ec Wc t).val =
      ((s).resLE Uc _ (pullOpen_preimage_eq ec Wc).le).appTop
        (orbitFunctions ec Wc t).val := by
  have h := (orbitFunctions ec Wc t).property
  change ((r).resLE Uc _ le_rfl).appTop (orbitFunctions ec Wc t).val =
    ((s).resLE Uc _ (pullOpen_preimage_eq ec Wc).le).appTop
      (orbitFunctions ec Wc t).val at h
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using h

/-- Every original pair of chart lifts agrees modulo the full common-frame boundary ideal. -/
theorem normalizedOrbitBoundary_lift_difference
    (a : invariantCoordinates (restrictedAction
      (normalizedFullRelationAction f hL d V c k n o) U hU))
    (b : invariantCoordinates (restrictedAction
      (normalizedFullRelationAction f hL d V c k n' o') U' hU'))
    (ha : normalizedBoundaryChartMap f hL d V c k n o U hU a =
      normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t)
    (hb : normalizedBoundaryChartMap f hL d V c k n' o' U' hU' b =
      normalizedOrbitBoundaryCoefficient f hL d V c k n' o' W U' hU' hU'W t)
    (l : ℕ) (α : Fin n ↪ Fin l) (β : Fin n' ↪ Fin l) :
    (MixedFrames.jointChartFirst e o o' α β U U').appTop a.val -
      (MixedFrames.jointChartSecond e o o' α β U U').appTop b.val ∈
        RingHom.ker ((normalizedOriginalBoundaryInclusion f hL d V c k l (α o)) ∣_
          (MixedFrames.jointChartOpen e o o' α β U U')).appTop.hom := by
  have ht := jointOrbitBoundaryFunction_equalized f hL d V c k W t
  have ha' := congrArg Subtype.val ha
  have hb' := congrArg Subtype.val hb
  simp only [normalizedBoundaryChartMap, invariantMap_val,
    normalizedOrbitBoundaryCoefficient_val] at ha' hb'
  exact MixedFrames.jointChart_lifts_sub_mem_kernel e o o' α β U U' i z r s hr hs
    Uc (pullOpen_preimage_eq ec Wc)
    (normalizedOrbitBoundary_domain_le f hL d V c k n o W U hUW)
    (normalizedOrbitBoundary_domain_le f hL d V c k n' o' W U' hU'W)
    (orbitFunctions ec Wc t).val ht a.val b.val
    ha' hb'

/-- Actual invariant chart lifts can be chosen with compatibility on every exact common boundary. -/
theorem exists_normalizedOrbitBoundary_joint_lifts (hUa : IsAffineOpen U)
    (hU'a : IsAffineOpen U') :
    ∃ (a : invariantCoordinates (restrictedAction
        (normalizedFullRelationAction f hL d V c k n o) U hU))
      (b : invariantCoordinates (restrictedAction
        (normalizedFullRelationAction f hL d V c k n' o') U' hU')),
      normalizedBoundaryChartMap f hL d V c k n o U hU a =
        normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t ∧
      normalizedBoundaryChartMap f hL d V c k n' o' U' hU' b =
        normalizedOrbitBoundaryCoefficient f hL d V c k n' o' W U' hU' hU'W t ∧
      ∀ (l : ℕ) (α : Fin n ↪ Fin l) (β : Fin n' ↪ Fin l),
        (MixedFrames.jointChartFirst e o o' α β U U').appTop a.val -
          (MixedFrames.jointChartSecond e o o' α β U U').appTop b.val ∈
            RingHom.ker ((normalizedOriginalBoundaryInclusion f hL d V c k l (α o)) ∣_
              (MixedFrames.jointChartOpen e o o' α β U U')).appTop.hom := by
  obtain ⟨a, ha⟩ := normalizedOrbitBoundaryCoefficient_lift
    f hL d V c k n o W U hU hUW t hUa
  obtain ⟨b, hb⟩ := normalizedOrbitBoundaryCoefficient_lift
    f hL d V c k n' o' W U' hU' hU'W t hU'a
  exact ⟨a, b, ha, hb, normalizedOrbitBoundary_lift_difference
    f hL d V c k n n' o o' W U U' hU hU' hUW hU'W t a b ha hb⟩

end FLT.Mazur.HilbertChart.AffineRestriction
