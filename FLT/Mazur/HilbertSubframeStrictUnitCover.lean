/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSubframeConstructedUnitLift
public import FLT.Mazur.SubframeDegreeUnitCover

/-!
# Constructed strict unit-degree neighborhoods cover non-prime-power frames

At every original source point of non-prime-power size, choose a positive
strict target size with unit degree in the stalk, then construct both affine
charts and the unscaled lift. This combines arithmetic coverage with actual
all-selection target coverage; it makes no claim about embedding errors.
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
variable (n : ℕ) (o : Fin n)
local notation "N" => normalizedFullRelationFrames f hL d V c k n o
local notation "ρ" => normalizedOriginalBoundaryAction f hL d V c k n o
local notation "τ" => normalizedFullRelationAction f hL d V c k n o
local notation "j" => normalizedOriginalBoundaryInclusion f hL d V c k n o
local notation "b" => normalizedOriginalBoundaryEndpoint f hL d V c k n o
local notation "hj" => normalizedOriginalBoundaryAction_inclusion f hL d V c k n o
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "Uc" => (pullOpen ec Wc).val
variable (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ σ : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)

variable (hn : 1 < n) (hp : ¬ IsPrimePow n)
  (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
    (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

attribute [local irreducible] normalizedBoundaryChartMap normalizedOrbitBoundaryCoefficient

include hU hn hp in
/-- Every point has constructed strict affine charts and an exact normalized boundary lift. -/
theorem exists_originalSubframe_strict_unit_lift
    (x : normalizedFullRelationFrames f hL d V c k n o) (hxU : x ∈ U)
    (hxW : normalizedFullRelationFirst f hL d V c k n o x ∈ (pullOpen eo W).val) :
    ∃ m' ∈ Finset.Icc 1 (n - 1), ∃ a : Fin m',
    ∃ (T : (normalizedFullRelationFrames f hL d V c k m' a).Opens)
      (hT : ∀ σ, (normalizedFullRelationAction f hL d V c k m' a σ).hom ⁻¹ᵁ T = T)
      (hTW : T ≤ normalizedFullRelationFirst f hL d V c k m' a ⁻¹ᵁ (pullOpen eo W).val)
      (Z : (normalizedFullRelationFrames f hL d V c k n o).Opens)
      (hZ : ∀ σ, (τ σ).hom ⁻¹ᵁ Z = Z)
      (hZW : Z ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val),
      IsAffineOpen T ∧ IsAffineOpen Z ∧ x ∈ Z ∧ Z ≤ U ∧
      ∃ hSel : ∀ ι : Fin m' ↪ Fin n, Z ≤ subframeMap e o a ι ⁻¹ᵁ T,
      ∃ hNZ : IsUnit ((Fintype.card (Fin n)).choose (Fintype.card (Fin m')) :
          Γ(Z.toScheme, ⊤)),
      ∃ v : invariantCoordinates (restrictedAction
          (normalizedFullRelationAction f hL d V c k m' a) T hT),
        normalizedBoundaryChartMap f hL d V c k m' a T hT v =
          normalizedOrbitBoundaryCoefficient f hL d V c k m' a W T hT hTW t ∧
        normalizedBoundaryChartMap f hL d V c k n o Z hZ
          (subframeNormalizedTransfer e o a Z hZ T hT hSel hNZ v) =
            normalizedOrbitBoundaryCoefficient f hL d V c k n o W Z hZ hZW t := by
  obtain ⟨m', hm, hunit⟩ := SubframeDegreeUnitCover.exists_binomial_isUnit
    (R := (normalizedFullRelationFrames f hL d V c k n o).presheaf.stalk x) n hn hp
  let a : Fin m' := ⟨0, lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1⟩
  exact ⟨m', hm, a, exists_originalSubframe_constructed_unit_lift
    f hL d V c k n o W U hU m' a t x hxU hxW hunit⟩

end FLT.Mazur.HilbertChart.AffineRestriction
