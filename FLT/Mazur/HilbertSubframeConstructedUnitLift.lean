/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSubframeUnitNeighborhood
public import FLT.Mazur.HilbertSubframeAffineTargets

/-!
# Unscaled transfer with a geometrically constructed affine target

A unit binomial degree at an original source point suffices to construct both
source and target charts and an exact unscaled boundary lift. Every selected
image lands in the constructed target. No target chart or selection inclusion
is supplied as input, and all schemes retain their nonreduced structure.
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

variable (m' : ℕ) (a : Fin m')
  (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
    (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

attribute [local irreducible] normalizedBoundaryChartMap normalizedOrbitBoundaryCoefficient

include hU in
/-- Construct all charts and an exact original lift from a unit degree in the source stalk. -/
theorem exists_originalSubframe_constructed_unit_lift
    (x : normalizedFullRelationFrames f hL d V c k n o) (hxU : x ∈ U)
    (hxW : normalizedFullRelationFirst f hL d V c k n o x ∈ (pullOpen eo W).val)
    (hn : IsUnit (n.choose m' :
      (normalizedFullRelationFrames f hL d V c k n o).presheaf.stalk x)) :
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
  obtain ⟨Us, ha, hUsW, hUs, Y, hYaff, hxY, hYU, hYW, hY, hSel⟩ :=
    exists_normalized_subframe_affine_family f hL d V c k n o
      (pullOpen eo W).val (pullOpen_preimage_eq eo W) U hU
      (fun _ : Unit ↦ m') (fun _ ↦ a) x hxU hxW
  obtain ⟨Z, hZ, hZW, hZaff, hxZ, hZY, hZs, hNZ, v, hv, hw⟩ :=
    exists_originalSubframe_unit_neighborhood f hL d V c k n o W Y hY hYW
      m' a (Us ()) (hUs ()) (hSel ()) (hUsW ()) t hYaff (ha ()) x hxY hn
  exact ⟨Us (), hUs (), hUsW (), Z, hZ, hZW, ha (), hZaff, hxZ, hZY.trans hYU,
    hZs, hNZ, v, hv, hw⟩

end FLT.Mazur.HilbertChart.AffineRestriction
