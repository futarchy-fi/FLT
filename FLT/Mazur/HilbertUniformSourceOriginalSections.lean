/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryUniformRelationCorrections
public import FLT.Mazur.EquivalenceRelationUniformSourceOpen
public import FLT.Mazur.RelativeRelationEtaleSourceFunctions

/-!
# Original orbit sections on the constructed uniform source open

Every moving-invariant coefficient restricts to a unique original invariant
section on the orbit image of the constructed source open. Boundary lifts
retain their exact boundary chart equation. Coverage by these opens and the
original scalar multiplier certificate are not claimed.
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
local notation "B" => uniformSourceOpen e (Fin n) o U hU
local notation "j" => (B).ι ≫ U.ι ≫ normalizedFullRelationFirst f hL d V c k n o
local notation "r" => SchemeRelationRestriction.fst p q j
local notation "s" => SchemeRelationRestriction.snd p q j
local notation "O" => orbitImageOpen eo (q).isOpenMap (etaleSourceImage j)

/-- Each original moving invariant descends on the constructed source orbit image. -/
theorem uniformSource_original_section_existsUnique
    (t : invariantCoordinates (restrictedAction
      (normalizedFullRelationAction f hL d V c k n o) U hU)) :
    ∃! b : (invariantSheaf eo).obj.obj (op O),
      (etaleSourceFunctionEquiv eo (q).isOpenMap j b).val = (B).ι.appTop t.val := by
  let v : SchemeEffectiveEpiSections.compatibleFunctions r s :=
    ⟨(B).ι.appTop t.val, uniformSourceOpen_compatible e (Fin n) o U hU t⟩
  let E := etaleSourceFunctionEquiv eo (q).isOpenMap j
  refine ⟨E.symm v, congrArg Subtype.val (E.apply_symm_apply v), ?_⟩
  intro b hb
  apply E.injective
  exact (Subtype.ext hb).trans (E.apply_symm_apply v).symm

/-- Actual boundary chart lifts construct original sections with their exact chart data. -/
theorem uniformSource_original_boundary_section
    (ha : IsAffineOpen U) (W : TopologicalSpace.Opens (Orbit eo))
    (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val)
    (t : (invariantSheaf ec).obj.obj (op ((TopologicalSpace.Opens.map (m).base).obj W))) :
    ∃ b : (invariantSheaf eo).obj.obj (op O),
      ∃ v : invariantCoordinates (restrictedAction
        (normalizedFullRelationAction f hL d V c k n o) U hU),
        (etaleSourceFunctionEquiv eo (q).isOpenMap j b).val = (B).ι.appTop v.val ∧
        normalizedBoundaryChartMap f hL d V c k n o U hU v =
          normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t := by
  obtain ⟨v, hv⟩ := normalizedOrbitBoundaryCoefficient_lift f hL d V c k n o W U hU hUW t ha
  obtain ⟨b, hb, _⟩ := uniformSource_original_section_existsUnique f hL d V c k n o U hU v
  exact ⟨b, v, hb, hv⟩

/-- The constructed original orbit image remains inside the prescribed original domain. -/
theorem uniformSource_orbitImage_le (W : TopologicalSpace.Opens (Orbit eo))
    (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val) :
    O ≤ W := by
  rintro y ⟨x, ⟨z, rfl⟩, rfl⟩
  exact hUW ((B).ι z).property

end FLT.Mazur.HilbertChart.AffineRestriction
