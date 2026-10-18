/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormalizedBoundarySurjectivity
public import FLT.Mazur.EquivalenceRelationDoubleVanishingOpen
public import FLT.Mazur.SchemeRelationWholeFiberSections
public import FLT.Mazur.VariableHilbertNoetherianSource

/-!
# Constructed full-compatible raw opens on the actual Hilbert source

The uniform relation neighborhood produces one source open, chosen before
the boundary coefficient. Every exact invariant boundary coefficient has
a section on this open satisfying the full original pair equation.
The open is allowed to be empty; original-prime avoidance remains separate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] EquivalenceRelationNormalizedFrames.source
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
attribute [local irreducible] relation AffineRestriction.fst AffineRestriction.snd
variable (n : ℕ) (o : Fin n)
local notation "N" => normalizedFullRelationFrames f hL d V c k n o
local notation "ρ" => normalizedOriginalBoundaryAction f hL d V c k n o
local notation "τ" => normalizedFullRelationAction f hL d V c k n o
local notation "j" => normalizedOriginalBoundaryInclusion f hL d V c k n o
local notation "b" => normalizedOriginalBoundaryEndpoint f hL d V c k n o
local notation "hj" => normalizedOriginalBoundaryAction_inclusion f hL d V c k n o
variable (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ σ : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)

local notation "kS" => U.ι ≫ normalizedFullRelationFirst f hL d V c k n o
local notation "D" => SchemeRelationRestriction.doubleDomain p q kS
local notation "F" => SchemeRelationRestriction.fst p q kS
local notation "H" => SchemeRelationRestriction.snd p q kS
local notation "jU" => j ∣_ U
local notation "Bsource" => invariantCoordinates (boundaryOpenAction ρ τ j hj U hU)
open SchemeWholeFiberOpen

/-- The actual uniform good open of the direct full original relation. -/
def originalSourceGoodRelationOpen : (D).Opens :=
  completeDoubleRelationVanishingOpen e (Fin n) o U hU

/-- All complete first-endpoint arrows lie in the constructed original relation open. -/
theorem originalSourceGoodRelationOpen_contains :
    (F ≫ U.ι) ⁻¹' completePointLocus («p» := p) («q» := q) (Fin n) o ⊆
      originalSourceGoodRelationOpen f hL d V c k n o U hU := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  exact completeDoubleRelationVanishingOpen_contains e (Fin n) o U hU

omit [Etale V.hom] in
/-- Every invariant coefficient equalizes on the same actual full relation open. -/
theorem originalSourceGoodRelationOpen_equalizes
    (a : invariantCoordinates (restrictedAction τ U hU)) :
    ((originalSourceGoodRelationOpen f hL d V c k n o U hU).ι ≫ F).appTop a.val =
      ((originalSourceGoodRelationOpen f hL d V c k n o U hU).ι ≫ H).appTop a.val :=
  completeDoubleRelationVanishingOpen_equalizes e (Fin n) o U hU a

/-- A source open constructed before choosing any boundary section. -/
def originalSourceConstructedOpen : U.toScheme.Opens :=
  locus F (originalSourceGoodRelationOpen f hL d V c k n o U hU)

local notation "Ogood" => originalSourceConstructedOpen f hL d V c k n o U hU

/-- Exact boundary lifts with full pair compatibility exist on the constructed raw open. -/
theorem originalSourceConstructedOpen_boundary_sections (ha : IsAffineOpen U) (t : Bsource) :
    ∃ v : Γ((Ogood).toScheme, ⊤),
      ((jU) ∣_ Ogood).appTop v = ((jU) ⁻¹ᵁ Ogood).ι.appTop t.val ∧
      (pairOpenFirst Ogood F H).appTop v = (pairOpenSecond Ogood F H).appTop v := by
  obtain ⟨a, ha⟩ := normalizedBoundaryChartMap_surjective f hL d V c k n o U hU ha t
  refine ⟨(Ogood).ι.appTop a.val, ?_, ?_⟩
  · exact restricted_global_boundary_equation a.val Ogood jU t.val (congrArg Subtype.val ha)
  · exact wholeFiber_restricted_pair_equation F H
      (originalSourceGoodRelationOpen f hL d V c k n o U hU) a.val
      (originalSourceGoodRelationOpen_equalizes f hL d V c k n o U hU a)

end FLT.Mazur.HilbertChart.AffineRestriction
