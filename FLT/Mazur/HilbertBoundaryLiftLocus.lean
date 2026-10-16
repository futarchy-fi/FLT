/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryPrincipalLifting
public import FLT.Mazur.RelativeRelationLiftLocus
public import FLT.Mazur.RelativeRelationIdealSourceCover

/-!
# The original boundary lifting locus and its source ideal

The original boundary section defines an actual open of the unchanged orbit
quotient. Membership is exactly finite-power obstruction vanishing on a
principal neighborhood. Full coverage is reduced to a unit-ideal equation in
the original affine source ring, not asserted as an additional hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "O" => Scheme.Hom.opensRange (Over.Hom.left (toEnvelope f hL d V c k))
local notation "B" => originalBoundarySource f hL d V c k
local notation "i" => originalBoundarySourceMap f hL d V c k
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

local notation "C" => originalClosedRelation f hL d V c k
local notation "r" => originalClosedFst f hL d V c k
local notation "s" => originalClosedSnd f hL d V c k
local notation "z" => originalClosedArrow f hL d V c k

open RelativeRelationOrbit
local notation "e" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k

attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation fst snd equivalence

local notation "m" => originalClosedInvariantMap f hL d V c k

variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
  (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
    (op ((TopologicalSpace.Opens.map
      (originalClosedInvariantMap f hL d V c k).base).obj W)))

/-- Actual invariant multipliers which lift the given original closed boundary section. -/
def originalBoundaryLiftIdeal : Ideal ((invariantSheaf e).obj.obj (op W)) :=
  closedLiftIdeal e ec (i).left (z).left
    (originalClosedArrow_left_fst f hL d V c k)
    (originalClosedArrow_left_snd f hL d V c k) W t

/-- The principal lifting locus is an actual open of the original quotient. -/
def originalBoundaryLiftOpen : TopologicalSpace.Opens (Orbit e) :=
  principalLiftOpen e ec (i).left (z).left
    (originalClosedArrow_left_fst f hL d V c k)
    (originalClosedArrow_left_snd f hL d V c k) W t

/-- The lifting multipliers generate this ideal in the original source section ring. -/
def originalBoundaryLiftSourceIdeal : Ideal Γ(A.left, (pullOpen e W).val) :=
  invariantIdealSource e W (originalBoundaryLiftIdeal f hL d V c k W t)

variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)

/-- Radical membership is the explicit original finite-power obstruction equation. -/
theorem originalBoundaryLiftIdeal_radical_iff
    (v : (invariantSheaf e).obj.obj (op W)) :
    v ∈ (originalBoundaryLiftIdeal f hL d V c k W t).radical ↔
      ∃ n : ℕ, originalClosedSectionObstruction f hL d V c k W hW
        (originalClosedSectionPullback f hL d V c k W v ^ n * t) = 0 := by
  change v ∈ (sectionLiftIdeal (originalClosedSectionPullback f hL d V c k W) t).radical ↔ _
  rw [mem_sectionLiftIdeal_radical]
  exact exists_congr fun n ↦
    (originalClosedSectionObstruction_eq_zero_iff f hL d V c k W hW _).symm

/-- The locus consists exactly of points admitting a unit denominator with vanishing power. -/
theorem mem_originalBoundaryLiftOpen_iff (x : Orbit e) :
    x ∈ originalBoundaryLiftOpen f hL d V c k W t ↔
      ∃ v : (invariantSheaf e).obj.obj (op W), x ∈ invariantPrincipal e W v ∧
        ∃ n : ℕ, originalClosedSectionObstruction f hL d V c k W hW
          (originalClosedSectionPullback f hL d V c k W v ^ n * t) = 0 := by
  change x ∈ sectionIdealOpen (ringedSpace e) W
    (originalBoundaryLiftIdeal f hL d V c k W t) ↔ _
  rw [← sectionIdealOpen_radical, mem_sectionIdealOpen]
  exact exists_congr fun v ↦ by
    rw [originalBoundaryLiftIdeal_radical_iff f hL d V c k W t hW v, and_comm]
    rfl

include hW in
/-- Original principal neighborhoods cover iff their source ideal is the unit ideal. -/
theorem originalBoundaryLiftOpen_eq_iff_sourceIdeal_top :
    originalBoundaryLiftOpen f hL d V c k W t = W ↔
      originalBoundaryLiftSourceIdeal f hL d V c k W t = ⊤ :=
  sectionIdealOpen_eq_iff_sourceIdeal_top e W
    (originalBoundaryLiftIdeal f hL d V c k W t) hW

end FLT.Mazur.HilbertChart.AffineRestriction
