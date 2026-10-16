/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryLiftLocus
public import FLT.Mazur.RelativeRelationPulledIdealCover

/-!
# A source ideal certificate for coverage of the original boundary

Only boundary points need the local lifting construction. Their coverage is
exactly the unit-ideal condition after restricting the original lifting
multipliers to the original affine closed source. A finite coefficient identity
certifies this condition without assuming that the ambient quotient is covered.
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
local notation "J" => originalBoundaryLiftIdeal f hL d V c k W t
local notation "N" => originalBoundaryLiftOpen f hL d V c k W t
local notation "Wc" =>
  (Functor.obj
    (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base (LocallyRingedSpace.Hom.toHom m))) W)
local notation "Nc" =>
  (Functor.obj
    (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base (LocallyRingedSpace.Hom.toHom m))) N)

/-- The lifting multipliers generate this actual ideal on the unchanged closed source. -/
def originalBoundaryLiftClosedSourceIdeal : Ideal Γ((B).left, (pullOpen ec Wc).val) :=
  Ideal.span (pulledIdealSourceGenerators e ec (i).left (z).left
    (originalClosedArrow_left_fst f hL d V c k)
    (originalClosedArrow_left_snd f hL d V c k) W J)

variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
include hW

/-- The actual closed source over this orbit domain is affine. -/
theorem originalBoundaryLift_closedSource_affine :
    IsAffineOpen (pullOpen ec Wc).val := by
  change IsAffineOpen (pullOpen ec ((TopologicalSpace.Opens.map
    (invariantMap e ec (i).left (z).left
      (originalClosedArrow_left_fst f hL d V c k)
      (originalClosedArrow_left_snd f hL d V c k)).base).obj W)).val
  rw [invariantMap_sourceOpen_eq]
  exact hW.preimage (i).left

/-- Enough lifting neighborhoods cover the boundary exactly when this closed-source ideal is one. -/
theorem originalBoundaryLift_boundary_cover_iff :
    Nc = Wc ↔ originalBoundaryLiftClosedSourceIdeal f hL d V c k W t = ⊤ :=
  preimage_sectionIdealOpen_eq_iff_sourceIdeal_top e ec (i).left (z).left
    (originalClosedArrow_left_fst f hL d V c k)
    (originalClosedArrow_left_snd f hL d V c k) W J
    (originalBoundaryLift_closedSource_affine f hL d V c k W hW)

/-- Boundary coverage has a finite source identity using actual original lifting multipliers. -/
theorem originalBoundaryLift_boundary_cover_iff_certificate :
    Nc = Wc ↔ ∃ a : J →₀ (sourceSheaf ec).obj.obj (op Wc),
      a.sum (fun v b ↦ b * (invariantInclusion ec).hom.app (op Wc)
        ((m).c.app (op W) v.val)) = 1 := by
  rw [originalBoundaryLift_boundary_cover_iff f hL d V c k W t hW]
  exact pulledIdealSource_eq_top_iff_certificate e ec (i).left (z).left
    (originalClosedArrow_left_fst f hL d V c k)
    (originalClosedArrow_left_snd f hL d V c k) W J

end FLT.Mazur.HilbertChart.AffineRestriction
