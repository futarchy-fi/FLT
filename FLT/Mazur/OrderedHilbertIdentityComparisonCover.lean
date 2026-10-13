/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertIdentityOriginalSection
public import FLT.Mazur.OriginalRestrictedHilbertIntersection
public import FLT.Mazur.RelativeCoproductPullCover

/-!
# Original Picard comparison intersections cover the original smooth source

Each retained affine source meets the original smooth presentation through
its prescribed original parameter. The full intersections form an actual
etale cover, providing sheaf coverage independently of orbit-space openness.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertIdentityComparisonCover
open HilbertChart CartierAbel SchemePicard FCurve RelativeRelationOrbit
open OrderedHilbertAffineEtaleTestCover OrderedHilbertFaithfulTestCover AffineRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
local notation "T" => smoothHilbertSource f
local notation "s" => smoothHilbertSourceSection f hL
local notation "E" => fun x ↦ Sigma.fst (Sigma.snd (chartData f hL T s x))
local notation "d" => fun x ↦ Prod.snd (Sigma.fst (chartData f hL T s x))
local notation "c" => fun x ↦ chartClass f hL T s x
local notation "A" => OrderedHilbertIdentityOriginalSection.test f hL
local notation "k" => OrderedHilbertIdentityOriginalSection.parameter f hL
local notation "U" => OrderedHilbertIdentityOriginalSection.sourceTest f hL
local notation "sU" => OrderedHilbertIdentityOriginalSection.sourceSection f hL
local notation "sA" => OrderedHilbertIdentityOriginalSection.sectionAt f hL
local notation "ι" => OrderedHilbertIdentityOriginalSection.component f hL

/-- The retained affine component intersected with the ORIGINAL smooth presentation. -/
def intersection (x : (smoothHilbertSource f).left) : Over (Spec (.of R)) :=
  OriginalRestrictedIntersection.relation f hL (d x) (E x) (c x) (k x) T s

/-- The original affine parameter endpoint. -/
def toComponent (x : (smoothHilbertSource f).left) : intersection f hL x ⟶ A x :=
  OriginalRestrictedIntersection.fst f hL (d x) (E x) (c x) (k x) T s

/-- The endpoint in the original smooth presentation. -/
def toOriginal (x : (smoothHilbertSource f).left) : intersection f hL x ⟶ T :=
  OriginalRestrictedIntersection.snd f hL (d x) (E x) (c x) (k x) T s

instance toOriginal_etale (x : (smoothHilbertSource f).left) :
    Etale (toOriginal f hL x).left :=
  OriginalRestrictedIntersection.snd_etale f hL (d x) (E x) (c x) (k x) T s

/-- These are equal sections of the ORIGINAL Picard sheaf on each comparison intersection. -/
theorem original_class (x : (smoothHilbertSource f).left) :
    (relativeFppfSheaf f).obj.map (toComponent f hL x).op (sA x) =
      (relativeFppfSheaf f).obj.map (toOriginal f hL x).op s :=
  OriginalRestrictedIntersection.equal_class f hL (d x) (E x) (c x) (k x) T s

/-- Every retained original parameter has a point in its constructed effective affine source. -/
theorem parameter_contains (x : (smoothHilbertSource f).left) :
    ∃ a : (A x).left, (k x).left a = retainedParameter f hL x := by
  let p := retainedParameter f hL x
  let l := AffineParameterNeighborhood.chart f (d x) (E x) p
  let e := identityGroundQuotientSourceIso f hL (d x) (E x) (c x) l
  refine ⟨e.inv (AffineParameterNeighborhood.point f (d x) (E x) p), ?_⟩
  change l.left ((e.inv ≫ e.hom)
    (AffineParameterNeighborhood.point f (d x) (E x) p)) = p
  rw [e.inv_hom_id]
  exact AffineParameterNeighborhood.point_chart f (d x) (E x) p

/-- The full comparison intersection contains the prescribed original source point. -/
theorem point_covers (x : (smoothHilbertSource f).left) :
    ∃ z : (intersection f hL x).left, (toOriginal f hL x).left z = x := by
  obtain ⟨a, ha⟩ := parameter_contains f hL x
  let o := (toIntersection f hL T s x).left (data f hL T s x).2.2.2.2
  have ho : (variableHilbertOverlapToChart f (d x) hL (E x) (c x) T s).left o =
      (k x).left a := ha.symm
  have H := (IsPullback.of_hasPullback
    (variableHilbertOverlapToChart f (d x) hL (E x) (c x) T s) (k x)).map (Over.forget _)
  obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback H o a ho
  change (pullback.fst
    (variableHilbertOverlapToChart f (d x) hL (E x) (c x) T s) (k x)).left z = o at hz
  refine ⟨z, ?_⟩
  change (variableHilbertOverlapToTest f (d x) (E x) (c x) T s).left
    ((pullback.fst
      (variableHilbertOverlapToChart f (d x) hL (E x) (c x) T s) (k x)).left z) = x
  rw [hz]
  exact OrderedHilbertFaithfulTestCover.point_covers f hL T s x

/-- These specific full original intersections form an actual fppf covering family. -/
theorem covering : Sieve.ofArrows (intersection f hL) (toOriginal f hL) ∈
    (Scheme.fppfTopology.over (Spec (.of R))) T := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  apply Precoverage.generate_mem_toGrothendieck
  exact (Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation)
    (X := (T).left) (T).left (fun x ↦ (intersection f hL x).left)
    (fun x ↦ (toOriginal f hL x).left)
    (fun x ↦ ⟨x, (point_covers f hL x).choose, (point_covers f hL x).choose_spec⟩)
    (fun _ ↦ ⟨inferInstance, inferInstance⟩)).mem₀

end FLT.Mazur.OrderedHilbertIdentityComparisonCover
