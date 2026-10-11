/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertAffineEtaleCoverage
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import FLT.Mazur.SmoothTranslationOrbitOpen

/-!
# Actual étale covers by original full Hilbert intersections

Choose one constructed affine étale translation chart above each point of the
original test. Its full intersection with the original Picard class forms
an actual small étale covering family of that test.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertAffineEtaleTestCover
open HilbertChart CartierAbel SchemePicard FCurve OrderedCurvePower
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))

/-- A constructed ordered translation chart chosen above an original test point. -/
def chartData (x : T.left) :
    Σ i : SmoothHilbertTranslationIndex,
      Σ E : Over (Spec (.of R)), E ⟶ smoothTranslationTest f i.1 :=
  let h := exists_orderedHilbert_affine_etale_overlap_point f hL T s x
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose⟩

/-- The chosen translation class is the pullback of the original ordered translation. -/
def chartClass (x : T.left) :
    (relativeFppfSheaf f).obj.obj (op (chartData f hL T s x).2.1) :=
  (relativeFppfSheaf f).obj.map (chartData f hL T s x).2.2.op
    (smoothTranslationClass f hL.2.1 (chartData f hL T s x).1.1)

/-- Each member is the original full intersection, retaining independent base maps. -/
def intersection (x : T.left) : Over (Spec (.of R)) :=
  variableHilbertOverlap f (chartData f hL T s x).1.2
    (chartData f hL T s x).2.1 (chartClass f hL T s x) T s

/-- The original projection of a chosen full intersection to the test. -/
def toTest (x : T.left) : intersection f hL T s x ⟶ T :=
  variableHilbertOverlapToTest f (chartData f hL T s x).1.2
    (chartData f hL T s x).2.1 (chartClass f hL T s x) T s

/-- The constructed member is étale and contains a point above its chosen original point. -/
theorem chartData_spec (x : T.left) :
    IsAffine (chartData f hL T s x).2.1.left ∧
      Etale (chartData f hL T s x).2.1.hom ∧
      ∃ y : (intersection f hL T s x).left, (toTest f hL T s x).left y = x :=
  (exists_orderedHilbert_affine_etale_overlap_point f hL T s x).choose_spec.choose_spec.choose_spec

instance toTest_etale (x : T.left) : Etale (toTest f hL T s x).left := by
  let _ := (chartData_spec f hL T s x).2.1
  exact variableHilbertOverlapToTest_etale f _ _ _ _ _

/-- An actual small étale cover of the original test by its full chart intersections. -/
def cover : Scheme.Cover.{0} Scheme.etalePrecoverage T.left :=
  Scheme.Cover.mkOfCovers (P := @Etale) T.left
    (fun x ↦ (intersection f hL T s x).left) (fun x ↦ (toTest f hL T s x).left)
    (fun x ↦ ⟨x, (chartData_spec f hL T s x).2.2⟩) (fun _ ↦ inferInstance)

/-- These exact full intersections also give an fppf cover of the original test. -/
def fppfCover : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left :=
  Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) T.left
    (fun x ↦ (intersection f hL T s x).left) (fun x ↦ (toTest f hL T s x).left)
    (fun x ↦ ⟨x, (chartData_spec f hL T s x).2.2⟩) (fun _ ↦ ⟨inferInstance, inferInstance⟩)

/-- The full intersections generate a covering sieve in the original relative fppf site. -/
theorem covering : Sieve.ofArrows (intersection f hL T s) (toTest f hL T s) ∈
    (Scheme.fppfTopology.over (Spec (.of R))) T := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck (fppfCover f hL T s).mem₀

/-- The selected translation base is affine, as required by affine descent coordinates. -/
instance chartData_isAffine (x : T.left) : IsAffine (chartData f hL T s x).2.1.left :=
  (chartData_spec f hL T s x).1

/-- The selected translation base retains its actual étale structural morphism. -/
instance chartData_etale (x : T.left) : Etale (chartData f hL T s x).2.1.hom :=
  (chartData_spec f hL T s x).2.1

end FLT.Mazur.OrderedHilbertAffineEtaleTestCover

namespace FLT.Mazur.OrderedHilbertAffineEtaleOrbitCover
open HilbertChart CartierAbel SchemePicard FCurve RelativeRelationOrbit
open OrderedHilbertAffineEtaleTestCover
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
local notation "T" => smoothHilbertSource f
local notation "s" => smoothHilbertSourceSection f hL

/-- Apply the affine étale test construction to the original global smooth source. -/
def orbitOpen (x : (smoothHilbertSource f).left) :
    TopologicalSpace.Opens (Orbit (smoothHilbertEquivalenceRelation f hL)) :=
  smoothTranslationOrbitOpen f hL (chartData f hL T s x).1.2
    (chartData f hL T s x).2.1 (chartClass f hL T s x)

/-- Each original source point belongs to its chosen actual quotient neighborhood. -/
theorem projection_mem (x : (smoothHilbertSource f).left) :
    projection (smoothHilbertEquivalenceRelation f hL) x ∈ orbitOpen f hL x := by
  apply (mem_smoothTranslationOrbitOpen_iff f hL _ _ _ x).mpr
  exact (chartData_spec f hL T s x).2.2

/-- The neighborhoods from the chosen affine translations cover the ORIGINAL invariant quotient. -/
theorem covers : ⨆ x : (smoothHilbertSource f).left, orbitOpen f hL x = ⊤ := by
  apply top_le_iff.mp
  intro z _
  obtain ⟨x, rfl⟩ := projection_surjective (smoothHilbertEquivalenceRelation f hL) z
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, projection_mem f hL x⟩

end FLT.Mazur.OrderedHilbertAffineEtaleOrbitCover
