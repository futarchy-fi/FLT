/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertSplitTranslationSource
public import FLT.Mazur.AffineHilbertSelectorOrbitOpen
public import FLT.Mazur.AffineHilbertFiniteSelectorKernel

/-!
# Constructed original orbit quotients through split translation branches

A translation section constructs original representative arrows on its actual
open source slice. Orbit propagation gives an etale surjective scheme quotient
of the saturated ORIGINAL source open. On affine slices the finite coefficient
kernel is also proved. No full-envelope, selector or kernel premise is supplied.
The original ground is unchanged; arbitrary nonsplit translation coverage is open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left] (s : Over.mk (𝟙 (Spec (.of R))) ⟶ V)
local notation "u" => splitTranslationSourceMap f d V k s
local notation "l" => splitTranslationChart f d V k s
local notation "p" => fst f hL d V c l
local notation "q" => snd f hL d V c l
local notation "e" => equivalence f hL d V c l

omit [Etale V.hom] [IsOpenImmersion k.left] in
/-- The constructed arrows begin at their literal original source points. -/
theorem splitTranslation_selector_fst : (e).r.left ≫ (p).left = 𝟙 _ :=
  congrArg Over.Hom.left (e).reflexivity₁

/-- Their invariance follows from the section slice, rather than an assumed selector field. -/
theorem splitTranslation_selector_invariant :
    (p).left ≫ (e).r.left ≫ (q).left = (q).left ≫ (e).r.left ≫ (q).left := by
  exact congrArg (fun t : relation f hL d V c l ⟶ splitTranslationSource f d V k s ↦
    t.left ≫ (e).r.left ≫ (q).left) (splitTranslation_endpoints f hL d V c k s)

/-- The constructed quotient target over the unchanged original proper-family base. -/
def splitTranslationOrbitTarget : Over (Spec (.of R)) :=
  selectorTarget f hL d V c l (e).r.left

/-- The original source open is its actual orbit saturation, with a constructed scheme quotient. -/
def splitTranslationOrbitProjection :
    (originalOrbitOpenSource f hL d V c k (u).left).left ⟶
      (splitTranslationOrbitTarget f hL d V c k s).left :=
  selectorOrbitOpenProjection f hL d V c k u (e).r.left
    (splitTranslation_selector_fst f hL d V c k s)
    (splitTranslation_selector_invariant f hL d V c k s)

local notation "l'" => originalOrbitOpenParameter f hL d V c k (Over.Hom.left u)

/-- The rebuilt ORIGINAL Picard relation is the complete constructed orbit quotient kernel. -/
theorem splitTranslationOrbit_isPullback :
    IsPullback (fst f hL d V c l').left (snd f hL d V c l').left
      (splitTranslationOrbitProjection f hL d V c k s)
      (splitTranslationOrbitProjection f hL d V c k s) :=
  selectorOrbitOpenProjection_isPullback f hL d V c k u (e).r.left
    (splitTranslation_selector_fst f hL d V c k s)
    (splitTranslation_selector_invariant f hL d V c k s)

/-- Both etaleness and surjectivity are conclusions of the original-arrow construction. -/
theorem splitTranslationOrbit_cover :
    Etale (splitTranslationOrbitProjection f hL d V c k s) ∧
      Surjective (splitTranslationOrbitProjection f hL d V c k s) := by
  let _ : IsOpenImmersion (u ≫ k).left :=
    inferInstanceAs (IsOpenImmersion (splitTranslationChart f d V k s).left)
  exact selectorOrbitOpenProjection_cover f hL d V c k u (e).r.left
    (splitTranslation_selector_fst f hL d V c k s)
    (splitTranslation_selector_invariant f hL d V c k s)

/-- The quotient retains the ORIGINAL base morphism as an equality of scheme morphisms. -/
@[reassoc]
theorem splitTranslationOrbit_ground :
    splitTranslationOrbitProjection f hL d V c k s ≫
      (splitTranslationOrbitTarget f hL d V c k s).hom =
        (originalOrbitOpenSource f hL d V c k (u).left).hom :=
  selectorOrbitOpenProjection_ground f hL d V c k u (e).r.left
    (splitTranslation_selector_fst f hL d V c k s)
    (splitTranslation_selector_invariant f hL d V c k s)

/-- Each original point on the chosen translation branch lies in the constructed orbit open. -/
theorem splitTranslationOrbit_contains (x : A.left)
    (hx : (k ≫ variableHilbertBase f d V).left x = s.left (A.hom x)) :
    ∃ y : (originalOrbitOpenSource f hL d V c k (u).left).left,
      (originalOrbitOpenToSource f hL d V c k (u).left).left y = x := by
  obtain ⟨z, hz⟩ := splitTranslation_contains f d V k s x hx
  obtain ⟨y, hy, _⟩ := originalOrbitOpen_seed_point f hL d V c k (u).left z
  exact ⟨y, hy.trans hz⟩

/-- The fresh finite model on the affine slice has its full original kernel. -/
theorem splitTranslationFinite_isPullback [IsAffine A.left] [IsAffine V.left] :
    IsPullback (p).left (q).left (finiteKernelProjection f hL d V c l).left
      (finiteKernelProjection f hL d V c l).left :=
  finiteSelector_isPullback f hL d V c l (e).r.left
    (splitTranslation_selector_fst f hL d V c k s)
    (splitTranslation_selector_invariant f hL d V c k s)

end FLT.Mazur.HilbertChart.AffineRestriction
