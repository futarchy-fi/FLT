/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryFiniteMultipliers
public import FLT.Mazur.EquivalenceRelationOpenChartScalars

/-!
# Constructed compatible scalar families on the finite original atlas

Every original invariant scalar gives an actual finite family of invariant
chart coefficients. Their full mixed compatibility is proved, and finite
cover descent recovers the same original scalar uniquely.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relativeFppfSheaf AmpleLineBundle
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
attribute [local irreducible] relation fst snd equivalence
  EquivalenceRelationNormalizedFrames.source
namespace OrbitBoundaryAtlas.FiniteAtlas
attribute [local irreducible] finiteCharts lifts obstruction
local notation "e" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen e W).val

variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
local notation "C" => finiteCharts f hL d V c k W hW

local notation "p" => Over.Hom.left (AffineRestriction.fst f hL d V c k)
local notation "q" => Over.Hom.left (AffineRestriction.snd f hL d V c k)

omit [IsAffine V.left] [Etale V.hom] [IsAffine A.left] [IsOpenImmersion k.left] in
/-- An original invariant scalar satisfies the actual restricted scheme-relation equation. -/
theorem original_scalar_equalized (a : (invariantSheaf e).obj.obj (op W)) :
    ((p) ∣_ E).appTop (orbitFunctions e W a).val =
      ((q).resLE E _ (pullOpen_preimage_eq e W).le).appTop (orbitFunctions e W a).val := by
  have h := (orbitFunctions e W a).property
  change ((p).resLE E _ le_rfl).appTop (orbitFunctions e W a).val =
    ((q).resLE E _ (pullOpen_preimage_eq e W).le).appTop (orbitFunctions e W a).val at h
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using h

/-- The original scalar determines invariant coefficients on all selected finite charts. -/
def scalarFamily (a : (invariantSheaf e).obj.obj (op W)) : Sections f hL d V c k W hW :=
  fun j ↦ openChartScalar (fullRelationSchemeEquivalence f hL d V c k)
    E (pullOpen_preimage_eq e W) (orbitFunctions e W a).val
    (original_scalar_equalized f hL d V c k W a)
    j.val.label j.val.domain j.val.stable j.val.overDomain

/-- Every chart coefficient is exactly the original scalar pulled back by its chart map. -/
theorem scalarFamily_val (a : (invariantSheaf e).obj.obj (op W)) (j : C) :
    (scalarFamily f hL d V c k W hW a j).val =
      (chartMap f hL d V c k W j.val).appTop (orbitFunctions e W a).val := rfl

/-- Full mixed compatibility is a proved property of the constructed scalar family. -/
theorem scalarFamily_compatible (a : (invariantSheaf e).obj.obj (op W)) (j l : C) :
    (MixedFrames.mixedChartFirst j.val.label l.val.label j.val.domain l.val.domain).appTop
        (scalarFamily f hL d V c k W hW a j).val =
      (MixedFrames.mixedChartSecond j.val.label l.val.label j.val.domain l.val.domain).appTop
        (scalarFamily f hL d V c k W hW a l).val :=
  openChartScalar_compatible (fullRelationSchemeEquivalence f hL d V c k)
    E (pullOpen_preimage_eq e W) (orbitFunctions e W a).val
    (original_scalar_equalized f hL d V c k W a)
    j.val.label j.val.domain j.val.stable j.val.overDomain
    l.val.label l.val.domain l.val.stable l.val.overDomain

/-- Equality of scalar families detects equality of the unchanged original invariant sections. -/
theorem scalarFamily_injective : Function.Injective (scalarFamily f hL d V c k W hW) := by
  intro a b hab
  apply (orbitFunctions e W).injective
  apply Subtype.ext
  apply finite_sections_ext f hL d V c k W hW
  intro j
  exact congrArg (fun v : Sections f hL d V c k W hW ↦ (v j).val) hab

/-- Descent of a constructed family recovers its specified original scalar. -/
theorem scalarFamily_recovers (a b : (invariantSheaf e).obj.obj (op W))
    (hb : ∀ j : C, (chartMap f hL d V c k W j.val).appTop
      (orbitFunctions e W b).val = (scalarFamily f hL d V c k W hW a j).val) : b = a := by
  apply (orbitFunctions e W).injective
  apply Subtype.ext
  exact finite_sections_ext f hL d V c k W hW hb

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
