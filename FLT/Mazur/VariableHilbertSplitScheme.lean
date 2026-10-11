/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertSplitQuotient
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The full split orbit quotient with its actual scheme structure

Affine neighborhoods are constructed from the proved full quotient
isomorphism. The resulting scheme has the original orbit carrier and invariant
structure sheaf verbatim, rather than only an abstract representing scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  [IsOpenImmersion V.hom] (c : (relativeFppfSheaf f).obj.obj (op V))
  (s : V ⟶ W) (hs : s ≫ b = 𝟙 V)
local notation "cW" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c

include hs in
/-- Affine schemes cover every point of the full split invariant quotient. -/
theorem variableHilbertSplitQuotient_affineNeighborhood
    (z : invariantLocallyRingedSpace (variableChartEquivalenceRelation f hL d W cW)) :
    ∃ (A : CommRingCat) (j : (Spec A).toLocallyRingedSpace ⟶
        invariantLocallyRingedSpace (variableChartEquivalenceRelation f hL d W cW)),
      z ∈ Set.range j.base ∧ LocallyRingedSpace.IsOpenImmersion j := by
  let e := variableHilbertSplitQuotientIso f hL d b c s hs
  obtain ⟨A, a, ha, y, hy⟩ := (variableHilbertTest f d V).left.exists_Spec_apply_eq (e.hom.base z)
  refine ⟨A, a.toLRSHom ≫ e.inv, ⟨y, ?_⟩, inferInstance⟩
  change e.inv.base (a y) = z
  rw [hy]
  exact congrArg (fun k ↦ k.base z) e.hom_inv_id

/-- Scheme effectivity on the original full orbit space and original invariant sheaf. -/
def variableHilbertSplitScheme : Scheme :=
  LocallyRingedSpace.IsOpenImmersion.scheme
    (invariantLocallyRingedSpace (variableChartEquivalenceRelation f hL d W cW))
    (variableHilbertSplitQuotient_affineNeighborhood f hL d b c s hs)

/-- The actual full quotient locally ringed space is preserved verbatim. -/
theorem variableHilbertSplitScheme_toLocallyRingedSpace :
    (variableHilbertSplitScheme f hL d b c s hs).toLocallyRingedSpace =
      invariantLocallyRingedSpace (variableChartEquivalenceRelation f hL d W cW) := rfl

/-- The constructed original invariant quotient is isomorphic to the target parameter scheme. -/
def variableHilbertSplitSchemeIso :
    variableHilbertSplitScheme f hL d b c s hs ≅ (variableHilbertTest f d V).left where
  hom := ⟨(variableHilbertSplitQuotientIso f hL d b c s hs).hom⟩
  inv := ⟨(variableHilbertSplitQuotientIso f hL d b c s hs).inv⟩
  hom_inv_id := Scheme.Hom.ext' (variableHilbertSplitQuotientIso f hL d b c s hs).hom_inv_id
  inv_hom_id := Scheme.Hom.ext' (variableHilbertSplitQuotientIso f hL d b c s hs).inv_hom_id

/-- The original orbit projection is now an actual scheme morphism. -/
def variableHilbertSplitSchemeProjection : (variableHilbertTest f d W).left ⟶
    variableHilbertSplitScheme f hL d b c s hs :=
  ⟨invariantLocallyRingedProjection (variableChartEquivalenceRelation f hL d W cW)⟩

/-- Its composition with the comparison is the original parameter-base change. -/
theorem variableHilbertSplitSchemeProjection_comparison :
    variableHilbertSplitSchemeProjection f hL d b c s hs ≫
      (variableHilbertSplitSchemeIso f hL d b c s hs).hom =
        (baseMarkedChartChange f b d).left :=
  Scheme.Hom.ext' (variableHilbertSplitQuotientIso_projection f hL d b c s hs)

/-- Changing the section leaves the original full quotient scheme unchanged. -/
theorem variableHilbertSplitScheme_independent (t : V ⟶ W) (ht : t ≫ b = 𝟙 V) :
    variableHilbertSplitScheme f hL d b c s hs = variableHilbertSplitScheme f hL d b c t ht :=
  PresheafedSpace.IsOpenImmersion.scheme_eq_of_locallyRingedSpace_eq rfl

/-- The full quotient comparison is canonical, independent of its chosen splitting. -/
theorem variableHilbertSplitQuotientIso_independent (t : V ⟶ W) (ht : t ≫ b = 𝟙 V) :
    variableHilbertSplitQuotientIso f hL d b c s hs =
      variableHilbertSplitQuotientIso f hL d b c t ht := by
  apply Iso.ext
  let e := variableChartEquivalenceRelation f hL d W cW
  let _ : Epi (invariantLocallyRingedProjection e) := by
    unfold invariantLocallyRingedProjection locallyRingedProjection
    infer_instance
  apply (cancel_epi (invariantLocallyRingedProjection e)).mp
  exact (variableHilbertSplitQuotientIso_projection f hL d b c s hs).trans
    (variableHilbertSplitQuotientIso_projection f hL d b c t ht).symm

end FLT.Mazur.HilbertChart
