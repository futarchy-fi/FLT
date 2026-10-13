/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteKernelModel
public import FLT.Mazur.ConstructibleDenseInterior

/-!
# A dense open in the actual finite coefficient model image

The finite model projection is dominant because its coefficients are literally
included in the original source functions. Chevalley's theorem makes its image
constructible. Its interior is therefore a dense open consisting of actual
image points. This does not claim flatness or equality with the Picard kernel.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "C" => finiteKernelCoefficientAlgebra f hL d V c k
local notation "v" => finiteKernelProjection f hL d V c k
local notation "Q" => finiteKernelModel f hL d V c k

/-- The finite coefficient projection is injective on the actual global section rings. -/
theorem finiteKernelProjection_appTop_injective : Function.Injective (v).left.appTop := by
  have h : (v).left.appTop =
      (Scheme.ΓSpecIso (.of C)).hom ≫ finiteKernelCoefficientInclusion f hL d V c k := by
    rw [← Iso.inv_comp_eq]
    exact finiteKernelProjection_coefficients f hL d V c k
  rw [h]
  exact (Subtype.val_injective.comp Subtype.val_injective).comp
    (Scheme.ΓSpecIso (.of C)).commRingCatIsoToRingEquiv.injective

/-- The constructed finite model has dense original-source image. -/
instance finiteKernelProjection_isDominant : IsDominant (v).left :=
  isDominant_of_of_appTop_injective (finiteKernelProjection_appTop_injective f hL d V c k)

/-- Chevalley applies to the actual projection, retaining its scheme-theoretic construction. -/
theorem finiteKernelProjection_range_constructible :
    IsConstructible (Set.range (v).left) := by
  simpa only [Set.image_univ] using (v).left.isConstructible_image IsConstructible.univ

/-- The canonical open consists only of points in the actual parameter image. -/
def finiteModelImageInterior : (Q).left.Opens :=
  ⟨interior (Set.range (v).left), isOpen_interior⟩

/-- The image interior is dense even for reducible or nonreduced original coefficient bases. -/
theorem finiteModelImageInterior_dense :
    Dense (finiteModelImageInterior f hL d V c k : Set (Q).left) :=
  ConstructibleDenseInterior.dense_interior
    (finiteKernelProjection_range_constructible f hL d V c k) (v).left.denseRange

/-- Every point of the constructed target open has an original parameter preimage. -/
theorem finiteModelImageInterior_subset_range :
    (finiteModelImageInterior f hL d V c k : Set (Q).left) ⊆ Set.range (v).left :=
  interior_subset

/-- Any open where the original projection is onto lies in the constructed open. -/
theorem finiteModelImageInterior_maximal (U : (Q).left.Opens)
    (hU : (U : Set (Q).left) ⊆ Set.range (v).left) :
    U ≤ finiteModelImageInterior f hL d V c k :=
  interior_maximal hU U.isOpen

end FLT.Mazur.HilbertChart.AffineRestriction
