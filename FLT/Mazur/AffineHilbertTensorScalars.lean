/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertTensorPullback

/-!
# Original structural scalars on glued tensor coefficients

The matching-family ring carries the original relation's structural R-algebra.
Its component scalars are the native scalars in every literal localization.
The gluing isomorphism, both original endpoints and the global counit preserve R.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation AffineProductTensorCoordinates
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "Z" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
/-- The algebra induced by the original source structural morphism. -/
local instance matchingScalarSourceAlgebra : Algebra R Γ(A.left, ⊤) :=
  affineBaseSectionAlgebra A.hom
/-- The algebra induced by the original translation structural morphism. -/
local instance matchingScalarTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom


namespace TensorChart
/-- The R-algebra on global relation functions is induced by its original structural morphism. -/
local instance matchingRelationAlgebra : Algebra R Γ((Z).left, ⊤) :=
  affineBaseSectionAlgebra (Z).hom

/-- Structural relation scalars are exactly original second-endpoint source scalars. -/
theorem toMatching_scalar (r : R) :
    toMatching f hL d V c k (algebraMap R Γ((Z).left, ⊤) r) =
      matchingTest f hL d V c k (algebraMap R Γ(A.left, ⊤) r) := by
  have hq : (q).left ≫ A.hom = (Z).hom := (q).w
  change toMatching f hL d V c k ((Z).hom.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) =
    toMatching f hL d V c k
      (((q).left ≫ A.hom).appTop ((Scheme.ΓSpecIso (.of R)).inv r))
  rw [hq]

/-- The original structural algebra transported through actual coefficient gluing. -/
@[instance_reducible] def matchingAlgebra : Algebra R (matchingRing f hL d V c k) :=
  ((toMatching f hL d V c k).comp (algebraMap R Γ((Z).left, ⊤))).toAlgebra

attribute [local instance] matchingAlgebra

/-- Every component retains its native literal-localization R-algebra, without twisting scalars. -/
theorem matchingAlgebra_component (r : R) (T : TensorChart f hL d V c k) :
    (algebraMap R (matchingRing f hL d V c k) r).val T =
      algebraMap R (Localization.Away T.denominator) r := by
  change (toMatching f hL d V c k (algebraMap R Γ((Z).left, ⊤) r)).val T = _
  rw [toMatching_scalar]
  exact (localizedTestAlgHom f hL d V c k T.denominator T.domain T.image_eq).commutes r

/-- Gluing is an isomorphism for the actual original structural R-algebras. -/
def globalAlgEquiv : Γ((Z).left, ⊤) ≃ₐ[R] matchingRing f hL d V c k :=
  { globalEquiv f hL d V c k with commutes' := fun _ ↦ rfl }

/-- The first original endpoint induces an R-algebra map into matching localized coefficients. -/
def matchingSourceAlgHom : Γ(A.left, ⊤) →ₐ[R] matchingRing f hL d V c k := by
  refine ⟨matchingSource f hL d V c k, ?_⟩
  intro r
  apply Subtype.ext
  funext T
  change localizedSourceMap f hL d V c k T.denominator T.domain T.image_eq
    (algebraMap R Γ(A.left, ⊤) r) = (algebraMap R (matchingRing f hL d V c k) r).val T
  rw [matchingAlgebra_component]
  exact (localizedSourceAlgHom f hL d V c k T.denominator T.domain T.image_eq).commutes r

/-- The second original endpoint is the compatible family of the original tensor-factor maps. -/
def matchingTestAlgHom : Γ(A.left, ⊤) →ₐ[R] matchingRing f hL d V c k := by
  refine ⟨matchingTest f hL d V c k, ?_⟩
  intro r
  exact (toMatching_scalar f hL d V c k r).symm

/-- The original full identity counit preserves the same structural R-algebra. -/
def matchingCounitAlgHom : matchingRing f hL d V c k →ₐ[R] Γ(A.left, ⊤) := by
  refine ⟨matchingCounit f hL d V c k, ?_⟩
  intro r
  change matchingCounit f hL d V c k (algebraMap R (matchingRing f hL d V c k) r) = _
  rw [← (matchingSourceAlgHom f hL d V c k).commutes r]
  exact matchingCounit_source f hL d V c k (algebraMap R Γ(A.left, ⊤) r)

end TensorChart
end FLT.Mazur.HilbertChart.AffineRestriction
