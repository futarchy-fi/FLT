/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertTensorGluing

/-!
# The ring of compatible literal tensor coefficients

The ring cut out by the actual product-denominator overlap equations is
isomorphic to global functions on the original full relation. The two
original endpoint maps become their constructed localized formulas.
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
local instance matchingSourceAlgebra : Algebra R Γ(A.left, ⊤) :=
  affineBaseSectionAlgebra A.hom
/-- The algebra induced by the original translation structural morphism. -/
local instance matchingTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom


namespace TensorChart

/-- Matching families in the original tensor localization rings. -/
def matchingRing : Subring ((T : TensorChart f hL d V c k) →
    Localization.Away T.denominator) where
  carrier := {z | ∀ T S,
    restrict f hL d V c k T (inter f hL d V c k T S) inf_le_left (z T) =
      restrict f hL d V c k S (inter f hL d V c k T S) inf_le_right (z S)}
  zero_mem' := by intro T S; simp only [Pi.zero_apply, map_zero]
  one_mem' := by intro T S; simp only [Pi.one_apply, map_one]
  add_mem' := by
    intro z w hz hw T S
    simp only [Pi.add_apply, map_add, hz T S, hw T S]
  mul_mem' := by
    intro z w hz hw T S
    simp only [Pi.mul_apply, map_mul, hz T S, hw T S]
  neg_mem' := by
    intro z hz T S
    simp only [Pi.neg_apply, map_neg, hz T S]

/-- The ring map from original global functions to their matching localized coordinates. -/
def toMatching : Γ((Z).left, ⊤) →+* matchingRing f hL d V c k where
  toFun a := ⟨fun T ↦ globalMap f hL d V c k T a, by
    intro T S
    rw [restrict_global, restrict_global]⟩
  map_one' := Subtype.ext (funext fun T ↦ (globalMap f hL d V c k T).map_one)
  map_mul' a b := Subtype.ext (funext fun T ↦ (globalMap f hL d V c k T).map_mul a b)
  map_zero' := Subtype.ext (funext fun T ↦ (globalMap f hL d V c k T).map_zero)
  map_add' a b := Subtype.ext (funext fun T ↦ (globalMap f hL d V c k T).map_add a b)

/-- Every matching family comes from exactly one original global relation function. -/
theorem toMatching_bijective : Function.Bijective (toMatching f hL d V c k) := by
  constructor
  · intro a b hab
    obtain ⟨z, _, hz⟩ := existsUnique_global f hL d V c k
      (toMatching f hL d V c k b).val (toMatching f hL d V c k b).property
    exact (hz a (fun T ↦ congrArg (fun w : matchingRing f hL d V c k ↦ w.val T) hab)).trans
      (hz b (fun _ ↦ rfl)).symm
  · intro z
    obtain ⟨a, ha, _⟩ := existsUnique_global f hL d V c k z.val z.property
    exact ⟨a, Subtype.ext (funext ha)⟩

/-- The actual ring of original global functions is the explicit localization equalizer. -/
def globalEquiv : Γ((Z).left, ⊤) ≃+* matchingRing f hL d V c k :=
  RingEquiv.ofBijective (toMatching f hL d V c k) (toMatching_bijective f hL d V c k)

/-- The original first endpoint as a multiplicative matching family. -/
def matchingSource : Γ(A.left, ⊤) →+* matchingRing f hL d V c k :=
  (toMatching f hL d V c k).comp (p).left.appTop.hom

/-- The original second endpoint as a multiplicative matching family. -/
def matchingTest : Γ(A.left, ⊤) →+* matchingRing f hL d V c k :=
  (toMatching f hL d V c k).comp (q).left.appTop.hom

/-- The first endpoint family consists of the actual localized source maps. -/
theorem matchingSource_apply (a : Γ(A.left, ⊤)) (T : TensorChart f hL d V c k) :
    (matchingSource f hL d V c k a).val T =
      localizedSourceMap f hL d V c k T.denominator T.domain T.image_eq a := rfl

/-- The second endpoint family is the literal localized first tensor factor. -/
theorem matchingTest_apply (a : Γ(A.left, ⊤)) (T : TensorChart f hL d V c k) :
    (matchingTest f hL d V c k a).val T =
      algebraMap _ (Localization.Away T.denominator) (a ⊗ₜ[R] (1 : Γ(V.left, ⊤))) :=
  localizedTestMap_eq_localization f hL d V c k T.denominator T.domain T.image_eq a

/-- Matching-family invariance is exactly equality of the full original endpoint pullbacks. -/
theorem matching_invariant_iff (a : Γ(A.left, ⊤)) :
    matchingSource f hL d V c k a = matchingTest f hL d V c k a ↔
      (p).left.appTop a = (q).left.appTop a :=
  (toMatching_bijective f hL d V c k).injective.eq_iff

end TensorChart
end FLT.Mazur.HilbertChart.AffineRestriction
