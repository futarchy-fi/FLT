/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertLocalTensorInvariants

/-!
# An intersection-stable atlas of literal tensor localizations

The charts retain the original relation open and its exact envelope image.
Products of tensor denominators give exact intersections, so this atlas covers
all original arrows and has specified affine overlaps.
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
local instance atlasSourceAlgebra : Algebra R Γ(A.left, ⊤) :=
  affineBaseSectionAlgebra A.hom
/-- The algebra induced by the original translation structural morphism. -/
local instance atlasTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom


/-- A principal tensor chart of the actual full relation, with its exact envelope image. -/
structure TensorChart where
  /-- The actual tensor denominator. -/
  denominator : Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)
  /-- The original relation open. -/
  domain : (relation f hL d V c k).left.Opens
  /-- Its image is precisely the indicated principal open of the affine envelope. -/
  image_eq : (toEnvelope f hL d V c k).left ''ᵁ domain =
    (prod A V).left.basicOpen ((tensorIso A V).hom denominator)

namespace TensorChart
variable (T S : TensorChart f hL d V c k)

/-- The original chart is affine, by its constructed literal localization model. -/
theorem isAffine : IsAffineOpen T.domain := by
  let e := principalTensorIso f hL d V c k T.denominator T.domain T.image_eq
  exact IsAffine.of_isIso e.hom

/-- Coordinate sections of a chart are its literal tensor localization. -/
def sectionsIso : Γ(T.domain.toScheme, ⊤) ≅ CommRingCat.of (Localization.Away T.denominator) :=
  principalTensorSectionsIso f hL d V c k T.denominator T.domain T.image_eq

/-- Exact intersections correspond to products of the original tensor denominators. -/
theorem intersection_image : (toEnvelope f hL d V c k).left ''ᵁ (T.domain ⊓ S.domain) =
    (prod A V).left.basicOpen ((tensorIso A V).hom (T.denominator * S.denominator)) := by
  rw [map_mul, Scheme.basicOpen_mul, ← T.image_eq, ← S.image_eq]
  ext x
  constructor
  · rintro ⟨z, ⟨hzT, hzS⟩, rfl⟩
    exact ⟨⟨z, hzT, rfl⟩, ⟨z, hzS, rfl⟩⟩
  · rintro ⟨⟨z, hzT, hz⟩, ⟨w, hwS, hw⟩⟩
    have hzw := (toEnvelope f hL d V c k).left.injective (hz.trans hw.symm)
    subst w
    exact ⟨z, ⟨hzT, hwS⟩, hz⟩

/-- A specified chart for the full pairwise overlap. -/
def inter : TensorChart f hL d V c k where
  denominator := T.denominator * S.denominator
  domain := T.domain ⊓ S.domain
  image_eq := intersection_image f hL d V c k T S

/-- Every point has a principal tensor chart inside any prescribed original open. -/
theorem exists_mem (x : (Z).left) (W : (Z).left.Opens) (hx : x ∈ W) :
    ∃ T : TensorChart f hL d V c k, x ∈ T.domain ∧ T.domain ≤ W := by
  obtain ⟨t, U, _, hxU, hUW, hU⟩ := exists_point_tensor_chart f hL d V c k x W hx
  exact ⟨⟨t, U, hU⟩, hxU, hUW⟩

/-- The atlas covers the entire original relation, not merely a chosen collection of arrows. -/
theorem iSup_domain : (⨆ T : TensorChart f hL d V c k, T.domain) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨T, hx, _⟩ := exists_mem f hL d V c k x ⊤ trivial
  exact (le_iSup (fun S : TensorChart f hL d V c k ↦ S.domain) T) hx

end TensorChart
end FLT.Mazur.HilbertChart.AffineRestriction
