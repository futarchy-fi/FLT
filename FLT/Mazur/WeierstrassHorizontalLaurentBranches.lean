/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationHorizontalSmooth
public import FLT.Mazur.PolygonNodeDifferenceBranches

/-!
# Both original Laurent branches cover the retained horizontal tensor open

The entire original horizontal localization is identified with the node
difference open by the proved divided-coordinate normalization. Both original
Laurent punctures survive this isomorphism and retain the coefficient map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped LaurentPolynomial TensorProduct
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
/-- Transport a whole localization along a proved equality of its original denominator. -/
irreducible_def horizontalLocalizationCongr {S C : Type u} [CommRing S] [CommRing C]
    [Algebra S C] {x y : C} (h : x = y) :
    Localization.Away x ≃ₐ[S] Localization.Away y := by
  subst y
  exact AlgEquiv.refl

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ depth) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6) (hp : 2 * k < depth)
local notation "F" => ResidueField R
local notation "B" => HorizontalCoordinate W (π ^ k) b3 b4 b6
local notation "a" => (residueTangentUnit D)⁻¹
local notation "d" => algebraMap F (PolygonNodeEqualizer.A (R := F)) ((a : Fˣ) : F) *
  (PolygonNodeLocalization.y - PolygonNodeLocalization.x)

/-- The whole retained tensor ring is the actual scaled-difference localization. -/
def residueHorizontalDifferenceEquiv : F ⊗[R] B ≃ₐ[F] Localization.Away d :=
  (residueHorizontalEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hp).trans
    (horizontalLocalizationCongr (S := F)
      (residuePolygonEquiv_x D k hk0 hk b3 b4 b6 h3 h4 h6 hp))

/-- The complete retained horizontal open in the original tensor spectrum. -/
def residueHorizontalDifferenceIso :
    Spec (.of (Localization.Away d)) ≅ Spec (.of (F ⊗[R] B)) :=
  Scheme.Spec.mapIso (residueHorizontalDifferenceEquiv D k hk0 hk
    b3 b4 b6 h3 h4 h6 hp).toRingEquiv.toCommRingCatIso.op
local notation "E" => residueHorizontalDifferenceIso D k hk0 hk b3 b4 b6 h3 h4 h6 hp

/-- The original negative puncture in the full retained tensor open. -/
def residueHorizontalLeft : Spec (.of F[T;T⁻¹]) ⟶ Spec (.of (F ⊗[R] B)) :=
  PolygonNodeDifferenceBranches.left a ≫ (E).hom

/-- The original positive puncture in the full retained tensor open. -/
def residueHorizontalRight : Spec (.of F[T;T⁻¹]) ⟶ Spec (.of (F ⊗[R] B)) :=
  PolygonNodeDifferenceBranches.right a ≫ (E).hom

instance residueHorizontalLeft_isOpenImmersion :
    IsOpenImmersion (residueHorizontalLeft D k hk0 hk b3 b4 b6 h3 h4 h6 hp) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

instance residueHorizontalRight_isOpenImmersion :
    IsOpenImmersion (residueHorizontalRight D k hk0 hk b3 b4 b6 h3 h4 h6 hp) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The horizontal normalization retains the actual residue coefficient map. -/
@[reassoc] theorem residueHorizontalDifferenceIso_structure :
    (E).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap F (F ⊗[R] B))) =
      Spec.map (CommRingCat.ofHom (algebraMap F (Localization.Away d))) :=
  algebraSpecIso_structure _

/-- The negative puncture retains the original residue coefficient map. -/
@[reassoc] theorem residueHorizontalLeft_structure :
    residueHorizontalLeft D k hk0 hk b3 b4 b6 h3 h4 h6 hp ≫
        Spec.map (CommRingCat.ofHom (algebraMap F (F ⊗[R] B))) =
      (MultiplicativeGroupScheme.gm F).hom := by
  rw [residueHorizontalLeft, Category.assoc, residueHorizontalDifferenceIso_structure,
    PolygonNodeDifferenceBranches.left_structure]

/-- The positive puncture retains the original residue coefficient map. -/
@[reassoc] theorem residueHorizontalRight_structure :
    residueHorizontalRight D k hk0 hk b3 b4 b6 h3 h4 h6 hp ≫
        Spec.map (CommRingCat.ofHom (algebraMap F (F ⊗[R] B))) =
      (MultiplicativeGroupScheme.gm F).hom := by
  rw [residueHorizontalRight, Category.assoc, residueHorizontalDifferenceIso_structure,
    PolygonNodeDifferenceBranches.right_structure]

/-- Both original punctures cover every point of the entire horizontal tensor open. -/
theorem residueHorizontalBranches_cover (z : Spec (.of (F ⊗[R] B))) :
    z ∈ Set.range (residueHorizontalLeft D k hk0 hk b3 b4 b6 h3 h4 h6 hp) ∨
      z ∈ Set.range (residueHorizontalRight D k hk0 hk b3 b4 b6 h3 h4 h6 hp) := by
  have hz := PolygonNodeDifferenceBranches.branches_cover a ((E).inv z)
  have he : (E).hom ((E).inv z) = z := congrArg (fun f => f z) (E).inv_hom_id
  rcases hz with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact Or.inl ⟨t, (congrArg (fun x => (E).hom x) ht).trans he⟩
  · exact Or.inr ⟨t, (congrArg (fun x => (E).hom x) ht).trans he⟩

end FLT.Mazur.WeierstrassDilatation
