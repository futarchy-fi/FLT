/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFaithfulAffineNeighborhood

/-!
# Actual affine test covers with constructed faithful translation neighborhoods

The degree and translation chart vary with the original test point. Each
member is an affine open in the original full intersection, and its translation
coordinate lies over a constructed faithful principal base neighborhood.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertFaithfulTestCover
open HilbertChart CartierAbel SchemePicard FCurve AffineEtaleFaithfulNeighborhood
open OrderedHilbertAffineEtaleTestCover
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))
local notation "E" => fun x ↦ Sigma.fst (Sigma.snd (chartData f hL T s x))
local notation "I" => fun x ↦ intersection f hL T s x

/-- A chosen point in the original full intersection above an original test point. -/
def overlapPoint (x : T.left) : (I x).left := (chartData_spec f hL T s x).2.2.choose

/-- The point remains over precisely the original test point. -/
theorem overlapPoint_toTest (x : T.left) :
    (toTest f hL T s x).left (overlapPoint f hL T s x) = x :=
  (chartData_spec f hL T s x).2.2.choose_spec

/-- The original translation morphism of this full intersection. -/
def coordinate (x : T.left) : I x ⟶ E x :=
  faithfulOverlapCoordinate f hL (chartData f hL T s x).1.2 (E x)
    (chartClass f hL T s x) T s

/-- The affine neighborhood and its actual maps, constructed above each original test point. -/
def data (x : T.left) : Σ v : (E x).left, Σ A : Scheme,
    Σ _j : A ⟶ (I x).left, Σ _β : A ⟶ (sourceOpen (E x).hom v).toScheme, A :=
  let h := exists_faithful_affine_overlap_neighborhood f hL (chartData f hL T s x).1.2
    (E x) (chartClass f hL T s x) T s (overlapPoint f hL T s x)
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩

/-- Every selected map retains the original point, translation coordinate and base equation. -/
theorem data_spec (x : T.left) :
    IsAffine (data f hL T s x).2.1 ∧ IsOpenImmersion (data f hL T s x).2.2.1 ∧
      (data f hL T s x).2.2.1 (data f hL T s x).2.2.2.2 = overlapPoint f hL T s x ∧
      (data f hL T s x).2.2.2.1 ≫ (sourceOpen (E x).hom (data f hL T s x).1).ι =
        (data f hL T s x).2.2.1 ≫ (coordinate f hL T s x).left ∧
      ((data f hL T s x).2.2.2.1 ≫ spectrumMap (E x).hom (data f hL T s x).1) ≫
        spectrumBase (E x).hom (data f hL T s x).1 = (data f hL T s x).2.2.1 ≫ (I x).hom := by
  let h := exists_faithful_affine_overlap_neighborhood f hL (chartData f hL T s x).1.2
    (E x) (chartClass f hL T s x) T s (overlapPoint f hL T s x)
  exact h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

instance data_affine (x : T.left) : IsAffine (data f hL T s x).2.1 :=
  (data_spec f hL T s x).1

instance data_openImmersion (x : T.left) : IsOpenImmersion (data f hL T s x).2.2.1 :=
  (data_spec f hL T s x).2.1

/-- The cover arrow is the actual inclusion followed by the original test projection. -/
def arrow (x : T.left) : (data f hL T s x).2.1 ⟶ T.left :=
  (data f hL T s x).2.2.1 ≫ (toTest f hL T s x).left

instance arrow_etale (x : T.left) : Etale (arrow f hL T s x) := by
  unfold arrow
  infer_instance

/-- Every original test point survives the constructed affine and faithful-base refinements. -/
theorem point_covers (x : T.left) :
    arrow f hL T s x (data f hL T s x).2.2.2.2 = x := by
  change (toTest f hL T s x).left
    ((data f hL T s x).2.2.1 (data f hL T s x).2.2.2.2) = x
  rw [(data_spec f hL T s x).2.2.1, overlapPoint_toTest]

/-- An actual small affine étale cover using the varying original ordered charts. -/
def cover : Scheme.Cover.{0} Scheme.etalePrecoverage T.left :=
  Scheme.Cover.mkOfCovers (P := @Etale) T.left (fun x ↦ (data f hL T s x).2.1)
    (arrow f hL T s) (fun x ↦ ⟨x, (data f hL T s x).2.2.2.2, point_covers f hL T s x⟩)
    (fun _ ↦ inferInstance)

/-- The same constructed affine arrows cover the original test in the fppf topology. -/
def fppfCover : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left :=
  Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) T.left
    (fun x ↦ (data f hL T s x).2.1) (arrow f hL T s)
    (fun x ↦ ⟨x, (data f hL T s x).2.2.2.2, point_covers f hL T s x⟩)
    (fun _ ↦ ⟨inferInstance, inferInstance⟩)

end FLT.Mazur.OrderedHilbertFaithfulTestCover
