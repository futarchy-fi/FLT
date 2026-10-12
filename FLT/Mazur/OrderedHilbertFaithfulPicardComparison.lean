/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertFaithfulBaseComparison

/-!
# Original Picard classes on the localized proper curve

The explicit test comparison and fixed-base sheaf comparison give a group
isomorphism on the actual retained affine tests. Thus equal-class equations
are preserved and reflected, including the original translated Hilbert class.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertFaithfulTestCover
open HilbertChart CartierAbel SchemePicard FCurve AffineEtaleFaithfulNeighborhood
open OrderedHilbertAffineEtaleTestCover
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))
local notation "D" => fun x ↦ data f hL T s x
local notation "E" => fun x ↦ Sigma.fst (Sigma.snd (chartData f hL T s x))
local notation "b" => fun x ↦ spectrumBase
  (Over.hom (Sigma.fst (Sigma.snd (chartData f hL T s x))))
    (Sigma.fst (data f hL T s x))
local notation "q" => fun x ↦ FaithfulNeighborhoodCurve.map f
  (Over.hom (Sigma.fst (Sigma.snd (chartData f hL T s x))))
    (Sigma.fst (data f hL T s x))

/-- The original test's Picard group is exactly that of the localized proper curve. -/
def localPicardIso (x : T.left) :
    (relativeFppfSheaf f).obj.obj (op (test f hL T s x)) ≅
      (relativeFppfSheaf (q x)).obj.obj (op (localTest f hL T s x)) :=
  (relativeFppfSheaf f).obj.mapIso (originalTestIso f hL T s x).op ≪≫
    ((sheafToPresheaf _ _).mapIso (relativeFppfBaseChange f (b x))).app
      (op (localTest f hL T s x))

/-- The original section on the actual affine cover, now on the localized proper curve. -/
def localSection (x : T.left) :
    (relativeFppfSheaf (q x)).obj.obj (op (localTest f hL T s x)) :=
  (localPicardIso f hL T s x).hom
    ((relativeFppfSheaf f).obj.map (testArrow f hL T s x).op s)

/-- Equal-class equations are reflected as well as preserved by the concrete comparison. -/
theorem localPicardIso_eq_iff (x : T.left)
    (a c : (relativeFppfSheaf f).obj.obj (op (test f hL T s x))) :
    (localPicardIso f hL T s x).hom a = (localPicardIso f hL T s x).hom c ↔ a = c := by
  constructor
  · intro h
    have h' := congrArg (fun z ↦ (localPicardIso f hL T s x).inv z) h
    simpa only [← ConcreteCategory.comp_apply, Iso.hom_inv_id,
      ConcreteCategory.id_apply] using h'
  · exact congrArg _

/-- The retained ORIGINAL Hilbert class becomes the original section of the local curve. -/
theorem localSection_original_chart (x : T.left) :
    (localPicardIso f hL T s x).hom
      (variableHilbertPoint f (chartData f hL T s x).1.2 hL (E x)
        (chartClass f hL T s x) (test f hL T s x) (toOriginalChart f hL T s x)) =
      localSection f hL T s x := by
  rw [original_class]
  rfl

end FLT.Mazur.OrderedHilbertFaithfulTestCover
