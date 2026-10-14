/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertNestedRestriction

/-!
# Full nested Picard kernels in original scheme coordinates

The nested relation isomorphism preserves both independent endpoints.
Consequently a kernel calculation on the actual double restriction transfers
to the freshly recomputed Picard relation of the newly selected chart.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  {B : Over (Spec (.of R))} (v : B ⟶ A)
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

/-- The nested scheme isomorphism keeps the first endpoint literally. -/
@[reassoc]
theorem nestedSchemeDoubleIso_fst : (nestedSchemeDoubleIso f hL d V c k v).hom ≫
    SchemeRelationRestriction.fst (p).left (q).left v.left =
      (fst f hL d V c (v ≫ k)).left := by
  dsimp only [nestedSchemeDoubleIso, Iso.trans_hom, Functor.mapIso_hom,
    SchemeRelationRestriction.overDoubleIso]
  rw [Category.assoc, SchemeRelationRestriction.overToDouble_fst]
  change (nestedToFullDouble f hL d V c k v ≫ nestedFullDoubleFst f hL d V c k v).left = _
  rw [nestedToFullDouble_fst]

/-- The second endpoint is retained independently, including on nonreduced tests. -/
@[reassoc]
theorem nestedSchemeDoubleIso_snd : (nestedSchemeDoubleIso f hL d V c k v).hom ≫
    SchemeRelationRestriction.snd (p).left (q).left v.left =
      (snd f hL d V c (v ≫ k)).left := by
  dsimp only [nestedSchemeDoubleIso, Iso.trans_hom, Functor.mapIso_hom,
    SchemeRelationRestriction.overDoubleIso]
  rw [Category.assoc, SchemeRelationRestriction.overToDouble_snd]
  change (nestedToFullDouble f hL d V c k v ≫ nestedFullDoubleSnd f hL d V c k v).left = _
  rw [nestedToFullDouble_snd]

/-- A full original double-restriction kernel gives the recomputed Picard relation kernel. -/
theorem nested_isPullback {T : Scheme} (w : B.left ⟶ T)
    (H : IsPullback (SchemeRelationRestriction.fst (p).left (q).left v.left)
      (SchemeRelationRestriction.snd (p).left (q).left v.left) w w) :
    IsPullback (fst f hL d V c (v ≫ k)).left (snd f hL d V c (v ≫ k)).left w w :=
  H.of_iso' (nestedSchemeDoubleIso f hL d V c k v) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (by simpa using nestedSchemeDoubleIso_fst f hL d V c k v)
    (by simpa using nestedSchemeDoubleIso_snd f hL d V c k v) (by simp) (by simp)

end FLT.Mazur.HilbertChart.AffineRestriction
