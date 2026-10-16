/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertRebasedCompleteFrame

/-!
# Complete frame size is constant along the full original relation

Two arbitrary complete geometric frames at the independent endpoints of an
original arrow have equal size. This is proved from the whole-fiber isomorphism,
without assuming a globally constant rank or an open completeness locus.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  {K : Type} [Field K] (a : Spec (.of K) ⟶ (relation f hL d V c k).left)
  (n m : ℕ)
  (t : Over.mk (a ≫ (fst f hL d V c k).left) ⟶ fullRelationOrderedPoints f hL d V c k n)
  (t' : Over.mk (a ≫ (snd f hL d V c k).left) ⟶ fullRelationOrderedPoints f hL d V c k m)
local notation "E" => fullRelationOverFirst f hL d V c k

omit [Etale V.hom] in
/-- The entire original fibers force equal complete-frame sizes at related geometric endpoints. -/
theorem fullRelation_completeFrame_cardinality
    (ht : Function.Bijective (fun i ↦ geometricCoordinate E (Fin n) t i default))
    (ht' : Function.Bijective (fun i ↦ geometricCoordinate E (Fin m) t' i default)) : n = m := by
  let en := Equiv.ofBijective _ ht
  let em := Equiv.ofBijective _ ht'
  let er := (fullRelationFiberRebase f hL d V c k a).hom.homeomorph.toEquiv
  let e : Fin n ≃ Fin m := (en.trans er).trans em.symm
  simpa only [Fintype.card_fin] using Fintype.card_congr e

end FLT.Mazur.HilbertChart.AffineRestriction
