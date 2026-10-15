/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryRelationNilpotence
public import FLT.Mazur.HilbertBoundaryEtaleLift

/-!
# Infinitesimal lifting of every original relation arrow

An entire lower-order relation arrow lifts uniquely after a choice of a higher
first endpoint. Its independent second endpoint and original Picard equality
are retained. Arbitrary nonaffine tests are allowed. This does not assert that
arbitrary prescribed deformations of both endpoints remain equivalent.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "B" n:max => originalThickenedSource f hL d V c k n
local notation "i" n:max => originalThickenedSourceMap f hL d V c k n
local notation "C" n:max => originalThickenedRelation f hL d V c k n
local notation "r" n:max => originalThickenedFst f hL d V c k n
local notation "s" n:max => originalThickenedSnd f hL d V c k n
local notation "z" n:max => originalThickenedArrow f hL d V c k n
local notation "j" h:max => originalThickenedTransition f hL d V c k h
local notation "t" h:max => originalThickenedRelationTransition f hL d V c k h

attribute [local irreducible] originalThickenedSource originalThickenedRelation
  originalThickenedSourceMap originalThickenedFst originalThickenedSnd originalThickenedArrow
  originalThickenedTransition originalThickenedRelationTransition

variable {T₀ T : Over (Spec (.of R))} (e : T₀ ⟶ T)
  [IsClosedImmersion e.left] (he : IsNilpotent e.left.ker)
  {m n : ℕ} (h : m ≤ n)
  (a : T₀ ⟶ originalThickenedRelation f hL d V c k m)
  (x : T ⟶ originalThickenedSource f hL d V c k n)
  (hx : e ≫ x = (a ≫ originalThickenedFst f hL d V c k m) ≫
    originalThickenedTransition f hL d V c k h)

omit [IsAffine A.left] in
include he hx in
/-- Every whole original arrow extends uniquely with its chosen first endpoint. -/
theorem originalThickenedArrow_etale_lift :
    ∃! b : T ⟶ C n, e ≫ b = a ≫ t h ∧ b ≫ r n = x := by
  apply EtaleNilpotentOverLift.existsUnique_lift e he (r n) (a ≫ t h) x
  rw [Category.assoc, originalThickenedRelationTransition_fst, ← Category.assoc, hx]

/-- The canonical higher-order whole arrow over the unchanged coefficient scheme. -/
def originalThickenedInfinitesimalArrow : T ⟶ C n :=
  (originalThickenedArrow_etale_lift f hL d V c k e he h a x hx).choose

local notation "β" => originalThickenedInfinitesimalArrow f hL d V c k e he h a x hx

omit [IsAffine A.left] in
/-- The complete original lower-order arrow is retained. -/
@[reassoc]
theorem originalThickenedInfinitesimalArrow_restrict : e ≫ β = a ≫ t h :=
  (originalThickenedArrow_etale_lift f hL d V c k e he h a x hx).choose_spec.1.1

omit [IsAffine A.left] in
/-- The higher-order first endpoint is exactly the prescribed one. -/
@[reassoc]
theorem originalThickenedInfinitesimalArrow_fst : β ≫ r n = x :=
  (originalThickenedArrow_etale_lift f hL d V c k e he h a x hx).choose_spec.1.2

/-- The independent second endpoint restricts to the original lower-order endpoint. -/
@[reassoc]
theorem originalThickenedInfinitesimalArrow_snd_restrict :
    e ≫ (β ≫ s n) = (a ≫ s m) ≫ j h := by
  rw [← Category.assoc, originalThickenedInfinitesimalArrow_restrict,
    Category.assoc, originalThickenedRelationTransition_snd, Category.assoc]

omit [IsAffine A.left] in
/-- Restricting the lifted original arrow recovers the original independent relation map. -/
@[reassoc]
theorem originalThickenedInfinitesimalArrow_original :
    e ≫ (β ≫ z n) = a ≫ z m := by
  rw [← Category.assoc, originalThickenedInfinitesimalArrow_restrict,
    Category.assoc, originalThickenedRelationTransition_arrow]

/-- The chosen endpoint and constructed second endpoint have the same original Picard class. -/
theorem originalThickenedInfinitesimalArrow_class :
    (relativeFppfSheaf f).obj.map x.op (originalThickenedSection f hL d V c k n) =
      (relativeFppfSheaf f).obj.map (β ≫ s n).op
        (originalThickenedSection f hL d V c k n) := by
  simpa only [originalThickenedInfinitesimalArrow_fst] using
    originalThickened_class_natural f hL d V c k n β

omit [IsAffine A.left] in
/-- The first original Hilbert parameter is retained as a whole morphism. -/
@[reassoc]
theorem originalThickenedInfinitesimalArrow_parameter :
    β ≫ (r n ≫ i n ≫ k) = x ≫ i n ≫ k := by
  rw [originalThickenedInfinitesimalArrow_fst_assoc]

omit [IsAffine A.left] in
/-- A different constructed lift with these data is the identical whole scheme arrow. -/
theorem originalThickenedInfinitesimalArrow_eq (β' : T ⟶ C n)
    (ha : e ≫ β' = a ≫ t h) (hx' : β' ≫ r n = x) : β = β' :=
  ((originalThickenedArrow_etale_lift f hL d V c k e he h a x hx).choose_spec.2
    β' ⟨ha, hx'⟩).symm

omit he hx in
/-- The independent second endpoint can instead be prescribed, without affine test hypotheses. -/
theorem originalThickenedArrow_etale_lift_second (he : IsNilpotent e.left.ker)
    (hx : e ≫ x = (a ≫ s m) ≫ j h) :
    ∃! b : T ⟶ C n, e ≫ b = a ≫ t h ∧ b ≫ s n = x := by
  apply EtaleNilpotentOverLift.existsUnique_lift e he (s n) (a ≫ t h) x
  rw [Category.assoc, originalThickenedRelationTransition_snd, ← Category.assoc, hx]

end FLT.Mazur.HilbertChart.AffineRestriction
