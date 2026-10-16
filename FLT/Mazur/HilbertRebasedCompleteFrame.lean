/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFullRelationFiberRebase
public import FLT.Mazur.HilbertFullRelationOrderedPoints
public import FLT.Mazur.RelativeCompleteFrameComparison

/-!
# Complete frames transported along arbitrary original Hilbert arrows

Transport every coordinate through the isomorphism of the entire original
fibers. This constructs a complete ordered frame at the other independent
endpoint, preserving each original second endpoint and the coefficient map.
No completeness neighborhood or finite subrelation is assumed.
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
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "E" => fullRelationOverFirst f hL d V c k
variable {K : Type} [Field K]
  (a : Spec (.of K) ⟶ (relation f hL d V c k).left) (n : ℕ)
  (t : Over.mk (a ≫ (fst f hL d V c k).left) ⟶ fullRelationOrderedPoints f hL d V c k n)
local notation "φ" => fullRelationFiberRebase f hL d V c k a

/-- The transported coordinate remains a section of the whole original fiber. -/
def rebasedFrameSection (i : Fin n) :
    Spec (.of K) ⟶ Limits.pullback (p).left (a ≫ (q).left) :=
  geometricCoordinate E (Fin n) t i ≫ (φ).hom

omit [Etale V.hom] in
/-- The geometric test is unchanged by the transport. -/
@[reassoc] theorem rebasedFrameSection_test (i : Fin n) :
    rebasedFrameSection f hL d V c k a n t i ≫
      pullback.snd (p).left (a ≫ (q).left) = 𝟙 _ := by
  rw [rebasedFrameSection, Category.assoc, fullRelationFiberRebase_test]
  exact geometricCoordinate_snd E (Fin n) t i

/-- The rebased coordinate as an actual original relation arrow at the other endpoint. -/
def rebasedFrameCoordinate (i : Fin n) : Over.mk (a ≫ (q).left) ⟶ E :=
  Over.homMk (rebasedFrameSection f hL d V c k a n t i ≫
    pullback.fst (p).left (a ≫ (q).left)) (by
      change (_ ≫ _) ≫ (p).left = a ≫ (q).left
      rw [Category.assoc, pullback.condition, ← Category.assoc,
        rebasedFrameSection_test, Category.id_comp])

omit [Etale V.hom] in
/-- Each independent second endpoint is exactly the one of the original coordinate. -/
@[reassoc] theorem rebasedFrameCoordinate_second (i : Fin n) :
    (rebasedFrameCoordinate f hL d V c k a n t i).left ≫ (q).left =
      (t ≫ distinctCoordinate E (Fin n) i).left ≫ (q).left := by
  change (geometricCoordinate E (Fin n) t i ≫ (φ).hom ≫
    pullback.fst (p).left (a ≫ (q).left)) ≫ (q).left = _
  simp only [Category.assoc, fullRelationFiberRebase_second]
  rw [← Category.assoc]
  change (geometricCoordinate E (Fin n) t i ≫ pullback.fst (E).hom _) ≫ _ = _
  rw [geometricCoordinate_fst]

variable (ht : Function.Bijective (fun i ↦
  geometricCoordinate (fullRelationOverFirst f hL d V c k) (Fin n) t i default))

include ht in
omit [Etale V.hom] in
/-- Transport enumerates the whole new geometric fiber, including every original arrow. -/
theorem rebasedFrameSection_bijective :
    Function.Bijective (fun i ↦ rebasedFrameSection f hL d V c k a n t i default) :=
  (φ).hom.homeomorph.bijective.comp ht

include ht in
omit [Etale V.hom] in
/-- The transported original coordinates are distinct, as actual morphisms. -/
theorem rebasedFrameCoordinate_injective :
    Function.Injective (rebasedFrameCoordinate f hL d V c k a n t) := by
  intro i j hij
  apply (rebasedFrameSection_bijective f hL d V c k a n t ht).1
  apply congrArg (fun z : Spec (.of K) ⟶ Limits.pullback (p).left (a ≫ (q).left) ↦ z default)
  apply pullback.hom_ext
  · exact congrArg Over.Hom.left hij
  · rw [rebasedFrameSection_test, rebasedFrameSection_test]

/-- The complete ordered frame at the other independent original endpoint. -/
def rebasedCompleteFrame :
    Over.mk (a ≫ (q).left) ⟶ fullRelationOrderedPoints f hL d V c k n := by
  let _ : Subsingleton (Over.mk (a ≫ (q).left)).left :=
    inferInstanceAs (Subsingleton (Spec (.of K)))
  exact distinctLift E (Fin n) (rebasedFrameCoordinate f hL d V c k a n t)
    (rebasedFrameCoordinate_injective f hL d V c k a n t ht)

/-- Its geometric coordinate is the actual transported original section. -/
@[reassoc] theorem rebasedCompleteFrame_geometric (i : Fin n) :
    geometricCoordinate E (Fin n) (rebasedCompleteFrame f hL d V c k a n t ht) i =
      rebasedFrameSection f hL d V c k a n t i := by
  let _ : Subsingleton (Over.mk (a ≫ (q).left)).left :=
    inferInstanceAs (Subsingleton (Spec (.of K)))
  apply pullback.hom_ext
  · rw [geometricCoordinate_fst]
    exact congrArg Over.Hom.left (distinctLift_coordinate E (Fin n)
      (rebasedFrameCoordinate f hL d V c k a n t)
      (rebasedFrameCoordinate_injective f hL d V c k a n t ht) i)
  · rw [geometricCoordinate_snd]
    exact (rebasedFrameSection_test f hL d V c k a n t i).symm

/-- Completeness is proved at the new geometric endpoint for the entire original relation. -/
theorem rebasedCompleteFrame_complete :
    Function.Bijective (fun i ↦ geometricCoordinate E (Fin n)
      (rebasedCompleteFrame f hL d V c k a n t ht) i default) := by
  have h := rebasedFrameSection_bijective f hL d V c k a n t ht
  have hg (i : Fin n) := congrArg
    (fun z : Spec (.of K) ⟶ Limits.pullback (p).left (a ≫ (q).left) ↦ z default)
    (rebasedCompleteFrame_geometric f hL d V c k a n t ht i)
  constructor
  · intro i j hij
    exact h.1 ((hg i).symm.trans (hij.trans (hg j)))
  · intro x
    obtain ⟨i, hi⟩ := h.2 x
    exact ⟨i, (hg i).trans hi⟩

/-- Every full original arrow compares complete endpoint frames by one unique permutation. -/
theorem rebasedCompleteFrame_compare
    (t' : Over.mk (a ≫ (q).left) ⟶ fullRelationOrderedPoints f hL d V c k n)
    (ht' : Function.Bijective (fun i ↦ geometricCoordinate E (Fin n) t' i default)) :
    ∃! e : Equiv.Perm (Fin n),
      (rebasedCompleteFrame f hL d V c k a n t ht).left ≫
        (fullRelationOrderedAction f hL d V c k n e).hom = t'.left := by
  let z := rebasedCompleteFrame f hL d V c k a n t ht
  have hz := rebasedCompleteFrame_complete f hL d V c k a n t ht
  exact ⟨completeFrameRelabel E (Fin n) z hz t' ht',
    completeFrameRelabel_action E (Fin n) z hz t' ht',
    fun e he ↦ completeFrameRelabel_unique E (Fin n) z hz t' ht' e he⟩

end FLT.Mazur.HilbertChart.AffineRestriction
