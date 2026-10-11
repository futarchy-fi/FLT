/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricAcyclicRankOne
public import FLT.Mazur.RelativePicardFppfCover

/-!
# The geometric acyclic rank-one Picard subfunctor on all test schemes

This is a subfunctor of the actual relative Picard presheaf. Its values
allow all line bundles on each varying total space, and all test schemes.
No section, Noetherianity, or chosen divisor is part of the definition.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X S : Scheme.{0}} (f : X ⟶ S)

/-- Relative classes whose actual representatives have acyclic rank-one residue fibers. -/
def RelativeGeometricAcyclicRankOne (c : RelativePic f) : Prop :=
  ∃ (L : X.Modules) (hL : LocallyFreeRankOne L),
    relativeClass f (mk L hL) = c ∧ GeometricAcyclicRankOne f L

/-- Every line representative detects this intrinsic relative-class condition. -/
theorem relativeGeometricAcyclicRankOne_mk (L : X.Modules) (hL : LocallyFreeRankOne L) :
    RelativeGeometricAcyclicRankOne f (relativeClass f (mk L hL)) ↔
      GeometricAcyclicRankOne f L := by
  constructor
  · rintro ⟨M, hM, hc, hA⟩
    exact (geometricAcyclicRankOne_relativeClass_iff f hM hL hc).mp hA
  · intro hA
    exact ⟨L, hL, rfl, hA⟩

/-- The condition pulls back along all cartesian maps of proper families. -/
theorem relativeGeometricAcyclicRankOne_map [IsProper f]
    {P T : Scheme.{0}} {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S}
    (h : IsPullback p q f g) {c : RelativePic f} (hc : RelativeGeometricAcyclicRankOne f c) :
    RelativeGeometricAcyclicRankOne q (relativeMap q f p g h.w.symm c) := by
  obtain ⟨L, hL, rfl, hA⟩ := hc
  exact ⟨(Scheme.Modules.pullback p).obj L, hL.pullback p, rfl,
    geometricAcyclicRankOne_baseChange f h L hL hA⟩

/-- The geometric acyclic rank-one locus inside the relative Picard presheaf on all tests. -/
def geometricAcyclicPicardSubfunctor [IsProper f] :
    Subfunctor (relativePresheaf f ⋙ forget CommGrpCat) where
  obj T := {c | RelativeGeometricAcyclicRankOne (Limits.pullback.snd f T.unop.hom) c}
  map a _ hc := relativeGeometricAcyclicRankOne_map _
    (relativeTotalMap_isPullback f a.unop) hc

/-- Membership uses the independently varying line bundle on the actual test total space. -/
lemma geometricAcyclicPicardSubfunctor_mem [IsProper f] (T : Over S)
    (L : (Limits.pullback f T.hom).Modules) (hL : LocallyFreeRankOne L) :
    relativeClass (Limits.pullback.snd f T.hom) (mk L hL) ∈
      (geometricAcyclicPicardSubfunctor f).obj (Opposite.op T) ↔
        GeometricAcyclicRankOne (Limits.pullback.snd f T.hom) L :=
  relativeGeometricAcyclicRankOne_mk _ L hL

end FLT.Mazur.CartierAbel
