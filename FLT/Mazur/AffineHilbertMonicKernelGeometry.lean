/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertMonicRelationGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Geometry of the full Picard relation inside the candidate kernel

The actual comparison is unramified and locally quasi-finite, by its composite
with either candidate endpoint. Over a locally Noetherian target change it is
locally finitely presented. None of these properties asserts kernel equality.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  {B : Over (Spec (.of R))} (u : B ⟶ A) {T : Scheme}
  (i : T ⟶ (finiteKernelModel f hL d V c k).left) [Mono i] (w : B.left ⟶ T)
  (h : IsPullback u.left w (finiteKernelProjection f hL d V c k).left i)
local notation "m" => monicModelRelationKernelMap f hL d V c k u i w h
local notation "p" => fst f hL d V c (u ≫ k)
local notation "q" => snd f hL d V c (u ≫ k)

/-- The comparison retains the first endpoint as an equality of scheme maps. -/
@[reassoc]
theorem monicModelRelationKernelMap_fst : m ≫ pullback.fst w w = (p).left :=
  pullback.lift_fst _ _ _

/-- The independent second endpoint is retained on every scheme test. -/
@[reassoc]
theorem monicModelRelationKernelMap_snd : m ≫ pullback.snd w w = (q).left :=
  pullback.lift_snd _ _ _

/-- The full relation comparison is unramified, without a flatness assumption on the model. -/
instance monicModelRelationKernelMap_formallyUnramified : FormallyUnramified m := by
  let _ := monicModelRelation_fst_etale f hL d V c k u i w h
  let _ : FormallyUnramified (m ≫ pullback.fst w w) := by
    rw [monicModelRelationKernelMap_fst]
    infer_instance
  exact FormallyUnramified.of_comp m (pullback.fst w w)

/-- Finite type is forced by the comparison's étale first endpoint. -/
instance monicModelRelationKernelMap_locallyOfFiniteType : LocallyOfFiniteType m := by
  let _ := monicModelRelation_fst_etale f hL d V c k u i w h
  let _ : LocallyOfFiniteType (m ≫ pullback.fst w w) := by
    rw [monicModelRelationKernelMap_fst]
    infer_instance
  exact locallyOfFiniteType_of_comp m (pullback.fst w w)

/-- The complete comparison has locally finite fibers, rather than only selected branches. -/
instance monicModelRelationKernelMap_locallyQuasiFinite : LocallyQuasiFinite m :=
  LocallyQuasiFinite.of_injective (m).injective

omit [Mono i] in
include h in
/-- The original source projection is still locally of finite presentation after base change. -/
theorem monicModelProjection_locallyOfFinitePresentation : LocallyOfFinitePresentation w :=
  MorphismProperty.of_isPullback h inferInstance

omit [Mono i] in
include h in
/-- A locally Noetherian target change gives a locally Noetherian entire source. -/
theorem monicModelSource_isLocallyNoetherian [IsLocallyNoetherian T] :
    IsLocallyNoetherian B.left := by
  let _ := monicModelProjection_locallyOfFinitePresentation f hL d V c k u i w h
  exact LocallyOfFiniteType.isLocallyNoetherian w

omit [Mono i] in
include h in
/-- The candidate kernel is locally Noetherian, without identifying it with the relation. -/
theorem monicModelKernel_isLocallyNoetherian [IsLocallyNoetherian T] :
    IsLocallyNoetherian (pullback w w) := by
  let _ := monicModelProjection_locallyOfFinitePresentation f hL d V c k u i w h
  let _ := monicModelSource_isLocallyNoetherian f hL d V c k u i w h
  exact LocallyOfFiniteType.isLocallyNoetherian (pullback.fst w w)

/-- The actual comparison is locally finitely presented over every Noetherian target change. -/
instance monicModelRelationKernelMap_locallyOfFinitePresentation [IsLocallyNoetherian T] :
    LocallyOfFinitePresentation m := by
  let _ := monicModelKernel_isLocallyNoetherian f hL d V c k u i w h
  infer_instance

end FLT.Mazur.HilbertChart.AffineRestriction
