/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallySplitLineAtlasSection

/-!
# Choice independence of the actual atlas section

Every ambient frame gives the same local map into the glued dual atlas.
The global reverse map is also invariant under source isomorphisms commuting
with the inclusion, and hence under equality of actual ambient subobjects.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.LocallyFreeDualProjectiveAtlas
open FCurve AffineFreeSheafCoordinates FiniteFreeContragredient ProjectiveSpace
variable {X : Scheme.{u}} (M : X.Modules) (hM : LocallyFiniteFree M)

/-- An arbitrary actual frame maps into the atlas by its recovered dual coordinate change. -/
def chartMapOfFrame (i : AffineFiniteFreeAtlas.Index M) {ι : Type u} [Finite ι]
    (e : M.restrict i.val.ι ≅ SheafOfModules.free ι) :
    ProjectiveSpace.space Γ(i.val.toScheme, ⊤) ι ⟶ LocallyFreeDualProjectiveAtlas.space M hM :=
  (linearIso (map (coordinates i.val.toScheme
    (e.symm ≪≫ AffineFiniteFreeAtlas.chart M i)))).hom ≫ chartMap M hM i

end FLT.Mazur.LocallyFreeDualProjectiveAtlas

namespace FLT.Mazur.LocallySplitLineAtlasSection
open FCurve SplitLineAffineNeighborhood LocallySplitLineAmbientChart
variable {X : Scheme.{u}} {L N M : X.Modules} (s : L ⟶ M)
variable (hL : LocallyFreeRankOne L) (hs : LocallySplit s) (hM : LocallyFiniteFree M)

/-- Every actual ambient frame recovers the same restriction of the global section. -/
lemma ι_morphism_frame (i : AffineFiniteFreeAtlas.Index M) {ι : Type u} [Finite ι]
    (e : M.restrict i.val.ι ≅ SheafOfModules.free ι) :
    i.val.ι ≫ morphism s hL hs hM =
      point s hL hs i.val e ≫ LocallyFreeDualProjectiveAtlas.chartMapOfFrame M hM i e := by
  rw [ι_morphism, LocallyFreeDualProjectiveAtlas.chartMapOfFrame,
    ← Category.assoc, point_chartIso]
  rfl

/-- An actual isomorphism of line inclusions leaves the global atlas section unchanged. -/
lemma morphism_sourceIso (a : L ≅ N) (t : N ⟶ M) (h : a.hom ≫ t = s)
    (hN : LocallyFreeRankOne N) (ht : LocallySplit t) :
    morphism s hL hs hM = morphism t hN ht hM := by
  apply (AffineFiniteFreeAtlas.cover M hM).hom_ext
  intro i
  change i.val.ι ≫ morphism s hL hs hM = i.val.ι ≫ morphism t hN ht hM
  rw [ι_morphism, ι_morphism]
  apply congrArg (· ≫ LocallyFreeDualProjectiveAtlas.chartMap M hM i)
  apply SplitLineAffinePresentation.morphism_sourceIso
    ((restrictFunctor i.val.ι).mapIso a)
  simp only [inclusion, Functor.mapIso_hom, ← Category.assoc, ← Functor.map_comp, h]

/-- The reverse atlas section depends only on the actual line subobject of the ambient sheaf. -/
lemma morphism_subobject_eq [Mono s] (t : N ⟶ M) [Mono t]
    (h : Subobject.mk s = Subobject.mk t) (hN : LocallyFreeRankOne N) (ht : LocallySplit t) :
    morphism s hL hs hM = morphism t hN ht hM :=
  morphism_sourceIso s hL hs hM (Subobject.isoOfMkEqMk s t h) t
    (by simp) hN ht

end FLT.Mazur.LocallySplitLineAtlasSection
