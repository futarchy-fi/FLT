/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SplitLineProjectiveNaturality
public import FLT.Mazur.LocallySplitSheafTransport

/-!
# Source invariance of the canonical reverse map

An actual isomorphism between source lines preserves the canonical global
projective point. The proof compares the original inclusions after pullback
on the constructed affine framed split cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SplitSheafLinePullback
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} {L N : Y.Modules}

/-- Canonical free pullback preserves an actual source isomorphism square. -/
lemma inclusion_sourceIso (a : L ≅ N) (s : L ⟶ SheafOfModules.free ι)
    (t : N ⟶ SheafOfModules.free ι) (h : a.hom ≫ t = s) :
    ((pullback f).mapIso a).hom ≫ inclusion f t = inclusion f s := by
  simp only [inclusion, Functor.mapIso_hom, ← Category.assoc, ← Functor.map_comp, h]

end FLT.Mazur.SplitSheafLinePullback

namespace FLT.Mazur.SplitLineAffinePresentation
open FCurve SplitLineAffineNeighborhood ProjectiveSpace AffineSplitLineCoordinates
variable {X : Scheme.{u}} {ι : Type u} [Finite ι] {L N : X.Modules}
variable (a : L ≅ N) (s : L ⟶ SheafOfModules.free ι)
variable (t : N ⟶ SheafOfModules.free ι) (h : a.hom ≫ t = s)
variable (hL : LocallyFreeRankOne L) (hN : LocallyFreeRankOne N)
variable (hs : LocallySplit s) (ht : LocallySplit t)

include h in
/-- Isomorphic original line inclusions have the same canonical global reverse point. -/
lemma morphism_sourceIso : morphism s hL hs = morphism t hN ht := by
  let P := ofLocal s hL hs
  apply P.cover.hom_ext
  intro i
  let f := P.cover.f i
  let b := (pullback f).mapIso a
  let d := b.symm ≪≫ P.frame i
  let q := P.retraction i ≫ b.hom
  have hi : b.hom ≫ SplitSheafLinePullback.inclusion f t =
      SplitSheafLinePullback.inclusion f s :=
    SplitSheafLinePullback.inclusion_sourceIso f a s t h
  have hq : SplitSheafLinePullback.inclusion f t ≫ q = 𝟙 _ := by
    apply (cancel_epi b.hom).mp
    dsimp only [q]
    rw [← Category.assoc, ← Category.assoc, hi, P.split i,
      Category.id_comp, Category.comp_id]
  rw [morphism_affine_test s hL hs f (P.frame i) (P.retraction i) (P.split i),
    morphism_affine_test t hN ht f d q hq]
  exact congrArg (· ≫ coefficientMap f.appTop.hom ι)
    (projectivePoint_sourceIso b (P.frame i) d _ _ _ _ (P.split i) hq hi)

end FLT.Mazur.SplitLineAffinePresentation
