/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleLineLimitDescent
public import FLT.Mazur.ProperStageFiberProjection

/-!
# Descending the ample residue fiber of a specified proper-stage line

The proper fiber subsystem is a compact separated inverse system. Ampleness
of the original residue-fiber pullback therefore descends to a refinement,
with the resulting line still the pullback of the specified proper-stage line.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits (Cone IsLimit pullbackSymmetry)
open Scheme.Modules FLT.Mazur.FCurve

namespace FLT.Mazur.Approximation

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  {S : Scheme.{u}} {D : I ⥤ Scheme.{u}}
  (t : D ⟶ (Functor.const I).obj S) (i : I)
  (c : Cone D) (hc : IsLimit c) (b : c.pt ⟶ S)
  (hb : ∀ j, c.π.app j ≫ t.app j = b) (s : S)
  [∀ {j k} (f : j ⟶ k), IsClosedImmersion (D.map f)] [IsProper (t.app i)]

include hc hb in
/-- The chosen line has an ample residue fiber after a proper-stage refinement. -/
theorem exists_properStage_ample_fiber (L : (D.obj i).Modules)
    (hL : LocallyFreeRankOne L)
    (hA : AmpleLineBundle
      ((pullback (b.fiberι s)).obj ((pullback (c.π.app i)).obj L))) :
    ∃ j : Over i, AmpleLineBundle
      ((pullback ((t.app j.left).fiberι s)).obj ((pullback (D.map j.hom)).obj L)) := by
  let q := S.fromSpecResidueField s
  let F := properStageBaseChangeDiagram t q i
  let C := properStageResidueFiberCone t i c b hb s
  let a : Over i := Over.mk (𝟙 i)
  let p : F.obj a ⟶ D.obj i := Limits.pullback.snd q (t.app i)
  let M := (pullback p).obj L
  let _ (j : Over i) : CompactSpace (F.obj j) :=
    properStageBaseChangeDiagram_compactSpace t q i j
  let _ (j : Over i) : QuasiSeparatedSpace (F.obj j) :=
    properStageBaseChangeDiagram_quasiSeparatedSpace t q i j
  let _ {j k : Over i} (f : j ⟶ k) : IsAffineHom (F.map f) := by
    let _ : IsClosedImmersion (F.map f) := properStageBaseChangeDiagram_closed t q i f
    infer_instance
  let _ : (F.obj a).IsSeparated := properStageBaseChangeDiagram_isSeparated t i q a
  have hCa : C.π.app a ≫ p = b.fiberι s ≫ c.π.app i :=
    properStageResidueFiberCone_projection t i c b hb s a
  have hAM : AmpleLineBundle ((pullback (C.π.app a)).obj M) :=
    hA.of_iso ((pullbackComp (C.π.app a) p).app L ≪≫
      (pullbackCongr hCa).app L ≪≫ ((pullbackComp (b.fiberι s) (c.π.app i)).app L).symm)
  obtain ⟨j, f, hj⟩ := exists_ampleLineBundle_of_limit F C
    (properStageResidueFiberIsLimit t i c b hb s hc) a M (hL.pullback p) hAM
  have hfp : F.map f ≫ p = Limits.pullback.snd q (t.app j.left) ≫ D.map j.hom :=
    properStageBaseChangeDiagram_to_identity t i q j f
  have hB : AmpleLineBundle
      ((pullback (Limits.pullback.snd q (t.app j.left))).obj
        ((pullback (D.map j.hom)).obj L)) :=
    hj.of_iso ((pullbackComp (Limits.pullback.snd q (t.app j.left)) (D.map j.hom)).app L ≪≫
      (pullbackCongr hfp.symm).app L ≪≫ ((pullbackComp (F.map f) p).app L).symm)
  let e := pullbackSymmetry (t.app j.left) q
  have he : e.hom ≫ Limits.pullback.snd q (t.app j.left) = (t.app j.left).fiberι s :=
    Limits.pullbackSymmetry_hom_comp_snd _ _
  refine ⟨j, (hB.pullback_affine e.hom).of_iso ?_⟩
  exact (pullbackCongr he.symm).app ((pullback (D.map j.hom)).obj L) ≪≫
    ((pullbackComp e.hom (Limits.pullback.snd q (t.app j.left))).app
      ((pullback (D.map j.hom)).obj L)).symm

end FLT.Mazur.Approximation
