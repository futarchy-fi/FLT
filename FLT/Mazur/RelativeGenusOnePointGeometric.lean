/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GenusOneGroupPointAcyclic
public import FLT.Mazur.SectionPointPowerBaseChange
public import FLT.Mazur.GroupSectionBaseChange
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Actual geometric fibers of point powers in genus-one group families

The original point line is pulled to each geometric fiber and identified
with the retained point line there. Genus one gives acyclicity and the
exact dimension of sections, without a fixed-curve presentation of the family.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Scheme.Modules
open scoped CategoryTheory.Obj
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme} (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  {k : Type} [Field k] [IsAlgClosed k] (g : Spec (.of k) ⟶ S)

include hg

/-- The original positive point power is acyclic on every actual geometric fiber. -/
theorem relative_pointPower_geometric_acyclic (m : ℕ) (hm : 0 < m) (n : ℕ) :
    Subsingleton (ModuleH ((Scheme.Modules.pullback (pullback.fst G.hom g)).obj
      (tensorPower (divisorLineBundle s.left.ker hI) m)) (n + 1)) := by
  let H := (Over.pullback g).obj G
  let _ : IsProper H.hom := inferInstanceAs (IsProper (pullback.snd G.hom g))
  let _ : SmoothOfRelativeDimension 1 H.hom :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback G.hom g)
      (inferInstance : SmoothOfRelativeDimension 1 G.hom)
  let _ : IsIntegral H.left := GeometricallyIntegral.geometrically_isIntegral
    g _ _ (IsPullback.of_hasPullback G.hom g)
  let t := pullSection g s
  let hJ := sectionPoint_cartier_baseChange (IsPullback.of_hasPullback G.hom g)
    s.left t.left s.w t.w (section_fst g s) hI
  let e := sectionPointPowerIso (IsPullback.of_hasPullback G.hom g)
    s.left t.left s.w t.w (section_fst g s) hI hJ m
  have hf := hg.pullback g
  let _ : Subsingleton (ModuleH (tensorPower (divisorLineBundle t.left.ker hJ) m)
      (n + 1)) := genusOne_group_pointPower_acyclic H
    hf.toNodalFiberCore.topologicalKrullDim_eq_one hf.constantSections hf.genus_one t hJ m hm n
  exact moduleH_subsingleton_of_iso e (n + 1)

/-- The original fiber coefficient has exactly the expected number of sections. -/
theorem relative_pointPower_geometric_h0 (m : ℕ) (hm : 0 < m) :
    Module.finrank k (ModuleScalarH (pullback.snd G.hom g)
      ((Scheme.Modules.pullback (pullback.fst G.hom g)).obj
        (tensorPower (divisorLineBundle s.left.ker hI) m)) 0) = m := by
  let H := (Over.pullback g).obj G
  let _ : IsProper H.hom := inferInstanceAs (IsProper (pullback.snd G.hom g))
  let _ : SmoothOfRelativeDimension 1 H.hom :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback G.hom g)
      (inferInstance : SmoothOfRelativeDimension 1 G.hom)
  let _ : IsIntegral H.left := GeometricallyIntegral.geometrically_isIntegral
    g _ _ (IsPullback.of_hasPullback G.hom g)
  let t := pullSection g s
  let hJ := sectionPoint_cartier_baseChange (IsPullback.of_hasPullback G.hom g)
    s.left t.left s.w t.w (section_fst g s) hI
  let e := sectionPointPowerIso (IsPullback.of_hasPullback G.hom g)
    s.left t.left s.w t.w (section_fst g s) hI hJ m
  have hf := hg.pullback g
  exact ((moduleScalarHFunctor (pullback.snd G.hom g) 0).mapIso e).toLinearEquiv.finrank_eq.trans
    (genusOne_group_pointPower_h0 H hf.toNodalFiberCore.topologicalKrullDim_eq_one
      hf.constantSections hf.genus_one t hJ m hm)

end FLT.Mazur.FCurve
