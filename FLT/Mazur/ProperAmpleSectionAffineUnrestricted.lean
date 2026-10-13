/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionRetainedProjOfAmple
public import FLT.Mazur.SectionRetainedProjStructuralMap
public import FLT.Mazur.TensorPowerGeneratorOpen
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Ample section opens on a proper scheme over an arbitrary affine base

The canonical retained Proj map is an open immersion by ampleness. Its
compatibility with the original structure map makes it proper, hence a
closed immersion. Its exact section-open preimages are therefore affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback SectionGradedSum
open SectionRetainedChartComparison SectionRetainedProjConstruction
open SectionRetainedProjStructuralMap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X S : Scheme} [IsAffine S] (f : X ⟶ S) [IsProper f]
  {L : X.Modules}

include f in
/-- A positive section of an ample line has affine generator open over any affine base. -/
theorem AmpleLineBundle.isAffineOpen_powerSection_unrestricted (hA : AmpleLineBundle L)
    (m : ℕ) (hm : 0 < m) (t : Γ(tensorPower L m, ⊤)) :
    IsAffineOpen (sectionGeneratorOpen (tensorPower L m) t) := by
  let _ : Fact (LocallyFreeRankOne L) := ⟨hA.2.1⟩
  let _ := RetainedSubringGrading.gradedRing (grade L ⊤) 1 (by decide)
  let h := positivePowerGenerated_of_ample L 1 hA (by decide)
  let _ := SectionRetainedProjOfAmple.isOpenImmersion L 1 (by decide) hA h
  let _ : IsSeparated (toBase L 1 f) := by
    unfold toBase toSpecFunctions
    infer_instance
  let _ : IsProper (toProj L 1 h ≫ toBase L 1 f) := by
    rw [toProj_toBase]
    infer_instance
  let _ := IsProper.of_comp (toProj L 1 h) (toBase L 1 f)
  let _ := IsClosedImmersion.of_isPreimmersion (toProj L 1 h)
    (toProj L 1 h).isClosedMap.isClosed_range
  have H (t' : Γ(tensorPower L (1 * m), ⊤)) :
      IsAffineOpen (sectionGeneratorOpen (tensorPower L (1 * m)) t') := by
    have ha := (Proj.isAffineOpen_basicOpen
      (RetainedSubringGrading.grade (grade L ⊤) 1) (insertion L 1 m t')
      (insertion_mem L 1 m t') hm).preimage (toProj L 1 h)
    rwa [SectionRetainedProjOpens.toProj_preimage_basicOpen L 1 h t' hm] at ha
  rw [Nat.one_mul] at H
  exact H t

include f in
/-- The original ample line itself has affine section opens without Noetherian hypotheses. -/
theorem AmpleLineBundle.isAffineOpen_section_unrestricted (hA : AmpleLineBundle L)
    (t : Γ(L, ⊤)) : IsAffineOpen (sectionGeneratorOpen L t) := by
  have ha := hA.isAffineOpen_powerSection_unrestricted f 1 (by decide)
    (tensorPowerSection L ⊤ t 1)
  rwa [tensorPowerSection_generatorOpen hA.2.1 t (by decide : 0 < 1)] at ha

end FLT.Mazur.FCurve
