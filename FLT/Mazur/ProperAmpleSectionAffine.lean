/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperAmpleRetainedProjIso
public import FLT.Mazur.SectionRetainedProjOpens
public import FLT.Mazur.TensorPowerGeneratorOpen

/-!
# Affineness of every ample section open on a proper scheme

The original retained section-ring Proj isomorphism identifies every positive
section open with its affine homogeneous basic open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback SectionGradedSum
open SectionRetainedChartComparison SectionRetainedProjConstruction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] {L : X.Modules}
include f

/-- Every positive-power section of an ample line on a proper scheme has affine open. -/
theorem AmpleLineBundle.isAffineOpen_powerSection (hA : AmpleLineBundle L)
    (m : ℕ) (hm : 0 < m) (t : Γ(tensorPower L m, ⊤)) :
    IsAffineOpen (sectionGeneratorOpen (tensorPower L m) t) := by
  let _ : Fact (LocallyFreeRankOne L) := ⟨hA.2.1⟩
  let _ := RetainedSubringGrading.gradedRing (grade L ⊤) 1 (by decide)
  let h := positivePowerGenerated_of_ample L 1 hA (by decide)
  let _ := ProperAmpleRetainedProjIso.isIso f L 1 hA (by decide) h
  have H (t' : Γ(tensorPower L (1 * m), ⊤)) :
      IsAffineOpen (sectionGeneratorOpen (tensorPower L (1 * m)) t') := by
    have ha := (Proj.isAffineOpen_basicOpen
      (RetainedSubringGrading.grade (grade L ⊤) 1) (insertion L 1 m t')
      (insertion_mem L 1 m t') hm).preimage (toProj L 1 h)
    rwa [SectionRetainedProjOpens.toProj_preimage_basicOpen L 1 h t' hm] at ha
  rw [Nat.one_mul] at H
  exact H t

/-- Every section of the original ample line itself has an affine generator open. -/
theorem AmpleLineBundle.isAffineOpen_section (hA : AmpleLineBundle L) (t : Γ(L, ⊤)) :
    IsAffineOpen (sectionGeneratorOpen L t) := by
  have ha := hA.isAffineOpen_powerSection f 1 (by decide) (tensorPowerSection L ⊤ t 1)
  rwa [tensorPowerSection_generatorOpen hA.2.1 t (by decide : 0 < 1)] at ha

end FLT.Mazur.FCurve
