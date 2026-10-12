/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorPowerH1Vanishing
public import FLT.Mazur.GenusOneGroupPointCohomology

/-!
# Exact dimensions of all positive powers of the original point

The constructed vanishing for O(o) propagates through the actual divisor
sequence. Riemann–Roch then gives h⁰(O(mo)) = m for every positive m, including
pole orders two, three and six needed for Weierstrass coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) [GrpObj G] [IsIntegral G.left] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom]
  (hd : topologicalKrullDim G.left = 1) (hc : HasConstantGlobalSections G.hom)
  (hg : curveGenus G.hom hd hc = 1)
  (s : 𝟙_ (Over (Spec (.of k))) ⟶ G) (hI : EffectiveCartier s.left.ker)

include hg

/-- Every positive tensor power of the specified point line has vanishing H¹. -/
theorem genusOne_group_pointPower_h1 (m : ℕ) :
    Subsingleton (ModuleScalarH G.hom
      (tensorPower (divisorLineBundle s.left.ker hI) (m + 1)) 1) := by
  let _ : IsFinite (s.left.ker.subschemeι ≫ G.hom) := by
    rw [← sectionImageIso_hom G.hom s.left s.w]
    infer_instance
  let _ : Subsingleton (ModuleH (divisorLineBundle s.left.ker hI) 1) :=
    genusOne_group_point_h1 G hd hc hg s hI
  apply divisorPower_h1_subsingleton_of_first G.hom hI _ m
  exact moduleH_subsingleton_of_iso (ModuleSheafTensor.rightUnitor _) 1

/-- Its actual positive-pole section space has dimension exactly the pole bound. -/
theorem genusOne_group_pointPower_h0 (m : ℕ) (hm : 0 < m) :
    Module.finrank k (ModuleScalarH G.hom
      (tensorPower (divisorLineBundle s.left.ker hI) m) 0) = m := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  let _ := genusOne_group_pointPower_h1 G hd hc hg s hI a
  let _ : IsFinite (s.left.ker.subschemeι ≫ G.hom) := by
    rw [← sectionImageIso_hom G.hom s.left s.w]
    infer_instance
  have he := curve_h0_eq_of_h1_vanishing G.hom hd hc
    (tensorPower (divisorLineBundle s.left.ker hI) (a + 1))
  rw [curveSheafDegree_divisor_power, divisorFieldLength_section G.hom s.left s.w,
    hg, Nat.cast_one, mul_one] at he
  change Module.finrank k (ModuleScalarH G.hom
    (tensorPower (divisorLineBundle s.left.ker hI) (a + 1)) 0) = a + 1
  omega

/-- The same vanishing holds for the full scheme-theoretic power of the point ideal. -/
theorem genusOne_group_pointIdealPower_h1 (m : ℕ) :
    Subsingleton (ModuleScalarH G.hom
      (divisorLineBundle (s.left.ker ^ (m + 1)) (hI.pow (m + 1))) 1) := by
  let _ : Subsingleton
      (ModuleH (tensorPower (divisorLineBundle s.left.ker hI) (m + 1)) 1) :=
    genusOne_group_pointPower_h1 G hd hc hg s hI m
  exact moduleH_subsingleton_of_iso (divisorLineBundlePowerIso hI (m + 1)).symm 1

/-- The ideal-power sheaf keeps the same exact section dimension. -/
theorem genusOne_group_pointIdealPower_h0 (m : ℕ) (hm : 0 < m) :
    Module.finrank k (ModuleScalarH G.hom
      (divisorLineBundle (s.left.ker ^ m) (hI.pow m)) 0) = m := by
  let e := ((moduleScalarHFunctor G.hom 0).mapIso
    (divisorLineBundlePowerIso hI m)).toLinearEquiv
  exact e.finrank_eq.symm.trans (genusOne_group_pointPower_h0 G hd hc hg s hI m hm)

end FLT.Mazur.FCurve
