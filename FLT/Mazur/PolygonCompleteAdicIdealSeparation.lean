/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealSheafFactorizationSupport
public import FLT.Mazur.IdealSheafAdicStalkSeparation
public import FLT.Mazur.CoherentIdealIntersection
public import FLT.Mazur.PolygonCompleteLineIsoDetection

/-!
# Full ideal separation on the complete polygon family

Krull intersection kills an infinitely deep ideal along the original closed
stage. Its coherent support is closed, so properness kills it everywhere.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve AnnihilatorSubsheaf FCurve.CoherentDevissage
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] originalStageToCompatibleProj exactVeroneseProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Every original zero-stage point belongs to the actual parameter-ideal support. -/
theorem originalZero_mem_adicSupport (x : (family K 0 n h).left) :
    originalStageToCompatibleProj K n h 0 x ∈ (compatibleProjAdicIdeal K n h).support := by
  exact idealSupport_mem_of_factorization
    (compatibleProjAdicIdeal K n h ^ (0 + 1)) (originalStageAdicIso K n h 0).hom
    (originalStageToCompatibleProj K n h 0) (originalStageAdicIso_hom_ι K n h 0) x

/-- The original adic stages jointly detect zero full ideals on the complete family. -/
theorem completeIdeal_eq_bot_of_le_powers (J : (exactVeroneseProj K n h).IdealSheafData)
    (hJ : ∀ m : ℕ, J ≤ compatibleProjAdicIdeal K n h ^ (m + 1)) : J = ⊥ := by
  let _ := CoherentIdealIntersection.idealModule_coherent J
  let U : (exactVeroneseProj K n h).Opens :=
    ⟨(support (idealModule J))ᶜ, (isClosed_support (idealModule J)).isOpen_compl⟩
  have hU : U = ⊤ := by
    apply completeOpen_eq_top_of_originalZero K n h
    apply top_unique
    intro x _
    change ¬ ¬ Limits.IsZero ((stalk (originalStageToCompatibleProj K n h 0 x)).obj
      (idealModule J))
    apply not_not.mpr
    exact idealModule_stalk_isZero_of_stalkIdeal_eq_bot J _
      (stalkIdeal_eq_bot_of_le_powers _ J hJ _ (originalZero_mem_adicSupport K n h x))
  apply idealSheaf_eq_of_stalkIdeal_eq
  intro x
  rw [stalkIdeal_bot]
  have hx : x ∈ U := by rw [hU]; trivial
  have hz : Limits.IsZero ((stalk x).obj (idealModule J)) := not_not.mp hx
  have hs := AddCommGrpCat.isZero_iff_subsingleton.mp hz
  apply bot_unique
  rintro _ ⟨v, rfl⟩
  change idealStalkInclusion J x v = 0
  rw [hs.elim v 0, map_zero]

end FLT.Mazur.PolygonInfinitesimalStages
