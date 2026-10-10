/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFanRefinedRestrictionTargets
public import FLT.Mazur.PrincipalFanRestrictionUniqueness

/-!
# Full restriction path equations after simultaneous refinement

Restrictions out of refined overlap rings retain the old ambient equations.
Surjectivity of the ambient relation transition promotes those equations to
the full new ambient ring. The literal target comparison then gives the exact
path equations required by the fan isomorphism theorem.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

attribute [local irreducible] principalFanRefinedRestrictionEquiv

universe u v

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A] {ι : Type v}
  {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
  [∀ i, Algebra.FiniteType R (B i)]
  {a : ι → A} {b : ∀ i, B i}
  {f : ∀ i, Localization.Away (a i) →ₐ[R] Localization.Away (b i)}
  {x y : PrincipalFanStage a b f}

/-- A refinement commutes on the whole ambient quotient ring. -/
theorem principalFanAmbient_refinement (h : x ≤ y) (i : ι) :
    (principalFanAmbient y i).comp
      (FiniteRelationModel.transition R (relationIdeal R A) h.1) =
    (principalTransition (b i) (principalFan_target_mono h i)).comp
      (principalFanAmbient x i) := by
  apply AlgHom.ext
  intro z
  have he := AlgHom.congr_fun (principalFan_hom_comm h i)
    (algebraMap (Stage R A x.source) (PrincipalStage R A (a i) x.source) z)
  change y.hom i (FiniteRelationLocalization.transition R _ _ h.1 _) = _ at he
  rw [FiniteRelationLocalization.transition_algebraMap] at he
  exact he

/-- The literal double-open target indexed by the old fan and a later fan. -/
abbrev PrincipalFanOldRestrictionTarget (h : x ≤ y) (i j : ι) :=
  FiniteRelationIterated.Stage R (relationIdeal R (B j))
    (principalRepresentative R (B j) (b j)) (x.target j)
    (principalFanRestrictionDenominator x i j)
    ⟨y.target j, principalFan_target_mono h j⟩

/-- Turn an actual refined restriction into a map to the canonical new fan target. -/
def principalFanRefinedRestriction (h : x ≤ y) (i j : ι)
    (ρ : PrincipalStage R (B i) (b i) (y.target i) →ₐ[R]
      PrincipalFanOldRestrictionTarget h i j) :
    PrincipalStage R (B i) (b i) (y.target i) →ₐ[R]
      PrincipalFanRestrictionTarget y i j :=
  (principalFanRefinedRestrictionEquiv h i j).toAlgHom.comp ρ

/-- Cancel the surjective ambient transition before comparing localization targets. -/
theorem principalFanOldRestriction_path (h : x ≤ y) (i j : ι)
    (ρ : PrincipalStage R (B i) (b i) (y.target i) →ₐ[R]
      PrincipalFanOldRestrictionTarget h i j)
    (hρ : (ρ.comp (principalTransition (b i) (principalFan_target_mono h i))).comp
        (principalFanAmbient x i) =
      (Algebra.algHom R (PrincipalStage R (B j) (b j) (y.target j))
        (PrincipalFanOldRestrictionTarget h i j)).comp
        ((principalTransition (b j) (principalFan_target_mono h j)).comp
          (principalFanAmbient x j))) :
    ρ.comp (principalFanAmbient y i) =
      (Algebra.algHom R (PrincipalStage R (B j) (b j) (y.target j))
        (PrincipalFanOldRestrictionTarget h i j)).comp (principalFanAmbient y j) := by
  apply AlgHom.ext
  intro z
  obtain ⟨q, rfl⟩ := FiniteRelationModel.transition_surjective R (relationIdeal R A) h.1 z
  have hi := AlgHom.congr_fun (principalFanAmbient_refinement h i) q
  have hj := AlgHom.congr_fun (principalFanAmbient_refinement h j) q
  have he := AlgHom.congr_fun hρ q
  exact (congrArg ρ hi).trans (he.trans
    (congrArg (algebraMap _ (PrincipalFanOldRestrictionTarget h i j)) hj.symm))

/-- Old ambient equations imply full new ambient equations, with actual refined domains. -/
theorem principalFanRefinedRestriction_path (h : x ≤ y) (i j : ι)
    (ρ : PrincipalStage R (B i) (b i) (y.target i) →ₐ[R]
      PrincipalFanOldRestrictionTarget h i j)
    (hρ : (ρ.comp (principalTransition (b i) (principalFan_target_mono h i))).comp
        (principalFanAmbient x i) =
      (Algebra.algHom R (PrincipalStage R (B j) (b j) (y.target j))
        (PrincipalFanOldRestrictionTarget h i j)).comp
        ((principalTransition (b j) (principalFan_target_mono h j)).comp
          (principalFanAmbient x j))) :
    (principalFanRefinedRestriction h i j ρ).comp (principalFanAmbient y i) =
      (principalFanRestrictionInclusion y i j).comp (principalFanAmbient y j) := by
  have hp := principalFanOldRestriction_path h i j ρ hρ
  apply AlgHom.ext
  intro z
  have he := AlgHom.congr_fun hp z
  change ρ (principalFanAmbient y i z) = algebraMap _ _ (principalFanAmbient y j z) at he
  change principalFanRefinedRestrictionEquiv h i j (ρ (principalFanAmbient y i z)) = _
  rw [he, principalFanRefinedRestrictionEquiv_algebraMap]
  rfl

/-- The promoted full path equations have exactly the contract used for fan isomorphisms. -/
theorem principalFanRefinedRestriction_equations (h : x ≤ y)
    (ρ : ∀ i j, PrincipalStage R (B i) (b i) (y.target i) →ₐ[R]
      PrincipalFanOldRestrictionTarget h i j)
    (hρ : ∀ i j,
      ((ρ i j).comp (principalTransition (b i) (principalFan_target_mono h i))).comp
        (principalFanAmbient x i) =
      (Algebra.algHom R (PrincipalStage R (B j) (b j) (y.target j))
        (PrincipalFanOldRestrictionTarget h i j)).comp
        ((principalTransition (b j) (principalFan_target_mono h j)).comp
          (principalFanAmbient x j))) :
    PrincipalFanRestrictionEquations y
      (fun i j ↦ (principalFanRefinedRestriction h i j (ρ i j)).toRingHom) := by
  intro i j
  exact congrArg AlgHom.toRingHom (principalFanRefinedRestriction_path h i j (ρ i j) (hρ i j))

end FLT.Mazur.FiniteTypeRelationModel
