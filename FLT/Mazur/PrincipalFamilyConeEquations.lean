/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFamilyEquationStages
public import FLT.Mazur.PrincipalFamilyLimits

/-!
# Compatible cones throughout the family approximation

Prescribed cone equations are equations between actual coordinate composites
at every stage of a cofinal subsystem. Restricting to this subsystem preserves
the original chart and overlap rings as colimits.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : Type u} [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
  {a : ∀ i, A i} {b : B}
  {f : ∀ i, Localization.Away (a i) →ₐ[R] Localization.Away b}
  {κ : Type w} {C : κ → Type z} [∀ k, CommRing (C k)] [∀ k, Algebra R (C k)]
  (x : PrincipalFamilyStage a b f)

/-- The imposed equations are equalities of the actual refined coordinate composites. -/
theorem principalFamilyEquations_cone (l r : κ → ι)
    (p : ∀ k, C k →ₐ[R] PrincipalStage R (A (l k)) (a (l k)) (x.source (l k)))
    (q : ∀ k, C k →ₐ[R] PrincipalStage R (A (r k)) (a (r k)) (x.source (r k)))
    {y : PrincipalFamilyStage a b f}
    (hy : PrincipalFamilyEquations x (fun k ↦ (x.hom (l k)).comp (p k))
      (fun k ↦ (x.hom (r k)).comp (q k)) y) :
    ∃ hxy : x ≤ y, ∀ k,
      (y.hom (l k)).comp ((principalTransition (a (l k)) (hxy.choose (l k))).comp (p k)) =
        (y.hom (r k)).comp
          ((principalTransition (a (r k)) (hxy.choose (r k))).comp (q k)) := by
  obtain ⟨hxy, ht, he⟩ := hy
  refine ⟨hxy, fun k ↦ ?_⟩
  rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc,
    hxy.choose_spec.choose_spec, hxy.choose_spec.choose_spec,
    AlgHom.comp_assoc, AlgHom.comp_assoc]
  exact he k

variable [Finite ι] [Finite κ] [∀ k, Algebra.FiniteType R (C k)]
  (g h : ∀ k, C k →ₐ[R] PrincipalStage R B b x.target)
  (he : ∀ k, (principalStageMap R B b x.target).comp (g k) =
    (principalStageMap R B b x.target).comp (h k))

/-- Every original source ring remains the colimit after imposing the cone equations. -/
def principalFamilyEquationSourceIsColimit (i : ι) :
    IsColimit ((principalFamilySourceCocone a b f i).whisker
      (principalFamilyEquationIndex x g h)) := by
  let _ := principalFamilyEquationIndex_final x g h he
  exact (Functor.Final.isColimitWhiskerEquiv (principalFamilyEquationIndex x g h)
    (principalFamilySourceCocone a b f i)).symm (principalFamilySourceIsColimit a b f i)

/-- The overlap ring remains the colimit after imposing the cone equations. -/
def principalFamilyEquationTargetIsColimit :
    IsColimit ((principalFamilyTargetCocone a b f).whisker
      (principalFamilyEquationIndex x g h)) := by
  let _ := principalFamilyEquationIndex_final x g h he
  exact (Functor.Final.isColimitWhiskerEquiv (principalFamilyEquationIndex x g h)
    (principalFamilyTargetCocone a b f)).symm (principalFamilyTargetIsColimit a b f)

end FLT.Mazur.FiniteTypeRelationModel
