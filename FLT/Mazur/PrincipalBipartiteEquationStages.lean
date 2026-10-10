/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalBipartiteRelations
public import FLT.Mazur.PrincipalBipartiteLimits

/-!
# A shared incidence subsystem satisfying all overlap equations

Each overlap has finitely many equations from finite-type test algebras.
Their simultaneous solution stages form a cofinal subsystem of the incidence
index, preserving the shared source chart stages throughout.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z t s

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {E : κ → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {src : ∀ j, E j → ι} {a : ∀ i, A i} {b : ∀ j, B j}
  {f : ∀ j e, Localization.Away (a (src j e)) →ₐ[R] Localization.Away (b j)}
  {K : κ → Type t} {C : ∀ j, K j → Type s}
  [∀ j k, CommRing (C j k)] [∀ j k, Algebra R (C j k)]
  (x : PrincipalBipartiteStage src a b f)
  (g h : ∀ j k, C j k →ₐ[R] PrincipalStage R (B j) (b j) (x.target j))

/-- A refinement of `x` on which all prescribed equations hold. -/
def PrincipalBipartiteEquations (y : PrincipalBipartiteStage src a b f) : Prop :=
  x ≤ y ∧ ∃ ht : x.target ≤ y.target, ∀ j k,
    (principalTransition (b j) (ht j)).comp (g j k) =
      (principalTransition (b j) (ht j)).comp (h j k)

/-- Equations remain true under every commuting refinement. -/
theorem principalBipartiteEquations_mono {y z : PrincipalBipartiteStage src a b f}
    (hy : PrincipalBipartiteEquations x g h y) (hyz : y ≤ z) :
    PrincipalBipartiteEquations x g h z := by
  obtain ⟨hxy, ht, he⟩ := hy
  refine ⟨hxy.trans hyz, fun j ↦ (ht j).trans (principalBipartite_target_mono hyz j),
    fun j k ↦ ?_⟩
  calc
    (principalTransition (b j) ((ht j).trans (principalBipartite_target_mono hyz j))).comp (g j k) =
        (principalTransition (b j) (principalBipartite_target_mono hyz j)).comp
          ((principalTransition (b j) (ht j)).comp (g j k)) := by
      rw [← AlgHom.comp_assoc, principalTransition_comp]
    _ = (principalTransition (b j) (principalBipartite_target_mono hyz j)).comp
        ((principalTransition (b j) (ht j)).comp (h j k)) := by rw [he j k]
    _ = (principalTransition (b j)
        ((ht j).trans (principalBipartite_target_mono hyz j))).comp (h j k) := by
      rw [← AlgHom.comp_assoc, principalTransition_comp]

/-- The equations express commuting cones of actual incidence maps at the refined stage. -/
theorem principalBipartiteEquations_cone (l r : ∀ j, K j → E j)
    (p : ∀ j k, C j k →ₐ[R] PrincipalStage R (A (src j (l j k)))
      (a (src j (l j k))) (x.source (src j (l j k))))
    (q : ∀ j k, C j k →ₐ[R] PrincipalStage R (A (src j (r j k)))
      (a (src j (r j k))) (x.source (src j (r j k))))
    {y : PrincipalBipartiteStage src a b f}
    (hy : PrincipalBipartiteEquations x (fun j k ↦ (x.hom j (l j k)).comp (p j k))
      (fun j k ↦ (x.hom j (r j k)).comp (q j k)) y) :
    ∃ hxy : x ≤ y, ∀ j k,
      (y.hom j (l j k)).comp ((principalTransition (a (src j (l j k)))
        (hxy.1 (src j (l j k)))).comp (p j k)) =
      (y.hom j (r j k)).comp ((principalTransition (a (src j (r j k)))
        (hxy.1 (src j (r j k)))).comp (q j k)) := by
  obtain ⟨hxy, ht, he⟩ := hy
  refine ⟨hxy, fun j k ↦ ?_⟩
  rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc,
    principalBipartite_hom_comm hxy, principalBipartite_hom_comm hxy,
    AlgHom.comp_assoc, AlgHom.comp_assoc]
  exact he j k

/-- The subsystem cut out by finite equations, with its inherited refinement order. -/
def PrincipalBipartiteEquationStage :=
  {y : PrincipalBipartiteStage src a b f // PrincipalBipartiteEquations x g h y}

/-- Refinement on the equation subsystem is inherited from the family index. -/
instance principalBipartiteEquationStagePreorder :
    Preorder (PrincipalBipartiteEquationStage x g h) :=
  inferInstanceAs (Preorder {y // PrincipalBipartiteEquations x g h y})

/-- Forget the equations and retain the underlying simultaneous coordinate lift. -/
def principalBipartiteEquationIndex :
    PrincipalBipartiteEquationStage x g h ⥤ PrincipalBipartiteStage src a b f where
  obj y := y.val
  map e := homOfLE (leOfHom e)

variable [∀ j, Finite (K j)] [∀ j k, Algebra.FiniteType R (C j k)]

/-- Equations true in the original overlap ring hold at some finite refinement. -/
theorem exists_principalBipartiteEquations
    (he : ∀ j k, (principalStageMap R (B j) (b j) (x.target j)).comp (g j k) =
      (principalStageMap R (B j) (b j) (x.target j)).comp (h j k)) :
    ∃ y, PrincipalBipartiteEquations x g h y := by
  obtain ⟨t, ht, hcomm⟩ := exists_principalBipartite_target_equations x C g h he
  exact ⟨principalBipartiteTargetExtension x t ht,
    principalBipartiteTargetExtension_le x t ht, ht, hcomm⟩

variable [∀ j, Finite (E j)]

omit [∀ j, Finite (K j)] [∀ j k, Algebra.FiniteType R (C j k)] in
/-- Common family refinements preserve the chosen equations. -/
instance principalBipartiteEquationStageDirected :
    IsDirectedOrder (PrincipalBipartiteEquationStage x g h) where
  directed y z := by
    obtain ⟨t, hyt, hzt⟩ := exists_ge_ge y.val z.val
    exact ⟨⟨t, principalBipartiteEquations_mono x g h y.property hyt⟩, hyt, hzt⟩

/-- One can satisfy the equations beyond any preassigned family stage. -/
theorem exists_principalBipartiteEquations_above
    (he : ∀ j k, (principalStageMap R (B j) (b j) (x.target j)).comp (g j k) =
      (principalStageMap R (B j) (b j) (x.target j)).comp (h j k))
    (y : PrincipalBipartiteStage src a b f) :
    ∃ z, y ≤ z ∧ PrincipalBipartiteEquations x g h z := by
  obtain ⟨t, ht⟩ := exists_principalBipartiteEquations x g h he
  obtain ⟨z, hyz, htz⟩ := exists_ge_ge y t
  exact ⟨z, hyz, principalBipartiteEquations_mono x g h ht htz⟩

/-- Imposing the finite equations does not change any colimit on the family index. -/
theorem principalBipartiteEquationIndex_final
    (he : ∀ j k, (principalStageMap R (B j) (b j) (x.target j)).comp (g j k) =
      (principalStageMap R (B j) (b j) (x.target j)).comp (h j k)) :
    (principalBipartiteEquationIndex x g h).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro y
    obtain ⟨z, hyz, hz⟩ := exists_principalBipartiteEquations_above x g h he y
    exact ⟨⟨z, hz⟩, ⟨homOfLE hyz⟩⟩
  · intro y z j k
    exact ⟨z, 𝟙 z, Subsingleton.elim _ _⟩

variable (he : ∀ j k, (principalStageMap R (B j) (b j) (x.target j)).comp (g j k) =
  (principalStageMap R (B j) (b j) (x.target j)).comp (h j k))

/-- Imposing every overlap equation preserves the original source chart rings. -/
def principalBipartiteEquationSourceIsColimit (i : ι) :
    IsColimit ((principalBipartiteSourceCocone src a b f i).whisker
      (principalBipartiteEquationIndex x g h)) := by
  let _ := principalBipartiteEquationIndex_final x g h he
  exact (Functor.Final.isColimitWhiskerEquiv (principalBipartiteEquationIndex x g h)
    (principalBipartiteSourceCocone src a b f i)).symm
      (principalBipartiteSourceIsColimit src a b f i)

/-- Imposing every overlap equation preserves the original overlap rings. -/
def principalBipartiteEquationTargetIsColimit (j : κ) :
    IsColimit ((principalBipartiteTargetCocone src a b f j).whisker
      (principalBipartiteEquationIndex x g h)) := by
  let _ := principalBipartiteEquationIndex_final x g h he
  exact (Functor.Final.isColimitWhiskerEquiv (principalBipartiteEquationIndex x g h)
    (principalBipartiteTargetCocone src a b f j)).symm
      (principalBipartiteTargetIsColimit src a b f j)

/-- The source principal open is still the inverse limit after all overlap equations. -/
def principalBipartiteEquationSourceIsLimit (i : ι) :
    IsLimit (Scheme.Spec.mapCone ((principalBipartiteSourceCocone src a b f i).whisker
      (principalBipartiteEquationIndex x g h)).op) :=
  isLimitOfPreserves Scheme.Spec (principalBipartiteEquationSourceIsColimit x g h he i).op

/-- The overlap principal open is still the inverse limit after all overlap equations. -/
def principalBipartiteEquationTargetIsLimit (j : κ) :
    IsLimit (Scheme.Spec.mapCone ((principalBipartiteTargetCocone src a b f j).whisker
      (principalBipartiteEquationIndex x g h)).op) :=
  isLimitOfPreserves Scheme.Spec (principalBipartiteEquationTargetIsColimit x g h he j).op

end FLT.Mazur.FiniteTypeRelationModel
