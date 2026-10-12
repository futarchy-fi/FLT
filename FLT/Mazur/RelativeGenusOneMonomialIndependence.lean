/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneAllPoleBasis

/-!
# Independence of all original relative monomial functions

Every finite initial segment is the faithful image of an actual original pole
basis. This proves independence over the base ring without a field hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
  relativePoleFunction

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅ structureModule S)

/-- The ordered sequence of original constant and higher monomial functions. -/
def relativePointOrderedFunction : ℕ → relativePoleComplementModule G.hom s.left
  | 0 => relativePoleFunction G.hom s.left hI 1 (relativePointOneBasis G hg s hI ())
  | m + 1 => relativePoleFunction G.hom s.left hI (m + 2)
      (relativePointHigherMonomial G hg s hI e m)

/-- The original basis at each pole bound retains the same ordered function sequence. -/
theorem relativePointAllPoleBasis_function (m : ℕ) (i : Fin (m + 1)) :
    relativePoleFunction G.hom s.left hI (m + 1)
      (relativePointAllPoleBasis G hg s hI e m i) =
        relativePointOrderedFunction G hg s hI e i := by
  induction m with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    rw [relativePointAllPoleBasis_zero]
    rfl
  | succ m ih =>
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [relativePointAllPoleBasis_last]
      rfl
    · rw [relativePointAllPoleBasis_old, relativePoleFunction_step]
      exact ih j

/-- Every positive initial segment is independent over the actual base section ring. -/
theorem relativePointOrderedFunction_initialIndependent (m : ℕ) :
    LinearIndependent Γ(S, ⊤)
      (fun i : Fin (m + 1) ↦ relativePointOrderedFunction G hg s hI e i) := by
  have h := (relativePointAllPoleBasis G hg s hI e m).linearIndependent.map'
    (relativePoleFunctionLinear G.hom s.left hI (m + 1))
    (LinearMap.ker_eq_bot.mpr (relativePoleFunction_injective G.hom s.left hI (m + 1)))
  change LinearIndependent Γ(S, ⊤) (fun i ↦
    (show relativePoleComplementModule G.hom s.left from
      relativePoleFunction G.hom s.left hI (m + 1)
        (relativePointAllPoleBasis G hg s hI e m i))) at h
  simpa only [relativePointAllPoleBasis_function] using h

/-- The entire original monomial sequence is independent over the base ring. -/
theorem relativePointOrderedFunction_independent :
    LinearIndependent Γ(S, ⊤) (relativePointOrderedFunction G hg s hI e) := by
  classical
  apply linearIndependent_iff_finset_linearIndependent.mpr
  intro t
  let j : t → Fin (t.sup id + 1) := fun i ↦
    ⟨i, Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)⟩
  exact (relativePointOrderedFunction_initialIndependent G hg s hI e (t.sup id)).comp j
    (fun i k hik ↦ Subtype.ext (congrArg Fin.val hik))

end FLT.Mazur.FCurve
