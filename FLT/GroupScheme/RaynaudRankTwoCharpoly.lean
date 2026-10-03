/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudInvariantLineCharpoly

/-!
# Original rank-two finite-flat characteristic polynomials

The irreducible case uses the derived two-dimensional factor; the reducible
case constructs and combines the invariant line and quotient.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ThreeAdicPlan
open NumberField IsLocalRing RaynaudParameters

variable {K : Type} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (p : ℕ) [Fact p.Prime]
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ωv" => AlgebraicClosure Kv
local notation "I" => localInertiaGroup v
local notation "Rsh" => unramifiedUnion (Ω := Ωv) (p : O)
local notation "Lsh" => FractionRing Rsh
local notation "Av" => IntegralClosure O Ωv

/-- Retain the canonical fraction-ring base algebra in the completion-field tower. -/
local instance rankTwoCharpolyBaseAlgebra : Algebra O Lsh := inferInstance
variable [Algebra (v.adicCompletion K) (FractionRing (unramifiedUnion
    (Ω := AlgebraicClosure (v.adicCompletion K)) (p : v.adicCompletionIntegers K)))]
  [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K)
    (FractionRing (unramifiedUnion (Ω := AlgebraicClosure (v.adicCompletion K))
      (p : v.adicCompletionIntegers K)))]
  [HenselianLocalRing (v.adicCompletionIntegers K)]
  [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  (X : FF (v.adicCompletionIntegers K) (v.adicCompletion K))
  [Module (ZMod p) X.Points]
  (ρ : Representation (ZMod p) (localInertiaGroup v) X.Points)

/-- The geometric residue retains the original characteristic. -/
local instance rankTwoGeometricResidueCharP : CharP (ResidueField Av) p :=
  charP_of_injective_algebraMap
    (algebraMap (ResidueField O) (ResidueField Av)).injective p

set_option maxHeartbeats 1600000 in
-- The two original-factor cases share the explicit union and point type.
/-- Flat rank-two points have the ordinary or niveau-two binary charpoly. -/
theorem original_rank_two_charpoly (hp : Irreducible (p : O))
    (hρ : ρ.IsDiscreteContinuous) (hact : ∀ σ w, ρ σ w = σ • w)
    (hdim : Module.finrank (ZMod p) X.Points = 2)
    (e : Lsh →ₐ[Kv] Ωv) (he : ∀ a : Rsh, e (algebraMap Rsh Lsh a) = (a : Ωv))
    {α β : Ωv} (hn : 0 < p - 1) (hn2 : 0 < p * p - 1) (hp0 : (p : Kv) ≠ 0)
    (hα : α ^ (p - 1) = algebraMap Kv Ωv (p : Kv))
    (hβ : β ^ (p * p - 1) = algebraMap Kv Ωv (p : Kv)) :
    (∃ a b : ℕ, a ≤ 1 ∧ b ≤ 1 ∧ ∀ σ : I,
      (ρ σ).charpoly.map (ZMod.castHom (dvd_refl p) (ResidueField Av)) =
        (Polynomial.X - Polynomial.C
          ((LocalRoot.character v hn hp0 hα σ : ResidueField Av) ^ a)) *
        (Polynomial.X - Polynomial.C
          ((LocalRoot.character v hn hp0 hα σ : ResidueField Av) ^ b))) ∨
    (∃ a b : ℕ, a ≤ 1 ∧ b ≤ 1 ∧ ∀ σ : I,
      (ρ σ).charpoly.map (ZMod.castHom (dvd_refl p) (ResidueField Av)) =
        (Polynomial.X - Polynomial.C
          ((LocalRoot.character v hn2 hp0 hβ σ : ResidueField Av) ^ (p * a + b))) *
        (Polynomial.X - Polynomial.C
          (((LocalRoot.character v hn2 hp0 hβ σ : ResidueField Av) ^ (p * a + b)) ^ p))) := by
  classical
  by_cases hirr : ρ.IsIrreducible
  · let : ρ.IsIrreducible := hirr
    let : TopologicalSpace (Module.End (ZMod p) X.Points)ˣ := ⊥
    let : DiscreteTopology (Module.End (ZMod p) X.Points)ˣ := ⟨rfl⟩
    let idX : X.Points →+[I] X.Points :=
      { toAddMonoidHom := AddMonoidHom.id _
        map_smul' := fun _ _ ↦ rfl }
    exact Or.inr (original_two_factor_charpoly v p X ρ hp
      (ρ.continuous_toHomUnits_iff_discrete.mpr hρ) hact idX idX
      Function.injective_id Function.surjective_id hdim e he hn2 hp0 hβ)
  · exact Or.inl (original_reducible_charpoly v p X ρ hp hρ hact hdim hirr e he hn hp0 hα)

end ThreeAdicPlan
