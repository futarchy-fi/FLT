/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudOriginalFactorCharpoly
public import FLT.Deformations.RepresentationTheory.RankTwoSimpleFactors
public import FLT.GroupScheme.RaynaudRepresentationContinuity

/-!
# Original reducible rank-two finite-flat characteristic polynomials

Construct the simple invariant line and quotient, apply the actual original
factor weights, and multiply characteristic polynomials along their exact sequence.
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
local instance lineCharpolyBaseAlgebra : Algebra O Lsh := inferInstance
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
local instance geometricResidueCharP : CharP (ResidueField Av) p :=
  charP_of_injective_algebraMap
    (algebraMap (ResidueField O) (ResidueField Av)).injective p

set_option synthInstance.maxHeartbeats 100000 in
-- The two quotient representations require nested instance searches.
set_option maxHeartbeats 1600000 in
-- Apply the original scalar-factor theorems to two dependent quotient types.
/-- Reducible rank-two points have two derived binary-weight factors. -/
theorem original_reducible_charpoly (hp : Irreducible (p : O))
    (hρ : ρ.IsDiscreteContinuous) (hact : ∀ σ w, ρ σ w = σ • w)
    (hdim : Module.finrank (ZMod p) X.Points = 2) (hred : ¬ ρ.IsIrreducible)
    (e : Lsh →ₐ[Kv] Ωv) (he : ∀ a : Rsh, e (algebraMap Rsh Lsh a) = (a : Ωv))
    {α : Ωv} (hn : 0 < p - 1) (hp0 : (p : Kv) ≠ 0)
    (hα : α ^ (p - 1) = algebraMap Kv Ωv (p : Kv)) :
    ∃ a b : ℕ, a ≤ 1 ∧ b ≤ 1 ∧ ∀ σ : I,
      (ρ σ).charpoly.map (ZMod.castHom (dvd_refl p) (ResidueField Av)) =
        (Polynomial.X - Polynomial.C
          ((LocalRoot.character v hn hp0 hα σ : ResidueField Av) ^ a)) *
        (Polynomial.X - Polynomial.C
          ((LocalRoot.character v hn hp0 hα σ : ResidueField Av) ^ b)) := by
  obtain ⟨W, hW, hQ, hirrW, hirrQ⟩ := ρ.exists_rank_one_factors hdim hred
  let : Finite (X.Points ⧸ W.toSubmodule) :=
    Finite.of_surjective W.toSubmodule.mkQ W.toSubmodule.mkQ_surjective
  let ρQ := ρ.quotient W.toSubmodule W.apply_mem_toSubmodule
  let : W.toRepresentation.IsIrreducible := hirrW
  let : ρQ.IsIrreducible := hirrQ
  let : DistribMulAction I W.toSubmodule := DistribMulAction.compHom _ W.toRepresentation
  let : DistribMulAction I (X.Points ⧸ W.toSubmodule) := DistribMulAction.compHom _ ρQ
  let : TopologicalSpace (Module.End (ZMod p) W.toSubmodule)ˣ := ⊥
  let : DiscreteTopology (Module.End (ZMod p) W.toSubmodule)ˣ := ⟨rfl⟩
  let : TopologicalSpace (Module.End (ZMod p) (X.Points ⧸ W.toSubmodule))ˣ := ⊥
  let : DiscreteTopology (Module.End (ZMod p) (X.Points ⧸ W.toSubmodule))ˣ := ⟨rfl⟩
  let i : W.toSubmodule →+[I] X.Points :=
    { toAddMonoidHom := W.toSubmodule.subtype.toAddMonoidHom
      map_smul' := fun σ w ↦ hact σ w }
  let idW : W.toSubmodule →+[I] W.toSubmodule :=
    { toAddMonoidHom := AddMonoidHom.id _
      map_smul' := fun _ _ ↦ rfl }
  let idX : X.Points →+[I] X.Points :=
    { toAddMonoidHom := AddMonoidHom.id _
      map_smul' := fun _ _ ↦ rfl }
  let q : X.Points →+[I] (X.Points ⧸ W.toSubmodule) :=
    { toAddMonoidHom := W.toSubmodule.mkQ.toAddMonoidHom
      map_smul' := fun σ x ↦ congrArg W.toSubmodule.mkQ (hact σ x).symm }
  obtain ⟨a, ha, hfa⟩ := original_one_factor_charpoly v p X W.toRepresentation hp
    ((W.toRepresentation.continuous_toHomUnits_iff_discrete).mpr (hρ.subrepresentation ρ W))
    (fun _ _ ↦ rfl) i idW Subtype.val_injective Function.surjective_id hW e he hn hp0 hα
  obtain ⟨b, hb, hfb⟩ := original_one_factor_charpoly v p X ρQ hp
    ((ρQ.continuous_toHomUnits_iff_discrete).mpr (hρ.quotient ρ W))
    (fun _ _ ↦ rfl) idX q Function.injective_id W.toSubmodule.mkQ_surjective hQ e he hn hp0 hα
  refine ⟨a, b, ha, hb, fun σ ↦ ?_⟩
  rw [ρ.charpoly_subrepresentation_mul_quotient W σ, Polynomial.map_mul, hfa σ, hfb σ]

end ThreeAdicPlan
