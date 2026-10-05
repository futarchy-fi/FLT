/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalEtaleSystemProjection

/-! # The quotient-system packaging retains the original nonsplit extension

The finite-level extension is the previously constructed extension, including
its torsor equivalences. The Tate identification retains both original maps
and the original Galois action; it does not choose a section.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.PDivisibleSystem
variable {p height : ℕ} [Fact p.Prime]
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- Each system level uses the same extension, with the same torsors and no splitting choice. -/
abbrev rationalConnectedEtaleLevelExtension (n : ℕ) :
    ModelExtension (X.rationalConnectedSystem.level n) (X.level n)
      (X.rationalEtaleSystem.level n) :=
  (X.level n).rationalConnectedEtaleExtension

/-- The level extension retains the connected system's actual embedding. -/
theorem rationalConnectedEtaleLevelExtension_inclusion (n : ℕ) :
    (X.rationalConnectedEtaleLevelExtension n).inclusion =
      X.rationalConnectedSystemInclusion.app n := rfl

/-- The level extension retains the quotient system's actual projection. -/
theorem rationalConnectedEtaleLevelExtension_quotient (n : ℕ) :
    (X.rationalConnectedEtaleLevelExtension n).quotient =
      X.rationalEtaleSystemProjection.app n := rfl

/-- The quotient Tate identification commutes with the original Galois action. -/
theorem rationalEtaleTateEquiv_galois (g : Field.absoluteGaloisGroup K)
    (x : X.rationalEtaleSystem.tateSequences) :
    X.rationalEtaleTateEquiv (g • x) = g • X.rationalEtaleTateEquiv x := rfl

/-- The system-level quotient Tate map retains the original Galois equivariance. -/
theorem rationalEtaleSystemProjection_tateMap_galois (g : Field.absoluteGaloisGroup K)
    (x : X.tateSequences) :
    X.rationalEtaleSystemProjection.tateMap (g • x) =
      g • X.rationalEtaleSystemProjection.tateMap x := by
  apply X.rationalEtaleTateEquiv.injective
  exact X.rationalEtaleTateProjection_galois g x

/-- The original connected and quotient Tate maps compose to zero after system packaging. -/
theorem rationalConnectedEtale_tate_composition :
    X.rationalEtaleSystemProjection.tateMap.comp X.rationalConnectedTateInclusion = 0 := by
  apply LinearMap.ext
  intro a
  have h : X.rationalConnectedTateInclusion a ∈ X.rationalConnectedTateInclusion.range :=
    ⟨a, rfl⟩
  rw [← X.rationalEtaleSystemProjection_tateMap_exact] at h
  exact h
end ThreeAdicPlan.PDivisibleSystem
