/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexCyclotomicTraceInvariant
public import FLT.PadicHodgeTheory.NormalizedTraceEquivariance

/-! # Full Galois equivariance of the bounded cyclotomic projections -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Every actual cyclotomic level is Galois over the original Q_p. -/
instance instIsGaloisPadicCyclotomicTower (n : ℕ) :
    IsGalois ℚ_[p] (padicCyclotomicTower p n) :=
  IsCyclotomicExtension.isGalois {p ^ n} ℚ_[p] (padicCyclotomicTower p n)

/-- The original algebraic projections commute with every original Galois automorphism. -/
theorem padicCyclotomicProjection_equivariant (n : ℕ) (σ : PadicGalois p) (x : PadicAlgCl p) :
    padicCyclotomicProjection p n (σ x) = σ (padicCyclotomicProjection p n x) := by
  let f := σ.restrictNormal (padicCyclotomicTower p n)
  have hc : (algebraMap (padicCyclotomicTower p n) (PadicAlgCl p)).comp f.toRingEquiv =
      σ.toRingHom.comp (algebraMap (padicCyclotomicTower p n) (PadicAlgCl p)) := by
    ext a
    exact σ.restrictNormal_commutes (padicCyclotomicTower p n) a
  have he := normalizedTrace_equivariant (padicCyclotomicTower p n) (PadicAlgCl p)
    f.toRingEquiv σ.toRingEquiv hc x
  rw [padicCyclotomicProjection_apply, padicCyclotomicProjection_apply]
  change (Algebra.normalizedTrace (padicCyclotomicTower p n) (PadicAlgCl p)
    (σ x) : PadicAlgCl p) = σ (Algebra.normalizedTrace _ _ x : padicCyclotomicTower p n)
  exact (congrArg Subtype.val he.symm).trans
    (AlgEquiv.restrictNormal_apply (padicCyclotomicTower p n) σ _)

/-- Every bounded extension is equivariant for the original completed action. -/
theorem complexCyclotomicProjection_equivariant (n : ℕ) (σ : PadicGalois p)
    (x : complexCyclotomicClosure p) :
    complexCyclotomicProjection p n (complexCyclotomicGalois p σ x) =
      complexGalois p σ (complexCyclotomicProjection p n x) := by
  refine (complexCyclotomicInclusion_dense p).induction_on x
    (isClosed_eq ((complexCyclotomicProjection p n).continuous.comp
      (complexCyclotomicGalois p σ).continuous)
      ((complexGalois_isometry p σ).continuous.comp
        (complexCyclotomicProjection p n).continuous)) ?_
  intro b
  rw [complexCyclotomicGalois_inclusion, complexCyclotomicProjection_inclusion,
    complexCyclotomicProjection_inclusion, complexGalois_coe,
    padicCyclotomicProjection_equivariant]

end PadicHodgeTheory
