/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexThetaQuotientComparison

/-! # Compatible coefficient topologies on the actual finite de Rham levels -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The coefficient topology on the actual finite level of the de Rham completion. -/
scoped instance complexFiniteThetaQuotientTopology (n : ℕ) :
    TopologicalSpace (ComplexFiniteThetaQuotient p n) :=
  TopologicalSpace.induced (complexFiniteThetaQuotientEquiv p n) inferInstance

/-- The canonical algebraic identification also identifies the coefficient topologies. -/
def complexFiniteThetaQuotientHomeomorph (n : ℕ) :
    ComplexFiniteThetaQuotient p n ≃ₜ ComplexThetaQuotientInvertP p n :=
  (complexFiniteThetaQuotientEquiv p n).toEquiv.toHomeomorphOfIsInducing ⟨rfl⟩

/-- The actual finite coefficient topology is Hausdorff. -/
scoped instance complexFiniteThetaQuotient_t2Space (n : ℕ) :
    T2Space (ComplexFiniteThetaQuotient p n) :=
  (complexFiniteThetaQuotientHomeomorph p n).symm.t2Space

/-- All ring operations are continuous in the transported coefficient topology. -/
scoped instance complexFiniteThetaQuotient_isTopologicalRing (n : ℕ) :
    IsTopologicalRing (ComplexFiniteThetaQuotient p n) := by
  let e := complexFiniteThetaQuotientEquiv p n
  have hi : Topology.IsInducing e := ⟨rfl⟩
  let := hi.isTopologicalAddGroup e.toAddMonoidHom
  let := hi.continuousMul e.toMonoidHom
  exact { }

/-- Localized integral reductions commute with the actual finite transitions. -/
theorem complexThetaQuotientLocalizationMap_transition {m n : ℕ} (h : n ≤ m)
    (a : ComplexAinfInvertP p) :
    complexThetaQuotientInvertPTransition p h (complexThetaQuotientLocalizationMap p m a) =
      complexThetaQuotientLocalizationMap p n a := by
  have he : (complexThetaQuotientInvertPTransition p h).comp
      (complexThetaQuotientLocalizationMap p m) = complexThetaQuotientLocalizationMap p n := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : Ainf p))
    ext x
    simp only [RingHom.comp_apply, complexThetaQuotientLocalizationMap_algebraMap,
      complexThetaQuotientInvertPTransition_algebraMap, Ideal.Quotient.factor_mk]
  exact RingHom.congr_fun he a

/-- The canonical finite-level equivalences commute with quotient transitions. -/
theorem complexFiniteThetaQuotientEquiv_transition {m n : ℕ} (h : n ≤ m)
    (x : ComplexFiniteThetaQuotient p m) :
    complexFiniteThetaQuotientEquiv p n
      (Ideal.Quotient.factorPow (RingHom.ker (complexThetaInvertP p)) h x) =
        complexThetaQuotientInvertPTransition p h (complexFiniteThetaQuotientEquiv p m x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simpa only [Ideal.Quotient.factor_mk, complexFiniteThetaQuotientEquiv_mk] using
    (complexThetaQuotientLocalizationMap_transition p h a).symm

/-- The existing finite de Rham quotient transitions are continuous in coefficient topology. -/
theorem complexFiniteThetaQuotient_transition_continuous {m n : ℕ} (h : n ≤ m) :
    Continuous (Ideal.Quotient.factorPow (RingHom.ker (complexThetaInvertP p)) h) := by
  apply (complexFiniteThetaQuotientHomeomorph p n).isInducing.continuous_iff.mpr
  have he : complexFiniteThetaQuotientHomeomorph p n ∘
      Ideal.Quotient.factorPow (RingHom.ker (complexThetaInvertP p)) h =
        complexThetaQuotientInvertPTransition p h ∘ complexFiniteThetaQuotientHomeomorph p m :=
    funext fun x ↦ complexFiniteThetaQuotientEquiv_transition p h x
  rw [he]
  exact (complexThetaQuotientInvertPTransition_continuous p h).comp
    (complexFiniteThetaQuotientHomeomorph p m).continuous

end PadicHodgeTheory
