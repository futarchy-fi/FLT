/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperGlobalSectionFinite
public import FLT.Mazur.SchemeRelativeNilpotentSections

/-!
# The finite infinitesimal kernel over a Noetherian affine base

The section-evaluation kernel is nilpotent as an ideal, not merely elementwise
nil. Quotienting by this actual kernel recovers the original base functions.
This gives a finite infinitesimal obstruction; it does not assert its vanishing.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeRelativeNilpotentKernel
open SchemeRelativeNilpotentSections
variable {R : CommRingCat.{0}} [IsNoetherianRing R] {X : Scheme.{0}}
  (f : X ⟶ Spec R) (s : Spec R ⟶ X) (hs : s ≫ f = 𝟙 _)
  [IsProper f] [GeometricallyConnected f] [GeometricallyReduced f]

include f hs in
/-- Proper finiteness turns the section-evaluation nil ideal into a nilpotent ideal. -/
lemma evaluation_ker_isNilpotent : IsNilpotent (RingHom.ker s.appTop.hom) := by
  let _ : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  exact ProperGlobalSectionFinite.isNilpotent_of_le_nilradical f _
    (evaluation_ker_le_nilradical f s hs)

include hs in
/-- One exponent kills every product of evaluation-zero functions. -/
lemma exists_evaluation_ker_pow_eq_bot :
    ∃ n : ℕ, (RingHom.ker s.appTop.hom) ^ n = ⊥ :=
  evaluation_ker_isNilpotent f s hs

omit [IsNoetherianRing R] [IsProper f] [GeometricallyConnected f]
    [GeometricallyReduced f] in
/-- The actual quotient by the evaluation kernel identifies with the actual base functions. -/
def evaluationQuotientEquiv :
    Γ(X, ⊤) ⧸ RingHom.ker s.appTop.hom ≃+* Γ(Spec R, ⊤) :=
  s.appTop.hom.quotientKerEquivOfSurjective
    (fun a ↦ ⟨f.appTop a, evaluation_pullback f s hs a⟩)

omit [IsNoetherianRing R] [IsProper f] [GeometricallyConnected f]
    [GeometricallyReduced f] in
/-- The quotient equivalence is the original evaluation on representatives. -/
lemma evaluationQuotientEquiv_mk (a : Γ(X, ⊤)) :
    evaluationQuotientEquiv f s hs (Ideal.Quotient.mk _ a) = s.appTop a := rfl

omit [IsNoetherianRing R] [IsProper f] [GeometricallyConnected f]
    [GeometricallyReduced f] in
/-- Its inverse is the class of the original structural pullback. -/
lemma evaluationQuotientEquiv_symm (a : Γ(Spec R, ⊤)) :
    (evaluationQuotientEquiv f s hs).symm a = Ideal.Quotient.mk _ (f.appTop a) := by
  apply (evaluationQuotientEquiv f s hs).injective
  rw [RingEquiv.apply_symm_apply, evaluationQuotientEquiv_mk,
    evaluation_pullback f s hs]

end FLT.Mazur.SchemeRelativeNilpotentKernel
