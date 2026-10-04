/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PolynomialCoefficientKernel
public import FLT.GroupScheme.LiftedQuotientReduction
public import Mathlib.RingTheory.Extension.Presentation.Basic

/-! # Lifted equations with their exact original reduction map

This constructs the quotient of lifted equations and identifies its reduction kernel.
The quotient has not been proved flat; regular-presentation theory is still needed.
-/

@[expose] public noncomputable section
namespace Algebra.Presentation
open MvPolynomial
variable {B C E ι σ : Type*} [CommRing B] [CommRing C] [CommRing E] [Algebra C E]
  (q : B →+* C) (P : Presentation C E ι σ)
  (g : σ → MvPolynomial ι B) (hg : ∀ i, MvPolynomial.map q (g i) = P.relation i)

/-- Lifted equations map to zero in the original presented algebra. -/
def liftedRelationMap : (MvPolynomial ι B ⧸ Ideal.span (Set.range g)) →+* E :=
  Ideal.Quotient.lift _ ((aeval P.val).toRingHom.comp (MvPolynomial.map q)) (by
    change Ideal.span (Set.range g) ≤ RingHom.ker _
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change aeval P.val (MvPolynomial.map q (g i)) = 0
    rw [hg, P.aeval_val_relation])

/-- Polynomial representatives reduce to their original presented values. -/
@[simp]
theorem liftedRelationMap_mk (f : MvPolynomial ι B) :
    P.liftedRelationMap q g hg (Ideal.Quotient.mk _ f) =
      aeval P.val (MvPolynomial.map q f) := rfl

/-- Reduction of lifted equations is surjective onto the specified original algebra. -/
theorem liftedRelationMap_surjective (hq : Function.Surjective q) :
    Function.Surjective (P.liftedRelationMap q g hg) := by
  intro e
  obtain ⟨f, hf⟩ := P.aeval_val_surjective e
  obtain ⟨f', hf'⟩ := MvPolynomial.map_surjective q hq f
  exact ⟨Ideal.Quotient.mk _ f', by rw [liftedRelationMap_mk, hf', hf]⟩

set_option backward.isDefEq.respectTransparency false in
/-- The entire reduction kernel is the extension of the coefficient kernel. -/
theorem ker_liftedRelationMap (hq : Function.Surjective q) :
    RingHom.ker (P.liftedRelationMap q g hg) =
      (RingHom.ker q).map (algebraMap B (MvPolynomial ι B ⧸ Ideal.span (Set.range g))) := by
  have hrel : (Ideal.span (Set.range g)).map (MvPolynomial.map q) = P.ker := by
    rw [Ideal.map_span, ← Set.range_comp]
    have he : (MvPolynomial.map q) ∘ g = P.relation := funext hg
    rw [he, P.span_range_relation_eq_ker]
  have he : RingHom.ker (aeval P.val).toRingHom = P.ker :=
    P.ker_eq_ker_aeval_val.symm
  rw [liftedRelationMap, Ideal.ker_quotient_lift, ← RingHom.comap_ker,
    he, ← hrel,
    Ideal.comap_map_of_surjective _ (MvPolynomial.map_surjective q hq),
    ← RingHom.ker_eq_comap_bot, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq,
    MvPolynomial.ker_map_eq_map_C, Ideal.map_map]
  rfl

/-- Any specified family of presentation relations has coefficientwise lifts, with exact
reduction and kernel. No flatness of the lifted algebra is asserted. -/
theorem exists_lifted_relations (hq : Function.Surjective q) :
    ∃ (g : σ → MvPolynomial ι B) (hg : ∀ i, MvPolynomial.map q (g i) = P.relation i),
      Function.Surjective (P.liftedRelationMap q g hg) ∧
      RingHom.ker (P.liftedRelationMap q g hg) =
        (RingHom.ker q).map
          (algebraMap B (MvPolynomial ι B ⧸ Ideal.span (Set.range g))) := by
  choose g hg using fun i ↦ MvPolynomial.map_surjective q hq (P.relation i)
  exact ⟨g, hg, P.liftedRelationMap_surjective q g hg hq,
    P.ker_liftedRelationMap q g hg hq⟩

/-- A finite family of lifted relations in finitely many variables gives a finitely
presented lifted quotient. This does not imply flatness. -/
theorem finitePresentation_liftedRelations [Finite ι] [Finite σ] :
    FinitePresentation B (MvPolynomial ι B ⧸ Ideal.span (Set.range g)) := by
  have hfg : (Ideal.span (Set.range g)).FG := by
    exact ⟨(Set.finite_range g).toFinset, by simp⟩
  exact FinitePresentation.quotient hfg

/-- Nilpotence of the original coefficient kernel persists in the actual lifted quotient. -/
theorem liftedRelationMap_ker_pow (hq : Function.Surjective q) {n : ℕ}
    (hn : RingHom.ker q ^ n = ⊥) :
    RingHom.ker (P.liftedRelationMap q g hg) ^ n = ⊥ := by
  rw [P.ker_liftedRelationMap q g hg hq, ← Ideal.map_pow, hn, Ideal.map_bot]

end Algebra.Presentation
