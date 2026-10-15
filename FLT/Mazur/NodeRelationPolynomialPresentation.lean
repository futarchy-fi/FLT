/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingRing

/-!
# Polynomial expressions on a relation between two original node charts

When the source and target generate a relation ring, every function is a
polynomial in the two target coordinates with original source coefficients.
This keeps the full relation ring, without passing to its reduced quotient.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonSmoothing
variable {A B R : Type*} [CommRing A] [CommRing B] [CommRing R]
variable (t : A) (s : B →+* R) (q : ChartRing t →+* R) (c : A →+* B)

/-- Evaluate two target variables with coefficients in the unchanged source ring. -/
def nodeRelationPolynomialMap : MvPolynomial (Fin 2) B →+* R :=
  MvPolynomial.eval₂Hom s ![q (leftCoordinate t), q (rightCoordinate t)]

/-- Original target polynomials are evaluated by this same source-coefficient map. -/
theorem nodeRelationPolynomialMap_target
    (hc : ∀ a, s (c a) = q (algebraMap A (ChartRing t) a))
    (p : MvPolynomial (Fin 2) A) :
    nodeRelationPolynomialMap t s q (MvPolynomial.map c p) =
      q (Ideal.Quotient.mk (relationIdeal t) p) := by
  have he : (nodeRelationPolynomialMap t s q).comp (MvPolynomial.map c) =
      q.comp (Ideal.Quotient.mk (relationIdeal t)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.map_C, nodeRelationPolynomialMap,
        MvPolynomial.eval₂Hom_C]
      rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
      exact hc a
    · intro i
      fin_cases i <;> simp [nodeRelationPolynomialMap, leftCoordinate, rightCoordinate]
  exact RingHom.congr_fun he p

/-- The two actual node maps give a surjective polynomial presentation of their relation. -/
theorem nodeRelationPolynomialMap_surjective
    (hc : ∀ a, s (c a) = q (algebraMap A (ChartRing t) a))
    (hg : Subring.closure (Set.range s ∪ Set.range q) = ⊤) :
    Function.Surjective (nodeRelationPolynomialMap t s q) := by
  have he : (nodeRelationPolynomialMap t s q).range = ⊤ := by
    apply top_unique
    rw [← hg]
    apply Subring.closure_le.mpr
    rintro z (⟨b, rfl⟩ | ⟨a, rfl⟩)
    · exact ⟨MvPolynomial.C b, MvPolynomial.eval₂_C _ _ _⟩
    · obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact ⟨MvPolynomial.map c p, nodeRelationPolynomialMap_target t s q c hc p⟩
  intro z
  have hz : z ∈ (nodeRelationPolynomialMap t s q).range := by rw [he]; trivial
  exact hz

end FLT.Mazur.PolygonSmoothing
