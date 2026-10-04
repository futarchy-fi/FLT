/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteHopfComponentTranslation
public import FLT.GroupScheme.LocalHopfArbitraryCoordinates
public import FLT.GroupScheme.RationalCoordinateRegularPresentation

/-! # Regular presentations of geometric Hopf factors in specified coordinates -/

@[expose] public noncomputable section

universe u

namespace HopfAlgebra

open FiniteAlgebra MvPolynomial

variable {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A] [HopfAlgebra k A]
  [IsArtinianRing A] [Module.Finite k A]
  (p : ℕ) [Fact p.Prime] [CharP k p]

include p

/-- Every polynomial presentation of a geometric Hopf component has a square kernel;
translation is used internally and does not change the specified coordinates. -/
theorem exists_component_relations_of_generators (m : ComponentIndex A) {n : ℕ}
    (x : Fin n → Component A m) (hs : Function.Surjective (aeval (R := k) x)) :
    ∃ r : Fin n → MvPolynomial (Fin n) k,
      RingHom.ker (aeval (R := k) x) = Ideal.span (Set.range r) := by
  obtain ⟨e⟩ := nonempty_componentEquiv_identity (k := k) m
  have hc : aeval (R := k) (fun i ↦ e (x i)) = e.toAlgHom.comp (aeval x) := by ext i; simp
  have hs' : Function.Surjective (aeval (R := k) (fun i ↦ e (x i))) := by
    rw [hc]
    exact e.surjective.comp hs
  obtain ⟨r, hr⟩ := exists_relations_of_arbitrary_generators p (fun i ↦ e (x i)) hs'
  refine ⟨r, ?_⟩
  rw [← hr, hc]
  ext q
  change aeval x q = 0 ↔ e (aeval x q) = 0
  exact (map_eq_zero_iff e e.injective).symm

/-- The specified geometric coordinates supply regular localized equations, their
full kernel and the original quotient map, for every Hopf component. -/
theorem exists_component_coordinate_regular_presentation (m : ComponentIndex A) {n : ℕ}
    (x : Fin n → Component A m) (hs : Function.Surjective (aeval (R := k) x)) :
    ∃ rs : List (aeval (R := k) x).localizedSource,
      rs.length = n ∧
      RingHom.ker (aeval (R := k) x).localizeAtMaximal = Ideal.ofList rs ∧
      RingTheory.Sequence.IsRegular (aeval (R := k) x).localizedSource rs ∧
      ∃ e : ((aeval (R := k) x).localizedSource ⧸ Ideal.ofList rs) ≃ₐ[k] Component A m,
        ∀ q, e (Ideal.Quotient.mk _ q) = (aeval (R := k) x).localizeAtMaximal q := by
  obtain ⟨e⟩ := nonempty_componentEquiv_identity (k := k) m
  obtain ⟨r, hr⟩ := exists_component_relations_of_generators p m x hs
  exact exists_local_regular_presentation_of_square_kernel
    ((Bialgebra.counitAlgHom k (FiniteIdentityComponent k A)).comp e.toAlgHom) x hs r hr

end HopfAlgebra
