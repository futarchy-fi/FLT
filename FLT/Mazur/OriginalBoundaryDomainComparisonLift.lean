/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationFiniteValuationArrows
public import FLT.Mazur.OriginalBoundaryFiniteComparisonTests

/-!
# Actual full comparison lifts from generic coverage over a domain

The finite closed comparison test covers a domain when it covers its generic
point. Reducedness of the coefficient domain then makes this closed immersion
an isomorphism. This constructs a unique full original arrow and finiteness
of the second endpoint, rather than assuming either. The boundary itself is
unchanged and need not be reduced; arbitrary nonreduced tests remain separate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem kernel_le_of_exists_factor {X Y Z : Scheme.{0}}
    (a : X ⟶ Y) (b : Z ⟶ Y) (h : ∃ d : Z ⟶ X, d ≫ a = b) :
    RingHom.ker a.appTop.hom ≤ RingHom.ker b.appTop.hom := by
  obtain ⟨d, rfl⟩ := h
  intro r hr
  change (d ≫ a).appTop.hom r = 0
  rw [Scheme.Hom.comp_appTop]
  change d.appTop.hom (a.appTop.hom r) = 0
  rw [show a.appTop.hom r = 0 from hr, map_zero]

variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsAffine A]
  (e : CategoryTheory.EquivalenceRelation p q) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local instance domainComparisonBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
attribute [local irreducible] scalarMorphism
variable {R : Type} [CommRing R] [IsDomain R]

include e

/-- Generic coverage makes the full original comparison test an isomorphism over a domain. -/
theorem originalBoundary_domain_comparison_isIso
    (t : Spec (.of R) ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (ht : t (⊥ : PrimeSpectrum R) ∈ Set.range c) : IsIso (pullback.snd c t) := by
  let _ := originalBoundary_comparison_test_closedImmersion J hJ t e
  let _ : Surjective (pullback.snd c t) := ⟨by
    intro u
    have hu := originalBoundary_comparison_test_coverage_of_generic J hJ t ht
      (Set.mem_range_self u)
    have hr : u ∈ Set.range (pullback.snd c t) := by
      rw [Scheme.Pullback.range_snd]
      exact hu
    exact hr⟩
  exact isIso_of_isClosedImmersion_of_surjective (pullback.snd c t)

/-- The full original arrow is constructed uniquely on the whole coefficient domain. -/
theorem originalBoundary_domain_unique_lift
    (t : Spec (.of R) ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (ht : t (⊥ : PrimeSpectrum R) ∈ Set.range c) :
    ∃! d : Spec (.of R) ⟶ pullback p J.subschemeι, d ≫ c = t := by
  let _ := originalBoundary_domain_comparison_isIso e J hJ t ht
  let _ := originalBoundaryComparison_mono e J hJ
  refine ⟨inv (pullback.snd c t) ≫ pullback.fst c t, ?_, ?_⟩
  · change (inv (pullback.snd c t) ≫ pullback.fst c t) ≫ c = t
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  · intro d hd
    apply (cancel_mono c).mp
    rw [hd, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

/-- Generic image coverage and one full finite endpoint construct finiteness of the other. -/
theorem originalBoundary_domain_second_finite
    (t : Spec (.of R) ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (ht : t (⊥ : PrimeSpectrum R) ∈ Set.range c) : IsFinite (pullback.snd p (t ≫ y)) := by
  obtain ⟨d, hd, _⟩ := originalBoundary_domain_unique_lift e J hJ t ht
  have hx : (d ≫ pullback.fst p J.subschemeι) ≫ p = t ≫ x := by
    rw [← hd]
    simp only [Category.assoc, originalBoundaryComparison, pullback.lift_fst_assoc,
      pullback.condition]
  have hy : (d ≫ pullback.fst p J.subschemeι) ≫ q = t ≫ y := by
    rw [← hd]
    simp only [Category.assoc, originalBoundaryComparison, pullback.lift_snd_assoc,
      InvariantIdealRelation.snd_ι]
  exact (EquivalenceRelationFiber.finite_pullback_iff_of_arrow e
    (t ≫ x) (t ≫ y) (d ≫ pullback.fst p J.subschemeι) hx hy).mp inferInstance

/-- The constructed arrow annihilates the full original comparison kernel on this domain. -/
theorem originalBoundary_domain_comparison_kernel
    (t : Spec (.of R) ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (ht : t (⊥ : PrimeSpectrum R) ∈ Set.range c) :
    RingHom.ker (c).appTop.hom ≤ RingHom.ker t.appTop.hom :=
  kernel_le_of_exists_factor c t (originalBoundary_domain_unique_lift e J hJ t ht).exists

end FLT.Mazur.EquivalenceRelationOrderedFrames
