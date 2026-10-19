/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupCharacterOrbits
public import FLT.Mazur.FiniteGroupQuotientGeometricPoints

/-!
# Lifting actual invariant characters to the original affine scheme

Integral lifting constructs a source character over the specified algebraically
closed field. Its quotient is exactly the given character as a scheme map.
All other lifts differ by the actual scheme action over that same field.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type} [Group G] [Finite G] {X : Scheme} [IsAffine X]
  (ρ : G →* Aut X) {K : Type} [Field K]

omit [Finite G] in
/-- Equality of quotient scheme maps detects every invariant value, including residue maps. -/
theorem sourceCharacterMap_quotient_eq_iff (v w : Γ(X, ⊤) →+* K) :
    sourceCharacterMap v ≫ quotientMap ρ = sourceCharacterMap w ≫ quotientMap ρ ↔
      ∀ t : invariantCoordinates ρ, v t.val = w t.val := by
  rw [sourceCharacterMap_quotient, sourceCharacterMap_quotient]
  constructor
  · intro h t
    exact congrArg (fun f ↦ f.hom t) (Spec.map_injective h)
  · intro h
    apply congrArg Spec.map
    ext t
    exact h t

/-- Any two characters in the same actual quotient fiber differ by a scheme automorphism. -/
theorem sourceCharacterMap_quotient_eq_iff_orbit (v w : Γ(X, ⊤) →+* K) :
    sourceCharacterMap v ≫ quotientMap ρ = sourceCharacterMap w ≫ quotientMap ρ ↔
      ∃ g : G, sourceCharacterMap v ≫ (ρ g).hom = sourceCharacterMap w := by
  constructor
  · intro h
    exact sourceCharacterMap_orbit_of_invariants ρ v w
      ((sourceCharacterMap_quotient_eq_iff ρ v w).mp h)
  · rintro ⟨g, hg⟩
    rw [← hg, Category.assoc, quotientMap_invariant]

variable [IsAlgClosed K]

omit [IsAffine X] in
/-- Integral lifting realizes every quotient character on the unchanged original affine source. -/
theorem exists_sourceCharacter_lift (χ : invariantCoordinates ρ →+* K) :
    ∃ w : Γ(X, ⊤) →+* K, ∀ t : invariantCoordinates ρ, w t.val = χ t := by
  let _ := SchemeCoordinateAction.coordinateAction ρ
  let _ := Algebra.IsInvariant.isIntegral (invariantCoordinates ρ) Γ(X, ⊤) G
  obtain ⟨w, hw⟩ := FiniteGroupQuotient.exists_ringHom_of_integral
    (invariantCoordinates ρ) Γ(X, ⊤) χ
  exact ⟨w, fun t ↦ congrArg (fun f : invariantCoordinates ρ →+* K ↦ f t) hw⟩

/-- The constructed lift has the specified quotient morphism, and all its lifts form one orbit. -/
theorem exists_sourceCharacter_quotient_orbit (χ : invariantCoordinates ρ →+* K) :
    ∃ w : Γ(X, ⊤) →+* K,
      sourceCharacterMap w ≫ quotientMap ρ = Spec.map (CommRingCat.ofHom χ) ∧
      ∀ v : Γ(X, ⊤) →+* K,
        sourceCharacterMap v ≫ quotientMap ρ = Spec.map (CommRingCat.ofHom χ) →
        ∃ g : G, sourceCharacterMap w ≫ (ρ g).hom = sourceCharacterMap v := by
  obtain ⟨w, hw⟩ := exists_sourceCharacter_lift ρ χ
  have he : sourceCharacterMap w ≫ quotientMap ρ = Spec.map (CommRingCat.ofHom χ) := by
    rw [sourceCharacterMap_quotient]
    apply congrArg Spec.map
    ext t
    exact hw t
  exact ⟨w, he, fun v hv ↦ (sourceCharacterMap_quotient_eq_iff_orbit ρ w v).mp
    (he.trans hv.symm)⟩

end FLT.Mazur.SchemeFiniteGroupQuotient
