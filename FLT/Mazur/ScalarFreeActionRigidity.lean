/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupFreeUnramified
public import FLT.Mazur.ScalarFiniteTypeFiberTests

/-!
# Free-action rigidity over the unchanged scalar ring

The scalar map must contain every invariant source function, including its
nilpotent coefficients. Under this explicit source-image condition, a free
finite action constructs full scalar rigidity and finite type. Differential
fiber tests then follow at every target prime, including embedded primes.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarFreeActionRigidity
open FiniteGroupQuotient
variable (G : Type) [Group G] [Finite G]
  {R A : Type} [CommRing R] [CommRing A] [Algebra R A] [MulSemiringAction G A]
  (hfix : ∀ (g : G) (r : R), g • algebraMap R A r = algebraMap R A r)
  (hfull : ∀ a : A, (∀ g : G, g • a = a) → ∃ r : R, algebraMap R A r = a)
  (hfree : ∀ g : G, g ≠ 1 → fixedPointIdeal G A g = ⊤)
local notation "S" => invariantRing G A

/-- Scalar fullness is used on actual invariant functions, not only on residue classes. -/
def invariantScalarMap : R →+* S := lift G A (algebraMap R A) hfix

include hfull in
omit [Finite G] in
/-- The exact scalar-image condition gives surjectivity onto the full fixed ring. -/
theorem invariantScalarMap_surjective : Function.Surjective (invariantScalarMap G hfix) := by
  intro a
  obtain ⟨r, hr⟩ := hfull a.val a.property
  exact ⟨r, Subtype.ext hr⟩

include hfix hfull hfree in
/-- Source-image fullness and freeness kill all original-scalar differentials. -/
theorem formallyUnramified : Algebra.FormallyUnramified R A := by
  let _ := (invariantScalarMap G hfix).toAlgebra
  let _ : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq' rfl
  let _ : Algebra.FormallyUnramified R S :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId R S)
      (invariantScalarMap_surjective G hfix hfull)
  let _ := invariant_formallyUnramified G A hfree
  exact Algebra.FormallyUnramified.comp R S A

include hfix hfull hfree in
/-- Finite source coordinates are constructed from trace generators and exact scalar fullness. -/
theorem finiteType : Algebra.FiniteType R A := by
  let _ := (invariantScalarMap G hfix).toAlgebra
  let _ : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq' rfl
  let _ : Algebra.FiniteType R S := Algebra.FiniteType.of_surjective (Algebra.ofId R S)
    (invariantScalarMap_surjective G hfix hfull)
  let _ := invariant_module_finite G hfree
  exact Algebra.FiniteType.trans
    (show Algebra.FiniteType R S from inferInstance)
    (show Algebra.FiniteType S A from inferInstance)

include hfix hfull hfree in
/-- Every exact target residue fiber vanishes; no reducedness of the original source is used. -/
theorem fiberVanishes {B : Type} [CommRing B] (φ : A →+* B) (Q : PrimeSpectrum B) :
    ScalarFiniteTypeFiberTests.FiberVanishes (algebraMap R A) φ Q := by
  have hu : let _ := (algebraMap R A).toAlgebra; Algebra.FormallyUnramified R A := by
    rw [toAlgebra_algebraMap]
    exact formallyUnramified G hfix hfull hfree
  let _ := (algebraMap R A).toAlgebra
  let _ := ((algebraMap B Q.asIdeal.ResidueField).comp φ).toAlgebra
  let _ := hu
  exact inferInstanceAs (Subsingleton (TensorProduct A Q.asIdeal.ResidueField
    (KaehlerDifferential R A)))

include hfix hfull hfree in
/-- Actual finite coordinates and equations now construct the original full-stalk test. -/
theorem stalkTest {B : Type} [CommRing B] (φ : A →+* B) (Q : PrimeSpectrum B) :
    ScalarStalkJacobianTests.Test (algebraMap R A) φ Q := by
  apply ScalarFiniteTypeFiberTests.test _ _ _ ?_ (fiberVanishes G hfix hfull hfree φ Q)
  rw [toAlgebra_algebraMap]
  exact finiteType G hfix hfull hfree

end FLT.Mazur.ScalarFreeActionRigidity
