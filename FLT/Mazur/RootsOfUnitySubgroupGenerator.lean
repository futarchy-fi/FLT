/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SubgroupIntrinsicCartierGenerator
public import FLT.Mazur.RootsOfUnityIntrinsicOrbit

/-!
# Cyclotomic Cartier generators for original roots subgroups

A group isomorphism from the roots-of-unity scheme to the actual subgroup
transports the cyclotomic section and its full intrinsic orbit product. The
result concerns the original ambient subgroup ideal, including repeated roots.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] {E : GeneralizedEllipticCurve (Spec (.of R))}
  {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  (e : RootsOfUnityScheme.model R n ≅ H.carrier) [IsMonHom e.hom]
  (φ : IntegralCyclotomicCoordinates.Coordinate n →+* R)

/-- The specialized root as a section of the original subgroup carrier. -/
def rootsGenerator : 𝟙_ (Over (Spec (.of R))) ⟶ H.carrier :=
  RootsOfUnityIntrinsicOrbit.generator n φ ≫ e.hom

/-- The transported root retains the exact torsion relation. -/
theorem rootsGenerator_pow : H.rootsGenerator e φ ^ n = 1 := by
  rw [rootsGenerator, ← MonObj.pow_comp, RootsOfUnityIntrinsicOrbit.generator_pow]
  exact MonObj.one_comp e.hom

/-- The entire intrinsic orbit product vanishes on the original subgroup. -/
theorem rootsGenerator_intrinsic_orbit :
    ∏ k : Fin n, (H.rootsGenerator e φ ^ k.val).left.ker = ⊥ := by
  let _ : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  let _ : ∀ k : Fin n, IsClosedImmersion
      ((RootsOfUnityIntrinsicOrbit.generator n φ ^ k.val).left ≫ e.hom.left) := fun k ↦
    FCurve.isClosedImmersion_section H.carrier.hom
      ((RootsOfUnityIntrinsicOrbit.generator n φ ^ k.val) ≫ e.hom).left (Over.w _)
  apply le_antisymm _ bot_le
  simpa only [rootsGenerator, ← MonObj.pow_comp, Over.comp_left,
    Scheme.Hom.ker_eq_bot_of_isIso] using
    RootsOfUnityIntrinsicOrbit.ambient_orbit_le n φ e.hom.left

/-- The specified root generates the entire original Cartier divisor. -/
theorem rootsGenerator_isCartierGenerator [SmoothOfRelativeDimension 1 E.group.hom] :
    H.IsCartierGenerator (H.rootsGenerator e φ) :=
  H.isCartierGenerator_of_intrinsic_orbit _ (H.rootsGenerator_pow e φ)
    (H.rootsGenerator_intrinsic_orbit e φ)

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
