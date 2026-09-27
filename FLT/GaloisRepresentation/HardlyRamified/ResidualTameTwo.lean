/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.InertiaTwoSquareZero
public import FLT.GaloisRepresentation.HardlyRamified.ThreeAdicAlgebra
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Residual inertia at two

Hardly ramified representations over finite fields of characteristic three
have square-zero unipotent inertia at two. For any representation on a module
killed by three, this condition bounds the exponent of the inertia image by
three. Its order therefore divides three provided the image is cyclic.

The missing local-field input is cyclicity of this finite inertia image:
one must kill wild pro-two inertia and pass to the procyclic tame quotient.
The exponent bound alone does not imply an order bound.
-/

@[expose] public section

open Module

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace ThreeAdicPlan

/-- Residual hardly ramified representations have square-zero inertia at two,
using the inertia subgroup of the completion of the rationals at two. -/
@[nolint unusedArguments]
theorem inertia_two_sq_zero
    {k V : Type*} [Field k] [Finite k] [CharP k 3]
    [TopologicalSpace k] [IsTopologicalRing k] [Algebra ℤ_[3] k]
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    (hdim : Module.rank k V = 2) (ρbar : GaloisRep ℚ k V)
    (hρ : GaloisRepresentation.IsHardlyRamified (show Odd 3 by decide) hdim ρbar) :
    ∀ σ ∈ localInertiaGroup twoAdicPlace,
      (ρbar.map (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)) σ - 1) ^ 2 = 0 := by
  exact hardlyRamified_inertiaTwo_sq_zero hdim ρbar hρ

/-- Square-zero unipotence gives cube one on a module killed by three.
This also covers the zero module, whose endomorphism ring is trivial. -/
theorem end_cube_eq_one_of_killed_by_three
    {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (hkill : ∀ w : W, (3 : ℕ) • w = 0) (f : Module.End R W)
    (hf : (f - 1) ^ 2 = 0) : f ^ 3 = 1 := by
  rcases subsingleton_or_nontrivial (Module.End R W) with h | h
  · exact Subsingleton.elim _ _
  · have hthree : (3 : Module.End R W) = 0 := by
      ext w
      simpa using hkill w
    let : CharP (Module.End R W) 3 :=
      (CharP.charP_iff_prime_eq_zero (by decide)).mpr hthree
    exact GaloisRepresentation.cube_eq_one_of_sub_one_sq_eq_zero f hf

section InertiaImage

variable {R W : Type*} [CommRing R] [TopologicalSpace R]
  [AddCommGroup W] [Module R W]

/-- The action of local inertia at two, valued in invertible endomorphisms. -/
def inertiaTwoAction (ρ : GaloisRep ℚ R W) :
    localInertiaGroup twoAdicPlace →* (Module.End R W)ˣ :=
  letI := moduleTopology R (Module.End R W)
  (((ρ.map (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ))).toMonoidHom).comp
    (localInertiaGroup twoAdicPlace).subtype).toHomUnits

/-- The image of inertia at two acting on the module. -/
def inertiaTwoImage (ρ : GaloisRep ℚ R W) : Subgroup (Module.End R W)ˣ :=
  (inertiaTwoAction ρ).range

instance inertiaTwoImage_finite [Finite W] (ρ : GaloisRep ℚ R W) :
    Finite (inertiaTwoImage ρ) := by
  let : Finite (Module.End R W) := Finite.of_injective
    (fun f : Module.End R W ↦ (f : W → W)) DFunLike.coe_injective
  infer_instance

/-- The order of the inertia image at two. For a finite discrete continuous
Galois module this is the ramification index in the field fixed by the
representation's kernel. We use image order as the concrete definition, so
no choice of prime in that field is needed. The comparison with
`Ideal.ramificationIdx` is not asserted here. -/
def e_two (ρ : GaloisRep ℚ R W) : ℕ := Nat.card (inertiaTwoImage ρ)

/-- Every element of the inertia image has cube one. -/
theorem inertiaTwoImage_cube_eq_one (ρ : GaloisRep ℚ R W)
    (hkill : ∀ w : W, (3 : ℕ) • w = 0)
    (hunip : ∀ σ ∈ localInertiaGroup twoAdicPlace,
      (ρ.map (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)) σ - 1) ^ 2 = 0)
    (g : inertiaTwoImage ρ) : g ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  obtain ⟨σ, hσ⟩ := g.property
  change (g.val.val) ^ 3 = 1
  rw [← hσ]
  exact end_cube_eq_one_of_killed_by_three hkill _ (hunip σ.val σ.property)

/-- The exponent of the inertia image divides three. This is weaker than
the corresponding bound on its order. -/
theorem inertiaTwoImage_exponent_dvd_three (ρ : GaloisRep ℚ R W)
    (hkill : ∀ w : W, (3 : ℕ) • w = 0)
    (hunip : ∀ σ ∈ localInertiaGroup twoAdicPlace,
      (ρ.map (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)) σ - 1) ^ 2 = 0) :
    Monoid.exponent (inertiaTwoImage ρ) ∣ 3 :=
  Monoid.exponent_dvd_of_forall_pow_eq_one (inertiaTwoImage_cube_eq_one ρ hkill hunip)

/-- Square-zero unipotent inertia on a module killed by three has 3-group image. -/
theorem inertiaTwoImage_isThreeGroup (ρ : GaloisRep ℚ R W)
    (hkill : ∀ w : W, (3 : ℕ) • w = 0)
    (hunip : ∀ σ ∈ localInertiaGroup twoAdicPlace,
      (ρ.map (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)) σ - 1) ^ 2 = 0) :
    IsPGroup 3 (inertiaTwoImage ρ) := by
  intro g
  exact ⟨1, by simpa using inertiaTwoImage_cube_eq_one ρ hkill hunip g⟩

/-- Any 2-group mapping to this inertia image acts trivially. To apply this
to wild inertia one still needs the local-field theorem that its finite
continuous images are 2-groups; the absolute wild inertia group itself is
pro-2, not necessarily a torsion 2-group in the sense of `IsPGroup`. -/
theorem twoGroup_hom_inertiaTwoImage_eq_one (ρ : GaloisRep ℚ R W)
    (hkill : ∀ w : W, (3 : ℕ) • w = 0)
    (hunip : ∀ σ ∈ localInertiaGroup twoAdicPlace,
      (ρ.map (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)) σ - 1) ^ 2 = 0)
    {P : Type*} [Group P] (hP : IsPGroup 2 P)
    (f : P →* inertiaTwoImage ρ) : f = 1 := by
  apply MonoidHom.ext
  intro g
  obtain ⟨n, hn⟩ := hP g
  apply (pow_eq_one_iff_of_coprime
    ((by decide : Nat.Coprime 2 3).pow_left n)).mp
  exact ⟨by rw [← map_pow, hn, map_one], inertiaTwoImage_cube_eq_one ρ hkill hunip _⟩

/-- If the inertia image is cyclic, its exponent bound gives the ramification
bound. Establishing this cyclicity from local ramification theory remains a
separate input, not a consequence of square-zero unipotence alone. -/
theorem ramification_two_dvd_three_of_isCyclic (ρ : GaloisRep ℚ R W)
    [IsCyclic (inertiaTwoImage ρ)]
    (hkill : ∀ w : W, (3 : ℕ) • w = 0)
    (hunip : ∀ σ ∈ localInertiaGroup twoAdicPlace,
      (ρ.map (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)) σ - 1) ^ 2 = 0) :
    e_two ρ ∣ 3 := by
  rw [e_two, ← IsCyclic.exponent_eq_card]
  exact inertiaTwoImage_exponent_dvd_three ρ hkill hunip

end InertiaImage

end ThreeAdicPlan
