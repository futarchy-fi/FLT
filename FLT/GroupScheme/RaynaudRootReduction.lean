/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudHenselianCharacters

/-!
# Reduction of prime-to-residue-characteristic roots of unity

Henselian lifting makes reduction surjective. The primitive roots already
constructed on both sides show that both groups have the same finite order,
so reduction is an isomorphism. Its inverse lifts characters multiplicatively.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R : Type*} [CommRing R]

section Local
variable [IsLocalRing R]

/-- Reduction on the actual groups of roots of unity. -/
def rootReduction (n : ℕ) : rootsOfUnity n R →* rootsOfUnity n (ResidueField R) where
  toFun z := ⟨Units.map (residue R).toMonoidHom z.val, by
    rw [mem_rootsOfUnity, ← map_pow, (mem_rootsOfUnity n z.val).mp z.property, map_one]⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

end Local

/-- Hensel's lemma lifts every root of unity of invertible order. -/
theorem rootReduction_surjective [HenselianLocalRing R] {n : ℕ}
    (hn : (n : ResidueField R) ≠ 0) : Function.Surjective (rootReduction (R := R) n) := by
  have : NeZero n := ⟨fun h ↦ hn (by simp [h])⟩
  intro ζ
  have hζ : (ζ.val : ResidueField R) ^ n = 1 := by
    exact congrArg Units.val ((mem_rootsOfUnity n ζ.val).mp ζ.property)
  obtain ⟨z, hz, he⟩ := henselian_lift_rootOfUnity hn (ζ.val : ResidueField R) hζ
  refine ⟨rootsOfUnity.mkOfPowEq z hz, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact he

/-- Reduction is bijective over the strict Henselian domain. -/
theorem rootReduction_bijective [IsDomain R] [HenselianLocalRing R]
    [IsSepClosed (ResidueField R)] {n : ℕ} (hn : (n : ResidueField R) ≠ 0) :
    Function.Bijective (rootReduction (R := R) n) := by
  have : NeZero (n : ResidueField R) := ⟨hn⟩
  have : NeZero n := .of_neZero_natCast (ResidueField R)
  let : HasEnoughRootsOfUnity R n := henselian_hasEnoughRootsOfUnity n hn
  apply (Nat.bijective_iff_surjective_and_card _).mpr
  exact ⟨rootReduction_surjective hn, by
    rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity, HasEnoughRootsOfUnity.natCard_rootsOfUnity]⟩

/-- The canonical inverse to reduction lifts roots compatibly with multiplication. -/
def rootReductionEquiv [IsDomain R] [HenselianLocalRing R]
    [IsSepClosed (ResidueField R)] {n : ℕ} (hn : (n : ResidueField R) ≠ 0) :
    rootsOfUnity n R ≃* rootsOfUnity n (ResidueField R) :=
  MulEquiv.ofBijective (rootReduction n) (rootReduction_bijective hn)

end ThreeAdicPlan
