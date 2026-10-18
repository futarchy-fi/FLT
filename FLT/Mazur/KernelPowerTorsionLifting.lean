/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Hom.Instances

/-!
# Correcting arbitrary lifts of torsion labels inside the reduction kernel

Surjectivity of the nth power map on the kernel corrects any chosen lift of an
n-torsion point. Injectivity gives uniqueness. These are algebraic prerequisites
for correcting complete smooth-group labels; no divisibility of a geometric
kernel is assumed globally or asserted here.
-/

@[expose] public section
namespace FLT.Mazur.KernelPowerTorsionLifting
variable {G H : Type*} [CommGroup G] [CommGroup H] (ρ : G →* H) (n : ℕ)

/-- Divisibility in the kernel corrects a chosen point without changing its reduction. -/
theorem exists_torsion_lift
    (hpow : Function.Surjective (fun z : ρ.ker ↦ z ^ n))
    (x : G) (hx : ρ x ^ n = 1) :
    ∃ y : G, ρ y = ρ x ∧ y ^ n = 1 := by
  let d : ρ.ker := ⟨x ^ n, by rw [MonoidHom.mem_ker, map_pow, hx]⟩
  obtain ⟨z, hz⟩ := hpow d
  have he : (z : G) ^ n = x ^ n := congrArg Subtype.val hz
  refine ⟨x / z, ?_, ?_⟩
  · rw [map_div, z.property, div_one]
  · rw [div_pow, he, div_self']

/-- Absence of nth-power kernel collisions makes torsion lifts unique. -/
theorem torsion_lift_unique
    (hpow : Function.Injective (fun z : ρ.ker ↦ z ^ n))
    {x y : G} (hx : x ^ n = 1) (hy : y ^ n = 1) (hxy : ρ x = ρ y) : x = y := by
  let d : ρ.ker := ⟨x / y, by rw [MonoidHom.mem_ker, map_div, hxy, div_self']⟩
  have hd : d ^ n = 1 ^ n := by
    apply Subtype.ext
    change (x / y) ^ n = (1 : G) ^ n
    rw [div_pow, hx, hy, one_pow, div_self']
  have he : (d : G) = 1 := congrArg Subtype.val (hpow hd)
  exact div_eq_one.mp he

/-- A bijective kernel power map supplies the unique torsion correction of each chosen lift. -/
theorem existsUnique_torsion_lift
    (hpow : Function.Bijective (fun z : ρ.ker ↦ z ^ n))
    (x : G) (hx : ρ x ^ n = 1) :
    ∃! y : G, ρ y = ρ x ∧ y ^ n = 1 := by
  obtain ⟨y, hy, hyn⟩ := exists_torsion_lift ρ n hpow.2 x hx
  exact ⟨y, ⟨hy, hyn⟩, fun z hz ↦
    torsion_lift_unique ρ n hpow.1 hz.2 hyn (hz.1.trans hy.symm)⟩

end FLT.Mazur.KernelPowerTorsionLifting
