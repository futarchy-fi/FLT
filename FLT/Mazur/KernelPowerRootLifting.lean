/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.KernelPowerTorsionLifting

/-!
# Lifting prescribed power roots through a group surjection

A root in the reduced group lifts to a root of the specified original element.
The correction uses only the power map on the actual reduction kernel, and
retains the prescribed reduced root. Kernel injectivity proves uniqueness.
-/

@[expose] public section
namespace FLT.Mazur.KernelPowerTorsionLifting
variable {G H : Type*} [CommGroup G] [CommGroup H] (ρ : G →* H) (n : ℕ)

/-- A lifted root can be corrected in the kernel without changing its reduction. -/
theorem exists_power_lift
    (hpow : Function.Surjective (fun z : ρ.ker ↦ z ^ n))
    (x a : G) (ha : ρ a ^ n = ρ x) :
    ∃ y : G, ρ y = ρ a ∧ y ^ n = x := by
  let d : ρ.ker := ⟨a ^ n / x, by rw [MonoidHom.mem_ker, map_div, map_pow, ha, div_self']⟩
  obtain ⟨z, hz⟩ := hpow d
  have he : (z : G) ^ n = a ^ n / x := congrArg Subtype.val hz
  refine ⟨a / z, ?_, ?_⟩
  · rw [map_div, z.property, div_one]
  · rw [div_pow, he, div_div_cancel]

/-- Power roots with a specified reduction are unique when kernel powers are injective. -/
theorem power_lift_unique
    (hpow : Function.Injective (fun z : ρ.ker ↦ z ^ n))
    {x y : G} (hxy : x ^ n = y ^ n) (hred : ρ x = ρ y) : x = y := by
  let d : ρ.ker := ⟨x / y, by rw [MonoidHom.mem_ker, map_div, hred, div_self']⟩
  have hd : d ^ n = 1 ^ n := by
    apply Subtype.ext
    change (x / y) ^ n = (1 : G) ^ n
    rw [div_pow, hxy, one_pow, div_self']
  exact div_eq_one.mp (congrArg Subtype.val (hpow hd))

/-- A surjective group map with bijective kernel powers lifts every prescribed power root. -/
theorem existsUnique_power_lift (hρ : Function.Surjective ρ)
    (hpow : Function.Bijective (fun z : ρ.ker ↦ z ^ n))
    (x : G) (b : H) (hb : b ^ n = ρ x) :
    ∃! y : G, ρ y = b ∧ y ^ n = x := by
  obtain ⟨a, ha⟩ := hρ b
  obtain ⟨y, hy, hyn⟩ := exists_power_lift ρ n hpow.2 x a (ha ▸ hb)
  refine ⟨y, ⟨hy.trans ha, hyn⟩, fun z hz ↦ ?_⟩
  exact power_lift_unique ρ n hpow.1 (hz.2.trans hyn.symm)
    (hz.1.trans (hy.trans ha).symm)

end FLT.Mazur.KernelPowerTorsionLifting
