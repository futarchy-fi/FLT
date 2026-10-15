/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationClosedSections

/-!
# Nilpotent kernels of invariant structure-sheaf comparisons

A nilpotent source kernel induces a nilpotent kernel on invariant sections,
with the same exponent. This controls the actual quotient structure sheaf
without claiming that its restriction map is surjective.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S S' : Scheme.{u}} {A U : Over S} {A' U' : Over S'}
  {p q : A ⟶ U} {p' q' : A' ⟶ U'}
  (e : CategoryTheory.EquivalenceRelation p q)
  (e' : CategoryTheory.EquivalenceRelation p' q')
  (g : U'.left ⟶ U.left) (r : A'.left ⟶ A.left)
  (hp : r ≫ p.left = p'.left ≫ g) (hq : r ≫ q.left = q'.left ≫ g)
local notation "m" => invariantMap e e' g r hp hq
variable (O : TopologicalSpace.Opens (Orbit e))
local notation "ρ" => closedSourceRestriction e e' g r hp hq O
/-- The injective map from invariant sections to original source functions. -/
def invariantSourceSectionHom : (invariantSheaf e).obj.obj (op O) →+*
    (sourceSheaf e).obj.obj (op O) := ((invariantInclusion e).hom.app (op O)).hom

local notation "ι" => invariantSourceSectionHom e O

/-- The quotient kernel is exactly the pullback of the original source kernel ideal. -/
theorem invariantMap_section_ker :
    RingHom.ker ((m).c.app (op O)).hom = (RingHom.ker ρ).comap ι := by
  ext s
  exact invariantMap_section_eq_zero_iff e e' g r hp hq O s

/-- Kernel powers on the original source vanish with the scheme-theoretic exponent. -/
theorem closedSourceRestriction_ker_pow [QuasiCompact g]
    (hO : IsAffineOpen (pullOpen e O).val) (n : ℕ) (hn : g.ker ^ n = ⊥) :
    RingHom.ker ρ ^ n = ⊥ := by
  have h : RingHom.ker (g.app (pullOpen e O).val).hom ^ n = ⊥ := by
    have he := congrArg (fun J : U.left.IdealSheafData ↦
      J.ideal ⟨(pullOpen e O).val, hO⟩) hn
    simpa only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply,
      Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] using he
  suffices H : ∀ (V : U'.left.Opens) (hV : V = g ⁻¹ᵁ (pullOpen e O).val),
      RingHom.ker (g.appLE _ V hV.le).hom ^ n = ⊥ from
    H _ (invariantMap_sourceOpen_eq e e' g r hp hq O)
  intro V hV
  subst V
  simpa only [Scheme.Hom.appLE_eq_app] using h

/-- The invariant quotient's section kernel has the same explicit nilpotence bound. -/
theorem invariantMap_section_ker_pow [QuasiCompact g]
    (hO : IsAffineOpen (pullOpen e O).val) (n : ℕ) (hn : g.ker ^ n = ⊥) :
    RingHom.ker ((m).c.app (op O)).hom ^ n = ⊥ := by
  rw [invariantMap_section_ker]
  apply le_antisymm _ bot_le
  calc
    (RingHom.ker ρ).comap ι ^ n ≤ (RingHom.ker ρ ^ n).comap ι :=
      Ideal.le_comap_pow _ _
    _ = Ideal.comap ι ⊥ := by rw [closedSourceRestriction_ker_pow e e' g r hp hq O hO n hn]
    _ = ⊥ := Ideal.comap_bot_of_injective _ (fun _ _ h ↦ invariantSection_ext e O h)

/-- Every quotient section killed by restriction is nilpotent with the same exponent. -/
theorem invariantMap_section_pow_eq_zero [QuasiCompact g]
    (hO : IsAffineOpen (pullOpen e O).val) (n : ℕ) (hn : g.ker ^ n = ⊥)
    (s : (invariantSheaf e).obj.obj (op O)) (hs : (m).c.app (op O) s = 0) :
    s ^ n = 0 := by
  have hm := Ideal.pow_mem_pow (I := RingHom.ker ((m).c.app (op O)).hom) hs n
  rw [invariantMap_section_ker_pow e e' g r hp hq O hO n hn] at hm
  exact hm

end FLT.Mazur.RelativeRelationOrbit
