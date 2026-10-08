/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicCohomologyImage
public import FLT.Mazur.IdealPowerScalarLift
public import Mathlib.RingTheory.Filtration

/-!
# Ideal compatibility of the cohomology image filtration

Base ideal powers multiply the actual image filtration into higher terms.
The proof lifts scalar multiplication on the coefficient sheaves and retains
the original inclusions. This proves one containment between topologies;
the reverse containment requires cohomological Artin-Rees.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open FLT.Mazur.FCurve FLT.Mazur.GlobalIdealPower
open FLT.Mazur.GlobalIdealPowerCompatibility FLT.Mazur.IdealPowerScalarLift

universe u

namespace FLT.Mazur.IdealAdicQuotient

local instance scalarImageHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]
  (J : Ideal R)
  (hJ : ∀ (r : R), r ∈ J → ∀ U : X.affineOpens,
    X.presheaf.map U.1.leTop.op (ρ r) ∈ I.ideal U)

include hJ

omit [IsLocallyNoetherian X] in
/-- Affine ideal containment persists for every power of the base ideal. -/
lemma basePowerScalar_mem (a : ℕ) (r : R) (hr : r ∈ J ^ a) (U : X.affineOpens) :
    X.presheaf.map U.1.leTop.op (ρ r) ∈ (I ^ a).ideal U := by
  let σ := (X.presheaf.map U.1.leTop.op).hom.comp ρ
  have h : J.map σ ≤ I.ideal U := Ideal.map_le_iff_le_comap.mpr (fun r hr ↦ hJ r hr U)
  have hp : (J ^ a).map σ ≤ (I.ideal U) ^ a := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' h a
  exact hp (Ideal.mem_map_of_mem σ hr)

/-- A base power scalar moves an actual cohomology image into the summed exponent. -/
lemma smul_mem_cohomologyImage (q n a : ℕ) (r : R) (hr : r ∈ J ^ a)
    (x : ModuleRingH ρ M q) (hx : x ∈ cohomologyImage ρ I M q n) :
    r • x ∈ cohomologyImage ρ I M q (n + a) := by
  obtain ⟨y, rfl⟩ := hx
  let g := scalarLift (I ^ a) (power I n M) (ρ r)
    (basePowerScalar_mem ρ I J hJ a r hr)
  let e := nestedPowerIso I n a M
  refine ⟨moduleHMap (g ≫ e.hom) q y, ?_⟩
  change moduleHMap (inclusion (I ^ (n + a)) M) q
    (moduleHMap (g ≫ e.hom) q y) = ρ r • moduleHMap (inclusion (I ^ n) M) q y
  rw [← LinearMap.comp_apply, ← moduleHMap_comp, Category.assoc, nestedPowerIso_comp,
    ← Category.assoc, scalarLift_inclusion, moduleHMap_comp, LinearMap.comp_apply,
    scalarEnd_cohomology, map_smul]

/-- The image filtration is compatible with multiplication by every base ideal power. -/
lemma idealPower_smul_cohomologyImage_le (q n a : ℕ) :
    J ^ a • cohomologyImage ρ I M q n ≤ cohomologyImage ρ I M q (n + a) := by
  apply Submodule.smul_le.mpr
  intro r hr x hx
  exact smul_mem_cohomologyImage ρ I M J hJ q n a r hr x hx

/-- The ordinary adic filtration is contained in the actual cohomology image filtration. -/
lemma idealPower_smul_top_le_cohomologyImage (q n : ℕ) :
    J ^ n • (⊤ : Submodule R (ModuleRingH ρ M q)) ≤ cohomologyImage ρ I M q n := by
  simpa only [cohomologyImage_zero, zero_add] using
    idealPower_smul_cohomologyImage_le ρ I M J hJ q 0 n

/-- The actual images form an ideal filtration with the original base scalars. -/
def cohomologyFiltration (q : ℕ) : J.Filtration (ModuleRingH ρ M q) where
  N := cohomologyImage ρ I M q
  mono n := cohomologyImage_antitone ρ I M q (Nat.le_succ n)
  smul_le n := by
    simpa only [pow_one] using idealPower_smul_cohomologyImage_le ρ I M J hJ q n 1

end FLT.Mazur.IdealAdicQuotient
