/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FreeModuleResidueRetraction
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Nonvanishing of scalar extension of a map from the scalar line

The image of one detects the entire base-changed map. Nonzero residue maps
therefore produce a retraction of the original map into a free module.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped ChangeOfRings TensorProduct
namespace FLT.Mazur.LineScalarExtensionNonvanishing
universe u
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S]
  (φ : R →+* S) {M : ModuleCat.{u} R} (f : ModuleCat.of R R ⟶ M)

/-- Scalar extension of a line map vanishes exactly when the image of one does. -/
lemma map_eq_zero_iff : (ModuleCat.extendScalars φ).map f = 0 ↔
    (1 : S) ⊗ₜ[R,φ] f 1 = 0 := by
  let _ := φ.toAlgebra
  constructor
  · intro h
    exact congrArg (fun g ↦ g ((1 : S) ⊗ₜ[R,φ] (1 : R))) h
  · intro h
    apply ModuleCat.ExtendScalars.hom_ext
    intro r
    have hr : f r = r • f 1 := by
      simpa only [smul_eq_mul, mul_one] using f.hom.map_smul r (1 : R)
    change (1 : S) ⊗ₜ[R,φ] f r = 0
    rw [hr, TensorProduct.tmul_smul, h, smul_zero]

/-- Nonvanishing can be checked on the single original generator. -/
lemma map_ne_zero_iff : (ModuleCat.extendScalars φ).map f ≠ 0 ↔
    (1 : S) ⊗ₜ[R,φ] f 1 ≠ 0 := not_congr (map_eq_zero_iff φ f)

variable {ι : Type u} (b : Module.Basis ι R M)

include b in
/-- Nonzero actual residue module maps split the original map into a free module. -/
lemma exists_retraction
    (h : ∀ p : PrimeSpectrum R,
      (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).map f ≠ 0) :
    ∃ r : M ⟶ ModuleCat.of R R, f ≫ r = 𝟙 _ := by
  obtain ⟨r, hr⟩ := FreeModuleResidueRetraction.exists_functional_of_residue_tensor_ne_zero
    b (f 1) (fun p ↦ by
      have hm : Module.compHom p.asIdeal.ResidueField
          (algebraMap R p.asIdeal.ResidueField) =
          (inferInstance : Module R p.asIdeal.ResidueField) := by
        apply Module.ext
        funext a x
        exact (Algebra.smul_def a x).symm
      have hp := (map_ne_zero_iff _ f).mp (h p)
      rw [hm] at hp
      exact hp)
  refine ⟨ModuleCat.ofHom r, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change r (f a) = a
  have ha : f a = a • f 1 := by
    simpa only [smul_eq_mul, mul_one] using f.hom.map_smul a (1 : R)
  rw [ha, map_smul, hr, smul_eq_mul, mul_one]

end FLT.Mazur.LineScalarExtensionNonvanishing
