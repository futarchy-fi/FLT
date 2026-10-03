/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.TorsionTensorMaps
public import FLT.GaloisRepresentation.HardlyRamified.TorsionModelComparisons

/-!
# Generic maps of the actual hardly ramified torsion models

Conjugate the original tensor maps by the chosen point comparisons. Their
Galois equivariance follows from naturality for the original local operators.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GaloisRepresentation.IsHardlyRamified
open ThreeAdicPlan PrimePower

variable {p : ℕ} [Fact p.Prime] {hpodd : Odd p}
  {R V : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[p] R]
  [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[p] R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
  {hV : Module.rank R V = 2} {ρ : GaloisRep ℚ R V}
  (hρ : IsHardlyRamified hpodd hV ρ)
local notation "v" => LocalCyclotomic.rationalPlace p

/-- Transport an original tensor map to the selected geometric point groups. -/
def torsionGenericMap {m n : ℕ}
    (f : Level (V := V) (p : R) m →ₗ[R] Level (V := V) (p : R) n)
    (hf : ∀ g x, f ((ρ.toLocal v g).baseChange (Quot (p : R) m) x) =
      (ρ.toLocal v g).baseChange (Quot (p : R) n) (f x)) :
    GenericGaloisHom (hρ.torsionModel m) (hρ.torsionModel n) where
  toAddMonoidHom := (hρ.torsionPoints n).symm.toAddMonoidHom.comp
    (f.toAddMonoidHom.comp (hρ.torsionPoints m).toAddMonoidHom)
  map_smul' g x := by
    apply (hρ.torsionPoints n).injective
    change hρ.torsionPoints n ((hρ.torsionPoints n).symm
      (f (hρ.torsionPoints m (g • x)))) = _
    rw [AddEquiv.apply_symm_apply, hρ.torsionPoints_smul, hρ.torsionPoints_smul]
    change f ((ρ.toLocal v g).baseChange (Quot (p : R) m) (hρ.torsionPoints m x)) =
      (ρ.toLocal v g).baseChange (Quot (p : R) n)
        (hρ.torsionPoints n ((hρ.torsionPoints n).symm (f (hρ.torsionPoints m x))))
    rw [AddEquiv.apply_symm_apply, hf]

/-- The prescribed map is multiplication by p^n on the original quotients. -/
def torsionGenericInclusion (m n : ℕ) :
    GenericGaloisHom (hρ.torsionModel m) (hρ.torsionModel (m + n)) :=
  hρ.torsionGenericMap (tensorInclusion (p : R) m n)
    (fun g x ↦ tensorInclusion_natural _ _ _ (ρ.toLocal v g) x)

/-- The prescribed reduction is the original quotient reduction. -/
def torsionGenericReduction (m n : ℕ) :
    GenericGaloisHom (hρ.torsionModel (m + n)) (hρ.torsionModel n) :=
  hρ.torsionGenericMap (tensorReduction (p : R) m n)
    (fun g x ↦ tensorReduction_natural _ _ _ (ρ.toLocal v g) x)

/-- Inclusion agrees with its formula on the original tensor module. -/
@[simp] theorem torsionPoints_inclusion (m n : ℕ) (x : (hρ.torsionModel m).Points) :
    hρ.torsionPoints (m + n) (hρ.torsionGenericInclusion m n x) =
      tensorInclusion (p : R) m n (hρ.torsionPoints m x) :=
  (hρ.torsionPoints (m + n)).apply_symm_apply _

/-- Reduction agrees with its formula on the original tensor module. -/
@[simp] theorem torsionPoints_reduction (m n : ℕ) (x : (hρ.torsionModel (m + n)).Points) :
    hρ.torsionPoints n (hρ.torsionGenericReduction m n x) =
      tensorReduction (p : R) m n (hρ.torsionPoints (m + n) x) :=
  (hρ.torsionPoints n).apply_symm_apply _

/-- Reduction between chosen models is surjective on generic points. -/
theorem torsionGenericReduction_surjective (m n : ℕ) :
    Function.Surjective (hρ.torsionGenericReduction m n) :=
  (hρ.torsionPoints n).symm.surjective.comp
    ((tensorReduction_surjective (V := V) (p : R) m n).comp
      (hρ.torsionPoints (m + n)).surjective)

/-- The transported generic sequence is exact. -/
theorem torsionGeneric_exact (m n : ℕ) :
    Function.Exact (hρ.torsionGenericInclusion m n) (hρ.torsionGenericReduction m n) := by
  intro x
  rw [← (hρ.torsionPoints n).map_eq_zero_iff, torsionPoints_reduction,
    tensor_exact (p : R) m n]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(hρ.torsionPoints m).symm y, (hρ.torsionPoints (m + n)).injective ?_⟩
    simpa only [torsionPoints_inclusion, AddEquiv.apply_symm_apply] using hy
  · rintro ⟨y, rfl⟩
    exact ⟨hρ.torsionPoints m y, (hρ.torsionPoints_inclusion m n y).symm⟩

end GaloisRepresentation.IsHardlyRamified
