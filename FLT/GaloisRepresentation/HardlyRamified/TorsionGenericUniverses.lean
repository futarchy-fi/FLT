/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.TorsionTensorMaps
public import FLT.GaloisRepresentation.HardlyRamified.TorsionComparisonsUniverses

/-!
# Arbitrary-universe Generic maps of the actual hardly ramified torsion models

Conjugate the original tensor maps by the chosen point comparisons. Their
Galois equivariance follows from naturality for the original local operators.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GaloisRepresentation.IsHardlyRamified
open ThreeAdicPlan PrimePower

variable {p : ℕ} [Fact p.Prime] {hpodd : Odd p}
  {R V : Type*} [CommRing R] [IsLocalRing R] [Algebra ℤ_[p] R]
  [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[p] R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
  {hV : Module.rank R V = 2} {ρ : GaloisRep ℚ R V}
  (hρ : IsHardlyRamified hpodd hV ρ)
local notation "v" => LocalCyclotomic.rationalPlace p

/-- Transport an original tensor map to the selected geometric point groups. -/
def torsionGenericMapUniverses {m n : ℕ}
    (f : Level (V := V) (p : R) m →ₗ[R] Level (V := V) (p : R) n)
    (hf : ∀ g x, f ((ρ.toLocal v g).baseChange (Quot (p : R) m) x) =
      (ρ.toLocal v g).baseChange (Quot (p : R) n) (f x)) :
    GenericGaloisHom (hρ.torsionModelUniverses m) (hρ.torsionModelUniverses n) where
  toAddMonoidHom := (hρ.torsionPointsUniverses n).symm.toAddMonoidHom.comp
    (f.toAddMonoidHom.comp (hρ.torsionPointsUniverses m).toAddMonoidHom)
  map_smul' g x := by
    apply (hρ.torsionPointsUniverses n).injective
    change hρ.torsionPointsUniverses n ((hρ.torsionPointsUniverses n).symm
      (f (hρ.torsionPointsUniverses m (g • x)))) = _
    rw [AddEquiv.apply_symm_apply, hρ.torsionPoints_smul_universes, hρ.torsionPoints_smul_universes]
    change f ((ρ.toLocal v g).baseChange (Quot (p : R) m) (hρ.torsionPointsUniverses m x)) =
      (ρ.toLocal v g).baseChange (Quot (p : R) n)
        (hρ.torsionPointsUniverses n ((hρ.torsionPointsUniverses n).symm
          (f (hρ.torsionPointsUniverses m x))))
    rw [AddEquiv.apply_symm_apply, hf]

/-- The prescribed map is multiplication by p^n on the original quotients. -/
def torsionGenericInclusionUniverses (m n : ℕ) :
    GenericGaloisHom (hρ.torsionModelUniverses m) (hρ.torsionModelUniverses (m + n)) :=
  hρ.torsionGenericMapUniverses (tensorInclusion (p : R) m n)
    (fun g x ↦ tensorInclusion_natural _ _ _ (ρ.toLocal v g) x)

/-- The prescribed reduction is the original quotient reduction. -/
def torsionGenericReductionUniverses (m n : ℕ) :
    GenericGaloisHom (hρ.torsionModelUniverses (m + n)) (hρ.torsionModelUniverses n) :=
  hρ.torsionGenericMapUniverses (tensorReduction (p : R) m n)
    (fun g x ↦ tensorReduction_natural _ _ _ (ρ.toLocal v g) x)

/-- Inclusion agrees with its formula on the original tensor module. -/
@[simp] theorem torsionPoints_inclusion_universes (m n : ℕ)
    (x : (hρ.torsionModelUniverses m).Points) :
    hρ.torsionPointsUniverses (m + n) (hρ.torsionGenericInclusionUniverses m n x) =
      tensorInclusion (p : R) m n (hρ.torsionPointsUniverses m x) :=
  (hρ.torsionPointsUniverses (m + n)).apply_symm_apply _

/-- Reduction agrees with its formula on the original tensor module. -/
@[simp] theorem torsionPoints_reduction_universes (m n : ℕ)
    (x : (hρ.torsionModelUniverses (m + n)).Points) :
    hρ.torsionPointsUniverses n (hρ.torsionGenericReductionUniverses m n x) =
      tensorReduction (p : R) m n (hρ.torsionPointsUniverses (m + n) x) :=
  (hρ.torsionPointsUniverses n).apply_symm_apply _

/-- Reduction between chosen models is surjective on generic points. -/
theorem torsionGenericReduction_surjective_universes (m n : ℕ) :
    Function.Surjective (hρ.torsionGenericReductionUniverses m n) :=
  (hρ.torsionPointsUniverses n).symm.surjective.comp
    ((tensorReduction_surjective (V := V) (p : R) m n).comp
      (hρ.torsionPointsUniverses (m + n)).surjective)

/-- The transported generic sequence is exact. -/
theorem torsionGeneric_exact_universes (m n : ℕ) :
    Function.Exact (hρ.torsionGenericInclusionUniverses m n)
      (hρ.torsionGenericReductionUniverses m n) := by
  intro x
  rw [← (hρ.torsionPointsUniverses n).map_eq_zero_iff, torsionPoints_reduction_universes,
    tensor_exact (p : R) m n]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(hρ.torsionPointsUniverses m).symm y, (hρ.torsionPointsUniverses (m + n)).injective ?_⟩
    simpa only [torsionPoints_inclusion_universes, AddEquiv.apply_symm_apply] using hy
  · rintro ⟨y, rfl⟩
    exact ⟨hρ.torsionPointsUniverses m y, (hρ.torsionPoints_inclusion_universes m n y).symm⟩

end GaloisRepresentation.IsHardlyRamified
