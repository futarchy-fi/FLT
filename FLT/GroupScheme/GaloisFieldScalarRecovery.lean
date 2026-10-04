/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.SemilinearScalarRecovery
public import Mathlib.FieldTheory.Galois.NormalBasis
public import Mathlib.RingTheory.Trace.Basic

/-!
# Effective descent over finite Galois fields

Linear independence of field automorphisms constructs the orthogonality
coordinates needed for scalar recovery. Consequently every compatible
semilinear algebra action over a finite Galois field extension is effective.
This is a generic-fibre theorem, not integral unramified descent.
-/

@[expose] public noncomputable section
open scoped BigOperators TensorProduct
open Module
namespace SemilinearDescent

universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

open scoped Classical in
/-- Field automorphisms give a full-rank evaluation matrix, hence Galois coordinates. -/
theorem exists_field_coordinates :
    ∃ a : Module.Free.ChooseBasisIndex K L → L,
      ∀ g : L ≃ₐ[K] L, ∑ i, a i * g (Module.Free.chooseBasis K L i) =
        if g = 1 then 1 else 0 := by
  classical
  let e := Module.Free.chooseBasis K L
  have hq : Submodule.span L (Set.range fun i (g : L ≃ₐ[K] L) ↦ g (e i)) = ⊤ := by
    apply span_flip_eq_top_iff_linearIndependent.mpr
    exact ((linearIndependent_algHom_toLinearMap K L L).comp _
      (algEquivEquivAlgHom K L).injective).map' _ (e.constr L).symm.ker
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp
    (hq ▸ Submodule.mem_top (x := Pi.single (1 : L ≃ₐ[K] L) (1 : L)))
  refine ⟨a, fun g ↦ ?_⟩
  simpa [Pi.single_apply, eq_comm] using congrFun ha g

variable {B : Type u} [CommRing B] [Algebra K B] [Algebra L B]
  [IsScalarTower K L B]
  (ρ : (L ≃ₐ[K] L) →* (B ≃ₐ[K] B))
  (hρ : ∀ g s, ρ g (algebraMap L B s) = algebraMap L B (g s))

include hρ in
/-- No orthogonality or trace hypothesis remains in effective descent over Galois fields. -/
theorem field_recoveryMap_bijective :
    Function.Bijective (recoveryMap (S := L) ρ) := by
  classical
  obtain ⟨a, ha⟩ := exists_field_coordinates (K := K) (L := L)
  exact recoveryMap_bijective (MonoidHom.id (L ≃ₐ[K] L)) ρ hρ
    a (Module.Free.chooseBasis K L) ha (Algebra.trace K L)
    (fun s ↦ trace_eq_sum_automorphisms (K := K) s)

/-- The generic-fibre descent equivalence is constructed from the actual Galois action. -/
def fieldRecoveryEquiv : L ⊗[K] fixed ρ ≃ₐ[K] B :=
  AlgEquiv.ofBijective (recoveryMap ρ) (field_recoveryMap_bijective ρ hρ)

end SemilinearDescent
