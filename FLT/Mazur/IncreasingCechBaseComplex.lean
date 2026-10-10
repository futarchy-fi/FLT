/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechBaseCycles
public import FLT.Mazur.IncreasingCechGenericCohomology

/-!
# The actual bounded complex with its original base action

Type wrappers retain the base action on terms. The positive-degree homology
comparison uses the incoming and outgoing maps of this same complex.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.IncreasingCechScalars
open IncreasingCechComplex FCurve

universe u
variable {X : Scheme.{u}} {ι : Type u} [LinearOrder ι]
  (M : X.Modules) (U : ι → X.Opens) {R : Type u} [CommRing R]
  (ρ : R →+* Γ(X, ⊤))

/-- The original bounded term, remembering its structural scalar action. -/
def BaseTerm (_ρ : R →+* Γ(X, ⊤)) (n : ℕ) : Type u :=
  (complex U (moduleAbelianSheaf M)).X n

instance baseTermAddCommGroup (n : ℕ) : AddCommGroup (BaseTerm M U ρ n) :=
  inferInstanceAs (AddCommGroup ((complex U (moduleAbelianSheaf M)).X n))

instance baseTermModule (n : ℕ) : Module R (BaseTerm M U ρ n) :=
  Module.compHom ((complex U (moduleAbelianSheaf M)).X n) ρ

/-- Adjacent differentials of the actual base-valued complex. -/
def baseD (n : ℕ) : BaseTerm M U ρ n →ₗ[R] BaseTerm M U ρ (n + 1) :=
  baseDifferential M U ρ n (n + 1)

/-- These are the original square-zero differentials. -/
lemma baseD_comp (n : ℕ) : (baseD M U ρ (n + 1)).comp (baseD M U ρ n) = 0 := by
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom
    ((complex U (moduleAbelianSheaf M)).d_comp_d n (n + 1) (n + 1 + 1)) x

/-- The boundedness statement retains the actual base action. -/
lemma baseTerm_subsingleton [Fintype ι] (n : ℕ) (hn : Fintype.card ι ≤ n) :
    Subsingleton (BaseTerm M U ρ n) :=
  term_subsingleton U (moduleAbelianSheaf M) n hn

/-- Adjacent cycles use the original categorical cycle submodule. -/
def basePositiveCyclesEquiv (n : ℕ) :
    baseCycles M U ρ (n + 1) ≃ₗ[R] (baseD M U ρ (n + 1)).ker := by
  let _ := fun i ↦ Module.compHom ((complex U (moduleAbelianSheaf M)).X i) ρ
  apply LinearEquiv.ofEq
  unfold baseCycles
  rw [CochainComplex.next]
  rfl

/-- Positive boundaries are precisely the adjacent incoming image. -/
lemma mem_basePositiveBoundaries (n : ℕ) (x : baseCycles M U ρ (n + 1)) :
    x ∈ baseBoundaries M U ρ (n + 1) ↔
      ∃ z : BaseTerm M U ρ n, baseD M U ρ n z = x.val := by
  change (∃ z, baseToCycles M U ρ (n + 1) z = x) ↔ _
  simp only [Subtype.ext_iff]
  change (∃ z : (complex U (moduleAbelianSheaf M)).X ((ComplexShape.up ℕ).prev (n + 1)),
    (complex U (moduleAbelianSheaf M)).d _ (n + 1) z = x.val) ↔ _
  rw [CochainComplex.prev_nat_succ]
  rfl

/-- Actual positive cohomology is the explicit adjacent cycles/boundaries quotient. -/
def basePositiveHomologyEquiv (n : ℕ) :
    BaseHomology M U ρ (n + 1) ≃ₗ[R]
      ((baseD M U ρ (n + 1)).ker ⧸
        (baseD M U ρ n).range.comap (baseD M U ρ (n + 1)).ker.subtype) := by
  let _ := fun i ↦ Module.compHom ((complex U (moduleAbelianSheaf M)).X i) ρ
  let _ := Module.compHom ((complex U (moduleAbelianSheaf M)).homology (n + 1)) ρ
  refine (baseHomologyQuotientEquiv M U ρ (n + 1)).trans
    (Submodule.Quotient.equiv _ _ (basePositiveCyclesEquiv M U ρ n) ?_)
  rw [Submodule.map_equiv_eq_comap_symm]
  ext x
  exact mem_basePositiveBoundaries M U ρ n ((basePositiveCyclesEquiv M U ρ n).symm x)

end FLT.Mazur.IncreasingCechScalars
