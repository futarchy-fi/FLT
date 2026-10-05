/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.IntegralPDPresentation
public import Mathlib.RingTheory.DividedPowers.DPMorphism

/-!
# Compatibility relations for the relative integral presentation

Impose the base divided powers on an ideal whose image lies in the presented
ideal. The quotient maps uniquely, with the prescribed symbols, to every
compatible PD target. This constructs relations and maps, not PD operations
on the quotient; it is not yet the relative PD envelope.
-/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (J : Ideal R) (hJ : DividedPowers J) (I : Ideal A)
  (hJI : ∀ x : J, algebraMap R A x ∈ I)

/-- Relations requiring the universal symbols to agree with the original base divided powers. -/
def relativePDRelations : Ideal (IntegralPDPresentation I) :=
  Ideal.span (Set.range fun nx : ℕ × J ↦
    integralPDSymbol I nx.1 ⟨algebraMap R A nx.2, hJI nx.2⟩ -
      algebraMap A (IntegralPDPresentation I) (algebraMap R A (hJ.dpow nx.1 nx.2)))

/-- The quotient with base compatibility imposed, without a presumed PD structure. -/
abbrev RelativePDPresentation := IntegralPDPresentation I ⧸ relativePDRelations J hJ I hJI

/-- Symbols in the relative presentation. -/
def relativePDSymbol (n : ℕ) (x : I) : RelativePDPresentation J hJ I hJI :=
  Ideal.Quotient.mk (relativePDRelations J hJ I hJI) (integralPDSymbol I n x)

/-- Base divided powers agree in this quotient by its defining relations. -/
theorem relativePDSymbol_base (n : ℕ) (x : J) :
    relativePDSymbol J hJ I hJI n ⟨algebraMap R A x, hJI x⟩ =
      algebraMap A (RelativePDPresentation J hJ I hJI) (algebraMap R A (hJ.dpow n x)) := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk (relativePDRelations J hJ I hJI)
    (integralPDSymbol I n ⟨algebraMap R A x, hJI x⟩ -
      algebraMap A (IntegralPDPresentation I) (algebraMap R A (hJ.dpow n x))) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(n, x), rfl⟩)

variable {B : Type*} [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  (K : Ideal B) (hK : DividedPowers K) (hI : ∀ x : I, algebraMap A B x ∈ K)
  (hbase : hJ.IsDPMorphism hK (algebraMap R B))

include hbase in
/-- Every genuinely compatible target kills the base compatibility relations. -/
theorem relativePDRelations_le_ker : relativePDRelations J hJ I hJI ≤
    RingHom.ker (integralPDTargetMap I K hK hI).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨n, x⟩, rfl⟩
  change integralPDTargetMap I K hK hI _ = 0
  rw [map_sub, integralPDTargetMap_symbol, AlgHom.commutes]
  change hK.dpow n (algebraMap A B (algebraMap R A x)) -
    algebraMap A B (algebraMap R A (hJ.dpow n x)) = 0
  rw [← IsScalarTower.algebraMap_apply R A B, ← IsScalarTower.algebraMap_apply R A B]
  exact sub_eq_zero.mpr (hbase.2 x x.property)

/-- The relative presentation's map to an arbitrary compatible target, including torsion targets. -/
def relativePDTargetMap : RelativePDPresentation J hJ I hJI →ₐ[A] B :=
  Ideal.Quotient.liftₐ (relativePDRelations J hJ I hJI)
    (integralPDTargetMap I K hK hI) (relativePDRelations_le_ker J hJ I hJI K hK hI hbase)

/-- Each symbol has its prescribed value in the compatible target. -/
theorem relativePDTargetMap_symbol (n : ℕ) (x : I) :
    relativePDTargetMap J hJ I hJI K hK hI hbase (relativePDSymbol J hJ I hJI n x) =
      hK.dpow n (algebraMap A B x) := integralPDTargetMap_symbol I K hK hI n x

omit [Algebra R B] [IsScalarTower R A B] in
/-- Symbol values uniquely determine maps from the relative presentation. -/
theorem relativePDPresentation_ext (f g : RelativePDPresentation J hJ I hJI →ₐ[A] B)
    (h : ∀ n x, f (relativePDSymbol J hJ I hJI n x) =
      g (relativePDSymbol J hJ I hJI n x)) : f = g := by
  have he : f.comp (Ideal.Quotient.mkₐ A (relativePDRelations J hJ I hJI)) =
      g.comp (Ideal.Quotient.mkₐ A (relativePDRelations J hJ I hJI)) :=
    integralPDPresentation_ext I _ _ h
  ext x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun he y

end PadicHodgeTheory
