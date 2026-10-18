/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeBadAffineCoverDenominators
public import FLT.Mazur.IntegralClosedSupport

/-!
# Exact kernels on the constructed reduced bad atlas

The actual bad charts are reduced. Consequently their scalar kernels already
compute the denominator ideal, without taking radicals or powers. This only
uses reduction on the bad support; the ambient source and its sections are unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeBadAffineCover
open SchemeOpenEnvelope SchemeScalarPrincipalNeighborhood
variable {R : Type} [CommRing R] {X : Scheme} (O : X.Opens)

instance badScheme_isReduced : IsReduced (badScheme O) :=
  FCurve.CoherentDevissage.reducedClosedSubscheme_isReduced ⟨(O : Set X)ᶜ, O.isOpen.isClosed_compl⟩

variable [NoetherianSpace X] (s : R →+* Γ(X, ⊤))

/-- The coordinate ring of each actual affine bad chart has no nonzero nilpotents. -/
theorem badChart_coordinates_reduced (i : (badCover O).I₀) :
    _root_.IsReduced Γ((badCover O).X i, ⊤) := inferInstance

/-- The actual scalar kernel on each bad chart is already radical. -/
theorem badChart_kernel_isRadical (i : (badCover O).I₀) :
    (RingHom.ker (badChartScalar s O i)).IsRadical :=
  Ideal.isRadical_bot.comap (badChartScalar s O i)

/-- No powers are needed in the finite bad-chart denominator formula. -/
theorem denominatorIdeal_eq_badChart_exact_kernels :
    denominatorIdeal s O = ⨅ i, RingHom.ker (badChartScalar s O i) := by
  rw [denominatorIdeal_eq_badChart_kernels]
  congr 1
  funext i
  exact (badChart_kernel_isRadical O s i).radical

/-- An original scalar is a denominator exactly when it vanishes on every bad chart. -/
theorem mem_denominatorIdeal_iff_badChart_zero (r : R) :
    r ∈ denominatorIdeal s O ↔ ∀ i, badChartScalar s O i r = 0 := by
  rw [denominatorIdeal_eq_badChart_exact_kernels, Ideal.mem_iInf]
  rfl

/-- Every safe original prime has one scalar killed on all actual bad charts at once. -/
theorem mem_scalarNeighborhoodLocus_iff_badChart_zero (P : PrimeSpectrum R) :
    P ∈ scalarNeighborhoodLocus s O ↔
      ∃ r : R, r ∉ P.asIdeal ∧ ∀ i, badChartScalar s O i r = 0 := by
  rw [mem_scalarNeighborhoodLocus_iff]
  constructor
  · rintro ⟨r, hr, hO⟩
    exact ⟨r, hr, (mem_denominatorIdeal_iff_badChart_zero O s r).mp hO⟩
  · rintro ⟨r, hr, hz⟩
    exact ⟨r, hr, (mem_denominatorIdeal_iff_badChart_zero O s r).mpr hz⟩

end FLT.Mazur.SchemeBadAffineCover
