/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.VeluTargetWitness
public import FLT.FreyCurve.Serre.VeluPrimeKernel
public import FLT.FreyCurve.Serre.QuotientEquationCoefficients

/-!
# Geometric kernel and coefficient data for actual Frey targets

Every target distinct from the source comes with a finite Galois-stable cyclic
geometric subgroup of order p whose Vélu equation is the target. This does not
yet construct a finite subgroup scheme or the modular-curve point.
-/

@[expose] public section

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace FreyPackage

variable {P : FreyPackage} {E : WeierstrassCurve ℚ}

/-- A nonidentity target retains a cyclic, Galois-stable geometric kernel of order p. -/
theorem IsVeluTarget.exists_cyclic_kernel (h : P.IsVeluTarget E) (hne : E ≠ P.freyCurve) :
    ∃ G : AddSubgroup (P.freyCurve⁄(AlgebraicClosure ℚ)).Point,
      IsAddCyclic G ∧ Nat.card G = P.p ∧
      (∀ (g : Field.absoluteGaloisGroup ℚ) x,
        x ∈ G → Affine.Point.map (W' := P.freyCurve) g.toAlgHom x ∈ G) ∧
      ∃ _ : Fintype G, E.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
        Velu.curve (P.freyCurve⁄(AlgebraicClosure ℚ)) G := by
  classical
  let _ : Fact P.p.Prime := ⟨P.pp⟩
  rcases h with heq | ⟨q, hq, hfixed, heq⟩
  · exact (hne heq).elim
  · refine ⟨Velu.torsionKernel P.freyCurve P.p q,
      Velu.torsionKernel_isAddCyclic_prime P.freyCurve P.p q hq,
      Velu.torsionKernel_card_prime P.freyCurve P.p q hq,
      Velu.torsionKernel_stable P.freyCurve P.p q hfixed, ?_⟩
    exact ⟨@Fintype.ofFinite _ (Velu.torsionKernel_finite P.freyCurve P.p q P.hppos), heq⟩

/-- Actual Frey targets retain the three coefficients unchanged by Vélu. -/
theorem IsVeluTarget.coefficients (h : P.IsVeluTarget E) :
    E.a₁ = P.freyCurve.a₁ ∧ E.a₂ = P.freyCurve.a₂ ∧ E.a₃ = P.freyCurve.a₃ := by
  rcases h with rfl | ⟨q, _, _, heq⟩
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨heq.a₁, heq.a₂, heq.a₃⟩

/-- The first and third coefficients remain in normalized Frey form on the actual target. -/
theorem IsVeluTarget.normalized_coefficients (h : P.IsVeluTarget E) :
    E.a₁ = 1 ∧ E.a₃ = 0 :=
  ⟨h.coefficients.1, h.coefficients.2.2⟩

/-- The b₂ invariant of an actual target is still the original difference of pth powers. -/
theorem IsVeluTarget.b₂ (h : P.IsVeluTarget E) :
    E.b₂ = P.b ^ P.p - P.a ^ P.p := by
  have he : E.b₂ = P.freyCurve.b₂ := by
    simp only [WeierstrassCurve.b₂, h.coefficients.1, h.coefficients.2.1]
  exact he.trans (FreyCurve.b₂ P)

end FreyPackage
