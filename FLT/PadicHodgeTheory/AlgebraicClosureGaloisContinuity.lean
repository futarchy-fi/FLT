/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.AlgebraicClosureGaloisTransport
public import Mathlib.FieldTheory.Galois.Profinite

/-! # Continuity of the actual Galois conjugation between isomorphic fields -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable {K L : Type*} [Field K] [Field L] [PerfectField K] [PerfectField L] (e : K ≃+* L)

omit [PerfectField K] [PerfectField L] in
/-- The chosen conjugation is continuous for the original Krull topologies. -/
theorem closureGaloisTransport_continuous : Continuous (closureGaloisTransport e) := by
  let c := closureFieldTransport e
  let : Algebra L K := e.symm.toRingHom.toAlgebra
  let : Algebra (AlgebraicClosure L) (AlgebraicClosure K) := c.symm.toRingHom.toAlgebra
  let : IsScalarTower L (AlgebraicClosure L) (AlgebraicClosure K) :=
    .of_algebraMap_eq fun x ↦ (closureFieldTransport_symm_algebraMap e x).symm
  let f := Field.absoluteGaloisGroup.mapOfAlgebra L K
  have hf : (closureGaloisTransport e : Gal(AlgebraicClosure K/K) →
      Gal(AlgebraicClosure L/L)) = f := by
    funext σ
    apply AlgEquiv.ext
    intro x
    apply c.symm.injective
    change c.symm (c (σ (c.symm x))) = c.symm ((show Gal(AlgebraicClosure L/L) from f σ) x)
    rw [RingEquiv.symm_apply_apply]
    exact ((σ.restrictScalars L).restrictNormal_commutes (AlgebraicClosure L) x).symm
  rw [hf]
  exact f.continuous

/-- The same chosen conjugation is a homeomorphism, with no second closure choice. -/
def closureGaloisContinuousTransport :
    Gal(AlgebraicClosure K/K) ≃ₜ* Gal(AlgebraicClosure L/L) := by
  let : IsGalois K (AlgebraicClosure K) := ⟨⟩
  exact { closureGaloisTransport e with
    continuous_toFun := closureGaloisTransport_continuous e
    continuous_invFun := by
      exact (closureGaloisTransport e).toEquiv.toHomeomorphOfContinuousClosed
        (closureGaloisTransport_continuous e)
        (closureGaloisTransport_continuous e).isClosedMap |>.continuous_symm }

end PadicHodgeTheory
