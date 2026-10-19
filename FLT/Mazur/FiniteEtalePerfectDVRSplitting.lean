/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.FiniteEtaleRationalCover
public import FLT.Mazur.FiniteExtensionPerfectValuationSubring

/-!
# Finite generic splitting with a perfect-residue DVR

Construct the splitting field and the extended Noetherian valuation ring
with perfect residue, retaining the entire original finite étale source.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteEtalePerfectDVRSplitting
variable {K : Type} [Field K] [PerfectField K]
  (A : ValuationSubring K) [IsDiscreteValuationRing A]
  [PerfectField (IsLocalRing.ResidueField A)]
  {H : Scheme} (f : H ⟶ Spec (.of K)) [Etale f] [IsFinite f]

/-- Construct a finite splitting extension together with a DVR extending the original one. -/
theorem exists_splitting :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
      (_ : Algebra.IsSeparable K L) (B : ValuationSubring L)
      (_ : IsDiscreteValuationRing B) (_ : IsNoetherianRing B)
      (_ : PerfectField (IsLocalRing.ResidueField B)) (φ : A →+* B)
      (n : ℕ) (r : Fin n → (Spec (.of L) ⟶
        pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L))))),
      IsLocalHom φ ∧ (∀ a : A, (φ a : L) = algebraMap K L a) ∧
      B.comap (algebraMap K L) = A ∧
      (∀ a, r a ≫ pullback.snd f _ = 𝟙 _) ∧
      (∀ a, IsOpenImmersion (r a)) ∧
      (∀ x : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme),
        ∃ a z, r a z = x) := by
  obtain ⟨L, hL, aL, finL, _, n, r, hr, hi, hc⟩ :=
    FiniteEtaleRationalCover.exists_cover f
  let _ := hL
  let _ := aL
  let _ := finL
  obtain ⟨B, hdvr, hnoeth, perf, φ, hlocal, hφ, hB⟩ :=
    FiniteExtensionPerfectValuationSubring.exists_extension (L := L) A
  exact ⟨L, hL, aL, finL, inferInstance, B, hdvr, hnoeth, perf, φ, n, r,
    hlocal, hφ, hB, hr, hi, hc⟩

end FLT.Mazur.FiniteEtalePerfectDVRSplitting
