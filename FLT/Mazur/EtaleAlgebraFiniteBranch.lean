/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Finite etale branches of actual etale coordinate algebras

An etale coefficient change and an idempotent localization isolate a finite
etale branch through any prescribed prime. The prime on the localization
contracts to the original prime, and the changed coefficient prime has the
original residue field. No quotient or descent datum is an input.
-/

@[expose] public noncomputable section
open TensorProduct
universe u
namespace FLT.Mazur.EtaleAlgebraFiniteBranch
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The selected idempotent branch remains etale over the changed coefficients. -/
theorem localization_etale [Algebra.Etale A B]
    (C : Type u) [CommRing C] [Algebra A C] (e : C ⊗[A] B) :
    Algebra.Etale C (Localization.Away e) :=
  Algebra.Etale.comp C (C ⊗[A] B) (Localization.Away e)

/-- Isolate a finite etale branch through the prescribed original prime. -/
theorem exists_branch [Algebra.Etale A B] (q : Ideal B) [q.IsPrime] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra.Etale A C)
      (P : Ideal C) (_ : P.IsPrime) (_ : P.LiesOver (q.under A))
      (e : C ⊗[A] B) (_ : IsIdempotentElem e)
      (Q : Ideal (Localization.Away e)) (_ : Q.IsPrime),
      Q.comap ((algebraMap (C ⊗[A] B) (Localization.Away e)).comp
        Algebra.TensorProduct.includeRight.toRingHom) = q ∧
      Q.comap (algebraMap C (Localization.Away e)) = P ∧
      Function.Bijective (Ideal.ResidueField.mapₐ (q.under A) P
        (Algebra.ofId _ _) (P.over_def _)) ∧
      Module.Finite C (Localization.Away e) ∧
      Algebra.Etale C (Localization.Away e) ∧
      ∀ Q' : Ideal (Localization.Away e), Q'.IsPrime →
        Q'.comap (algebraMap C (Localization.Away e)) = P → Q' = Q := by
  obtain ⟨C, hC, hAC, hEt, P, hP, hPq, e, he, P', hP', hP'P,
      hP'q, heP', hres, hfin, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (q.under A) q
  have hd : Disjoint (Submonoid.powers e : Set (C ⊗[A] B)) (P' : Set _) := by
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  let Q := P'.map (algebraMap _ (Localization.Away e))
  let _ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers e) _ _ hP' hd
  have hc : Q.comap (algebraMap _ (Localization.Away e)) = P' :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers e)
      (Localization.Away e) hP' hd
  have hbase : Q.comap (algebraMap C (Localization.Away e)) = P := by
    rw [IsScalarTower.algebraMap_eq C (C ⊗[A] B) (Localization.Away e),
      ← Ideal.comap_comap, hc]
    exact (P'.over_def P).symm
  refine ⟨C, hC, hAC, hEt, P, hP, hPq, e, he, Q, inferInstance,
    ?_, hbase, hres, hfin, localization_etale C e, ?_⟩
  · rw [← Ideal.comap_comap, hc]
    exact hP'q
  · intro Q' hQ' hQ'P
    apply (IsLocalization.orderEmbedding (Submonoid.powers e)
      (Localization.Away e)).injective
    change Q'.comap (algebraMap _ (Localization.Away e)) =
      Q.comap (algebraMap _ (Localization.Away e))
    rw [hc]
    let T := Q'.comap (algebraMap (C ⊗[A] B) (Localization.Away e))
    have hTP : T.LiesOver P := by
      constructor
      change P = (Q'.comap (algebraMap (C ⊗[A] B)
        (Localization.Away e))).comap (algebraMap C (C ⊗[A] B))
      rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
      exact hQ'P.symm
    exact huniq T inferInstance hTP
      (Ideal.notMem_of_isUnit Q' (IsLocalization.Away.algebraMap_isUnit e))

end FLT.Mazur.EtaleAlgebraFiniteBranch
