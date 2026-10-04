/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Flat.FibreRegularSequenceInduction
public import FLT.Mathlib.RingTheory.Flat.LocalizedQuotientFlatness
public import Mathlib.RingTheory.Localization.Submodule

/-! # Relative complete-intersection flatness over a Noetherian algebra -/

@[expose] public noncomputable section

open TensorProduct RingTheory.Sequence

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

namespace Module.Flat

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsNoetherianRing S] [Flat R S]

/-- At a prime of a Noetherian flat algebra, a sequence regular on the local
residue fibre gives a base-flat quotient of that stalk. -/
theorem flat_stalk_quotient_of_fibre_sequence (P : Ideal S) [P.IsPrime] (rs : List S)
    (hrs : IsWeaklyRegular
      (Localization.AtPrime P ⊗[Localization.AtPrime (P.comap (algebraMap R S))]
        (Localization.AtPrime (P.comap (algebraMap R S)) ⧸
          IsLocalRing.maximalIdeal (Localization.AtPrime (P.comap (algebraMap R S)))))
      (rs.map (algebraMap S (Localization.AtPrime P)))) :
    Flat R (Localization.AtPrime P ⧸ (Ideal.ofList rs).map
      (algebraMap S (Localization.AtPrime P))) := by
  let p := P.comap (algebraMap R S)
  let Rp := Localization.AtPrime p
  let Sp := Localization.AtPrime P
  have : IsLocalHom (algebraMap Rp Sp) := by
    rw [Localization.AtPrime.algebraMap_eq p P]
    infer_instance
  have h := (regular_and_flat_quotient_of_fibre_sequence (R := Rp) (S := Sp)
    (N := Sp) (rs.map (algebraMap S Sp)) hrs).2
  have : Flat Rp (Sp ⧸ (Ideal.ofList rs).map (algebraMap S Sp)) := by
    have he : Ideal.ofList (rs.map (algebraMap S Sp)) • (⊤ : Submodule Sp Sp) =
        (Ideal.ofList rs).map (algebraMap S Sp) := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.map_ofList]
    rw [he] at h
    exact h
  exact Flat.trans R Rp _

/-- If the specified equations are regular on every local residue fibre,
their quotient is flat over the original base. -/
theorem flat_quotient_of_local_fibre_sequence (rs : List S)
    (hrs : ∀ (P : Ideal S) [P.IsMaximal], Ideal.ofList rs ≤ P → IsWeaklyRegular
      (Localization.AtPrime P ⊗[Localization.AtPrime (P.comap (algebraMap R S))]
        (Localization.AtPrime (P.comap (algebraMap R S)) ⧸
          IsLocalRing.maximalIdeal (Localization.AtPrime (P.comap (algebraMap R S)))))
      (rs.map (algebraMap S (Localization.AtPrime P)))) :
    Flat R (S ⧸ Ideal.ofList rs) := by
  apply Ideal.flat_quotient_of_localized
  intro P _
  by_cases hP : Ideal.ofList rs ≤ P
  · exact flat_stalk_quotient_of_fibre_sequence P rs (hrs P hP)
  · have he : (Ideal.ofList rs).map (algebraMap S (Localization.AtPrime P)) = ⊤ :=
      IsLocalization.map_eq_top_of_not_subset P.primeCompl (Localization.AtPrime P) (by
        intro hh
        apply hP
        intro x hx
        exact not_not.mp (hh hx))
    rw [he]
    infer_instance

end Module.Flat
