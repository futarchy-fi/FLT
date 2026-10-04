/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Localization.PrincipalPresentationEquiv
public import FLT.Mathlib.RingTheory.Regular.FinitePrincipalIdealCover

/-! # Finite principal presentation covers over arbitrary base rings -/

@[expose] public noncomputable section

namespace AlgHom

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A]

/-- Principal presentations near every target prime give a finite cover by the
actual principal target charts. Equation counts and original coordinates are retained. -/
theorem exists_finite_principal_presentation_cover (f : S →ₐ[R] A)
    (hf : Function.Surjective f) (n : ℕ)
    (h : ∀ (Q : Ideal A) [Q.IsPrime], ∃ (a : S) (rs : List S),
      f a ∉ Q ∧ rs.length = n ∧ (∀ r ∈ rs, f r = 0) ∧
      Ideal.ofList (rs.map (algebraMap S (Localization.Away a))) =
        (RingHom.ker f).map (algebraMap S (Localization.Away a))) :
    ∃ (t : Finset (S ⧸ RingHom.ker f)) (a : t → S) (rs : t → List S),
      Ideal.span (Set.range fun i ↦ f (a i)) = ⊤ ∧
      ∀ i, (rs i).length = n ∧ (∀ r ∈ rs i, f r = 0) ∧
        Ideal.ofList ((rs i).map (algebraMap S (Localization.Away (a i)))) =
          (RingHom.ker f).map (algebraMap S (Localization.Away (a i))) ∧
        ∃ e : (Localization.Away (a i) ⧸
            Ideal.ofList ((rs i).map (algebraMap S (Localization.Away (a i))))) ≃ₐ[R]
            Localization.Away (f (a i)),
          ∀ s : S, e (Ideal.Quotient.mk _ (algebraMap S _ s)) = algebraMap A _ (f s) := by
  let C (a : S) := ∃ rs : List S, rs.length = n ∧ (∀ r ∈ rs, f r = 0) ∧
    Ideal.ofList (rs.map (algebraMap S (Localization.Away a))) =
      (RingHom.ker f).map (algebraMap S (Localization.Away a))
  have hc (P : Ideal S) [P.IsPrime] (hP : RingHom.ker f ≤ P) : ∃ a ∉ P, C a := by
    have : (P.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hP
    obtain ⟨a, rs, ha, hlen, hrs, hgen⟩ := h (P.map f)
    exact ⟨a, fun hp ↦ ha (Ideal.mem_map_of_mem f hp), rs, hlen, hrs, hgen⟩
  obtain ⟨t, a, ha, _, hspan⟩ :=
    (RingHom.ker f).exists_finite_quotient_principal_cover C hc
  choose rs hlen hrs hgen using ha
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  have hspanA : Ideal.span (Set.range fun i ↦ f (a i)) = ⊤ := by
    have hh := congrArg (Ideal.map e.toRingHom) hspan
    rw [Ideal.map_span, ← Set.range_comp, Ideal.map_top] at hh
    exact hh
  exact ⟨t, a, rs, hspanA, fun i ↦ ⟨hlen i, hrs i, hgen i,
    f.exists_principal_presentation_equiv hf (a i) (rs i) (hgen i)⟩⟩

end AlgHom
