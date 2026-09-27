/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone
-/
module

public import FLT.FreyCurve.Basic
public import FLT.EllipticCurve.Torsion
public import FLT.MazurW
import FLT.FreyCurve.Serre.AwayFromP
import FLT.FreyCurve.Serre.FixedLineDescent
import FLT.FreyCurve.Serre.FreyTwoTorsion
import FLT.FreyCurve.Serre.GoodReductionAtPProof
import FLT.FreyCurve.Serre.JoinCoprimeTorsion
import FLT.FreyCurve.Serre.QuotientCurve
import FLT.FreyCurve.Serre.UnramifiedCharacter
/-!

# Irreducibility of the p-torsion of the Frey curve

A deep result of Mazur implies that the Frey curve is irreducible.

-/

@[expose] public section

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

/-- Reducibility of the Frey representation gives the torsion configuration forbidden
by `mazur_W`. Semistability makes one filtration character everywhere unramified,
hence trivial. Its fixed line descends to rational torsion, or its trivial quotient
gives rational torsion on a quotient curve; full two-torsion survives in either case. -/
theorem FreyPackage.mazurW_counterexample_of_reducible (P : FreyPackage) :
    let E := P.freyCurve
    let p := P.p
    have : Fact p.Prime := ⟨P.pp⟩
    ¬ GaloisRep.IsIrreducible (E.galoisRep p P.hppos) →
      ∃ (E' : WeierstrassCurve ℚ) (hE' : E'.IsElliptic),
        letI : E'.IsElliptic := hE'
        ∃ f : ((ZMod 2 × ZMod 2) × ZMod p) →+ (E'⁄ℚ).Point,
          Function.Injective f := by
  dsimp only
  let : Fact P.p.Prime := ⟨P.pp⟩
  intro hred
  obtain ⟨F⟩ := P.filtration_of_reducible hred
  have haway := P.characters_unramified_away F
  have htriv : (∀ g x, F.χ₁ g x = x) ∨ (∀ g x, F.χ₂ g x = x) := by
    rcases P.one_character_unramified_at_p_of_goodReduction
        (goodReductionAtPQuotient P.p P.pp P.hp5) F with h₁ | h₂
    · left
      apply GaloisRep.trivial_of_everywhere_unramified F.χ₁
      intro q hq
      by_cases heq : q = P.p
      · subst q
        exact h₁
      · exact (haway q hq heq).1
    · right
      apply GaloisRep.trivial_of_everywhere_unramified F.χ₂
      intro q hq
      by_cases heq : q = P.p
      · subst q
        exact h₂
      · exact (haway q hq heq).2
  obtain ⟨f₂, hf₂⟩ := P.frey_full_two_torsion
  have hcoprime : Nat.Coprime 2 P.p := Nat.coprime_two_left.mpr P.hp_odd
  rcases htriv with h₁ | h₂
  · obtain ⟨fₚ, hfₚ⟩ := rational_torsion_of_fixed_line P.freyCurve P.p
      F.i F.i_injective (fun g x ↦ (F.i_equivariant g x).trans (congrArg F.i (h₁ g x)))
    exact ⟨P.freyCurve, inferInstance, SerrePlan.join_coprime_torsion hcoprime f₂ hf₂ fₚ hfₚ⟩
  · obtain ⟨E', hE', φ, fₚ, hker, hfₚ⟩ :=
      quotient_curve_of_trivial_quotient P.freyCurve P.p P.hppos
        (by have := P.hp5; omega) F.q F.q_surjective
        (fun g v ↦ (F.q_equivariant g v).trans (h₂ g (F.q v)))
    let : E'.IsElliptic := hE'
    obtain ⟨g₂, hg₂⟩ := fullTwoTorsion_survives_of_kernel_killed hcoprime f₂ hf₂ φ hker
    exact ⟨E', hE', SerrePlan.join_coprime_torsion hcoprime g₂ hg₂ fₚ hfₚ⟩

/--
For exponent at least `17`, the p-torsion in the Frey curve associated to a
counterexample to FLT is irreducible.
-/
theorem FreyPackage.mazur (P : FreyPackage) (hp17 : 17 ≤ P.p) :
    let E := P.freyCurve
    let p := P.p
    have : Fact p.Prime := ⟨P.pp⟩
    GaloisRep.IsIrreducible (E.galoisRep p P.hppos) := by
  by_contra hred
  obtain ⟨E', hE', f, hf⟩ := P.mazurW_counterexample_of_reducible hred
  let : E'.IsElliptic := hE'
  exact mazur_W P.p P.pp hp17 E' ⟨f, hf⟩
