/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.Contracts

/-!
# The two-cusp collision argument

If specialization is injective on sections of a target, two sections of the
source with equal reductions have equal projected sections. Applying this at
two allowed primes forces a section reducing to opposite cusps to have both
projected cusp sections as its image. Restriction to the generic point then
contradicts `G2Cusps`.

This proves the conditional consumer L03 of `docs/MAZUR_CONTRACTS.md`. The
integral data and both G2 properties remain explicit inputs. In particular,
the argument constructs neither the modular curve nor the Eisenstein quotient.
The final theorem uses the canonical residue maps from `IntegralBase`.

Source: Mazur, *Modular curves and the Eisenstein ideal* (1977), III §5,
pp. 159–160.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur

namespace QuotientData

variable {p : ℕ} {D : IntegralData p} (Q : QuotientData D)

/-- Equal reductions at an allowed prime identify the projected sections. -/
theorem map_sections_eq_of_specialization (hsp : G2Specialization Q)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (s : Spec (CommRingCat.of (ZMod q)) ⟶ Base p) {x y : Sections D.X}
    (h : s ≫ x.left = s ≫ y.left) :
    Sections.map Q.projection x = Sections.map Q.projection y := by
  apply hsp q hq hq2 hqp s
  simpa only [Sections.map_left, Category.assoc] using
    congrArg (fun z => z ≫ Q.projection.left) h

/-- The over-category form of specialization gives the same section equality. -/
theorem map_sections_eq_of_restrict (hsp : G2Specialization Q)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (s : Spec (CommRingCat.of (ZMod q)) ⟶ Base p) {x y : Sections D.X}
    (h : Sections.restrict s x = Sections.restrict s y) :
    Sections.map Q.projection x = Sections.map Q.projection y :=
  Q.map_sections_eq_of_specialization hsp hq hq2 hqp s
    (congrArg (fun z => z.left) h)

/-- Distinct generic cusp images imply distinct integral projected cusp sections. -/
theorem map_cusps_ne (hc : G2Cusps Q) :
    Sections.map Q.projection D.cuspZero ≠
      Sections.map Q.projection D.cuspInfinity := by
  intro h
  apply hc
  simpa only [Sections.restrict_map, genericSection, onGeneric, Points.map] using
    congrArg (Sections.restrict D.generic) h

/-- No section reduces to infinity at one allowed prime and zero at another.
The two primes need not be distinct for this implication. -/
theorem no_two_cusp_collision (hc : G2Cusps Q) (hsp : G2Specialization Q)
    {r q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrp : r ≠ p)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (sr : Spec (CommRingCat.of (ZMod r)) ⟶ Base p)
    (sq : Spec (CommRingCat.of (ZMod q)) ⟶ Base p) (x : Sections D.X)
    (hinf : sr ≫ x.left = sr ≫ D.cuspInfinity.left)
    (hzero : sq ≫ x.left = sq ≫ D.cuspZero.left) : False := by
  have hi := Q.map_sections_eq_of_specialization hsp hr hr2 hrp sr hinf
  have hz := Q.map_sections_eq_of_specialization hsp hq hq2 hqp sq hzero
  exact Q.map_cusps_ne hc (hz.symm.trans hi)

/-- The collision consumer at three, stated with scheme-morphism equalities. -/
theorem no_cusp_collision_at_three (hc : G2Cusps Q) (hsp : G2Specialization Q)
    (hp : p.Prime) (hp17 : 17 ≤ p) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) (x : Sections D.X)
    (hinf : IntegralBase.residueThree hp hp17 ≫ x.left =
      IntegralBase.residueThree hp hp17 ≫ D.cuspInfinity.left)
    (hzero : IntegralBase.residue hp hq hq2 hqp ≫ x.left =
      IntegralBase.residue hp hq hq2 hqp ≫ D.cuspZero.left) : False :=
  Q.no_two_cusp_collision hc hsp (by decide) (by decide) (by omega)
    hq hq2 hqp _ _ x hinf hzero

/-- A section specializing to infinity at three cannot specialize to zero at
any allowed prime, with both specializations expressed as over-category points. -/
theorem residue_ne_zero_of_residueThree_eq_infinity
    (hc : G2Cusps Q) (hsp : G2Specialization Q) (hp : p.Prime) (hp17 : 17 ≤ p)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) (x : Sections D.X)
    (hinf : IntegralBase.residueThreeSection hp hp17 x =
      IntegralBase.residueThreeSection hp hp17 D.cuspInfinity) :
    IntegralBase.residueSection hp hq hq2 hqp x ≠
      IntegralBase.residueSection hp hq hq2 hqp D.cuspZero := by
  intro hzero
  exact Q.no_cusp_collision_at_three hc hsp hp hp17 hq hq2 hqp x
    (congrArg (fun z => z.left) hinf) (congrArg (fun z => z.left) hzero)

end QuotientData

end FLT.Mazur
