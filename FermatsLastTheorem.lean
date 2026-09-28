import FLT -- import the project files

/-!

# Fermat's Last Theorem

There are many ways of stating Fermat's Last Theorem.
In this file, we give the traditional statement using
the positive integers `ℕ+`, using the three-input assembly.
The remaining arithmetic inputs are Mazur's rational torsion bound,
integral lifting, and compatible families. The three-adic trace input
is supplied by the proved sorting and character-purity results.

-/

/-- Fermat's Last Theorem for positive naturals. -/
theorem PNat.pow_add_pow_ne_pow
    (x y z : ℕ+)
    (n : ℕ) (hn : n > 2) :
    x^n + y^n ≠ z^n :=
  PNat.pow_add_pow_ne_pow_of_three_inputs
    FLT.Assembly.mazurTorsionExclusion FLT.Assembly.hardlyRamifiedLifting
    FLT.Assembly.hardlyRamifiedCompatibleFamilies x y z n hn

/--
info: 'PNat.pow_add_pow_ne_pow' depends on axioms:
[Mazur_statement, propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PNat.pow_add_pow_ne_pow

-- The EPSRC-funded phase of the FLT project (formalize FLT modulo results known in the 1980s)
-- will be complete when `sorryAx` is no longer mentioned in the output of this last command.
