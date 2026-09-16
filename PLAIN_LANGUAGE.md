# Plain-language account of the compared theorems

This project formalizes all five main results of arXiv:2502.09871, "An atomic
decomposition of one-dimensional metric currents without boundary" (Chen, Goodman,
Hernandez, Spector), in Lean 4 against Mathlib.

**ApproximationMetric** (paper Theorem 1.1): every boundaryless 1-dimensional metric
current on a complete, separable, geodesic metric space is a limit of finite nonnegative
combinations of closed piecewise-geodesic curves, with total weight at most (1+ε) times
the mass and each curve's Morrey norm at most 2088/ε². The paper's universal constant C
is pinned to the numeral 2088 = 4·522, which is stronger than the paper's existential
form since C is quantified outside the data.

**BBAssertion** (Theorem 4.4): the same current admits a normalized decomposition along a
sequence of closed piecewise-geodesic curves of length at most 2l, with the mass and
length averages both tending to 1.

**SurgeryEta** (Corollary 3.2): a closed piecewise-geodesic curve splits into closed
piecewise-geodesic curves of total length at most (1+η) times the original, each of
Morrey norm at most 522/η². The paper's absolute constant c is pinned to 1/15, shown
sharp at η = 1 for this argument.

**C1SmallBall** (Corollary 2.6): a concatenation of at most k geodesics has Morrey norm
at most 2k. Formalized for an arbitrary metric space, since the proof uses neither
completeness, separability nor ambient geodesy.

**EtaRepeats** (Corollary A.6, psi display): the rescaling identity between the measures
eta_l and eta_1; the psi-tilde display is formalized separately as EtaRepeatsTilde.

Two results the paper cites rather than proves — Ambrosio-Kirchheim Proposition 2.7
(mass supremum formula, hard direction) and Paolini-Stepanov Theorem 3.1 with
Proposition 4.2 (existence of a mass-realizing family of curves) — appear as explicit
hypotheses of Theorems 1.1 and 4.4 rather than as axioms. Corollaries 2.6, 3.2 and A.6
are unconditional. Every declaration depends only on propext, Classical.choice and
Quot.sound.
