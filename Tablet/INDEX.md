# Tablet Index

| Name | Env | Kind | Status | Labels | Title | Imports |
|------|-----|------|--------|--------|-------|---------|
| ApproximationMetric | theorem | proof | closed | approximationMetric | Paper Theorem 1.1 | BBAssertion, BoundaryZero, GeodesicPairing, IsClosedCurve, IsPiecewiseGeodesic, MetricCurrent1, SurgeryEta, curveCurrent, curveMeasure, morreyNorm |
| ArcDeltaEpsNCount | lemma | proof | closed | - | A sub-window of the arc's own resolution, avoiding its truncated end edges, inherits $(\delta,\epsilon,n)$-ness | ArcGeodesicResolution, ClampedLinearShortEdgeCount, IsDeltaEpsN, RestrictPiecewiseGeodesic, ShiftedBreakpointShortEdgeCount, SplicedBreakpointShortEdgeCount, curveArc |
| ArcGeodesicResolution | lemma | proof | closed | - | A circular arc inherits a geodesic resolution with the truncated edges first and last | ConcatGeodesicResolution, IsGeodesicResolution, RestrictGeodesicResolutionTruncated, curveArc |
| ArcLocalization | helper | proof | closed | - | Interval localization of a circle-distance ball | dGamma |
| ArcShortWindowEdgeCount | lemma | proof | closed | - | A short interior window of the arc's own resolution bounds its edge count | IsGeodesicResolution, ShiftedBreakpointShortEdgeCount, ShortWindowAtMostOneLongEdge, SplicedBreakpointShortEdgeCount, curveArc |
| BBAssertion | theorem | proof | closed | bbassertion | Paper Theorem 4.4 | BBSamplingDiagonal, BoundaryZero, ClosingUp, DiagonalizationGeneral, EasyEstimateForMass, GeodesicPairing, IsClosedCurve, IsPiecewiseGeodesic, MassFamilyBound, MassPosOfNonzero, MassSupFormula, MetricCurrent1, PSFamily, PaoliniStepanovExists, curveCurrent |
| BBSamplingDiagonal | lemma | proof | closed | BBSamplingDiagonal | The remaining diagonal extraction, at the unsampled curves | CountableDiagonalExtraction, CurveScaledEvalMeasurable, EtaRepeats, EtaRepeatsTilde, PsiMeasurable, PsiTildeMeasurable, PsiTildeUniformBound, PsiUniformBound, SLLNCurves, psi, psiTilde |
| BasicCut | definition | definition | closed | - | Basic cut $C(\gamma,t,t')$ | GeodesicPairing, IsClosedCurve, curveArc, curveConcat |
| BasicCutClosed | lemma | proof | closed | - | The basic cut's outputs are closed and piecewise geodesic | ArcGeodesicResolution, BasicCut, BasicCutDiscardedResolutionGeneral, CurveConcatEndpoints, GeodesicPairing, IsClosedCurve, IsGeodesicOn, IsGeodesicResolution, IsPiecewiseGeodesic, curveArc, curveConcat, curveRestrict, curveWrapRestrict |
| BasicCutCurrent | lemma | proof | closed | - | The basic cut splits the current additively | BasicCut, CurrentConcatAdditive, CurrentResolutionAdditive, CurrentReverse, GeodesicPairing, RestrictCurrentFormula, curveArc, curveCurrent, curveRestrict, curveWrapRestrict |
| BasicCutDiscardedEval | lemma | proof | closed | eq:discarded-eval-len, eq:discarded-eval-agree, eq:discarded-eval-geo | Pointwise description of the discarded output of a basic cut | BasicCut, CurveConcatEndpoints, GeodesicPairing, IsClosedCurve, IsGeodesicOn, curveArc, curveConcat, curveRestrict, curveWrapRestrict |
| BasicCutDiscardedResolution | lemma | proof | closed | - | The basic cut's discarded arc, at resolution breakpoints, has an exact resolution | BasicCut, ConcatGeodesicResolution, CurveConcatEndpoints, GeodesicIsPiecewiseGeodesic, IsPiecewiseGeodesicWith, RestrictPiecewiseGeodesic, curveRestrict, curveWrapRestrict |
| BasicCutDiscardedResolutionGeneral | lemma | proof | closed | - | The basic cut's discarded arc, at arbitrary cut points, has an exact resolution | BasicCut, ConcatGeodesicResolution, GeodesicIsPiecewiseGeodesic, IsPiecewiseGeodesicWith, curveArc, curveConcat, curveRestrict, curveWrapRestrict |
| BasicCutLength | lemma | proof | closed | eq:kept-len, eq:discarded-len, eq:closing-le-arc | The basic cut's outputs have controlled lengths | BasicCut, CurveLipschitz, curveConcat, curveRestrict, curveWrapRestrict |
| BasicCutResolutionAtBreakpoints | lemma | proof | closed | - | The basic cut's kept arc, at resolution breakpoints, has a controlled small-edge count | BasicCut, ConcatGeodesicResolution, ConcatResolutionShortEdgeCount, CurveConcatEndpoints, GeodesicIsPiecewiseGeodesic, RestrictPiecewiseGeodesic, SubResolutionShortEdgeCount, curveRestrict, curveWrapRestrict, smallPieceCount |
| BasicCutResolutionGeneral | lemma | proof | closed | - | The basic cut's kept arc, at arbitrary cut points, has a controlled small-piece count | ArcGeodesicResolution, BasicCut, ConcatGeodesicResolution, CurveConcatEndpoints, GeodesicIsPiecewiseGeodesic, IsPiecewiseGeodesic, ShiftedBreakpointShortEdgeCount, SplicedBreakpointShortEdgeCount, curveRestrict, curveWrapRestrict, smallPieceCount |
| BigEdgeWindowPacking | helper | proof | closed | - | Packing bound for long edges fully inside a window | Preamble |
| BoundaryZero | definition | definition | closed | - | Boundary-zero condition $\partial T = 0$ | Form1 |
| C1SmallBall | corollary | proof | closed | C1-small-ball | C1-small-ball | GeodesicMorreyLeTwo, IsPiecewiseGeodesicWith, MorreyResolutionAdditive, MorreySubadditive |
| ClampedLinearShortEdgeCount | helper | proof | closed | - | The linear counting clause holds at unclamped windows | Preamble |
| ClosingUp | lemma | proof | closed | ClosingUp | Closing the loops | ConcatPiecewiseGeodesic, CurrentConcatAdditive, CurrentReverse, CurveConcatEndpoints, CurveCurrentBound, CurveLipschitz, GeodesicIsPiecewiseGeodesic, GeodesicPairing, GeodesicSampledCurrent, IsClosedCurve, IsPiecewiseGeodesicWith, PSFamily, SamplingEndpoints, SamplingPiecewiseGeodesic, curveConcat, curveCurrent, curveSampling |
| ConcatGeodesicResolution | lemma | proof | closed | - | Gluing two geodesic resolutions across a matched endpoint, with the glued resolution named | IsGeodesicResolution, curveConcat |
| ConcatPiecewiseGeodesic | lemma | proof | closed | - | Concatenation of piecewise geodesics is piecewise geodesic, with edge counts adding | IsPiecewiseGeodesicWith, curveConcat |
| ConcatResolutionShortEdgeCount | lemma | proof | closed | - | Short-edge counts are additive across a glued resolution | Preamble |
| ConeInterpolation | lemma | proof | closed | - | Truncated cone functions: bounds, and finite Lipschitz interpolation | Preamble |
| CountableDiagonalExtraction | lemma | proof | closed | - | Countable diagonal extraction | Preamble |
| CurrentChordEstimate | lemma | proof | closed | - | Chord estimate for the current of a curve | CurveCurrentBound |
| CurrentConcatAdditive | lemma | proof | closed | - | Additivity of $[[\gamma | CurveLipschitz, curveConcat, curveCurrent |
| CurrentContinuousF | lemma | proof | closed | CurrentContinuousF | Continuity of a metric $1$-current with respect to pointwise convergence of $f$ | MetricCurrent1 |
| CurrentFormAddF | lemma | proof | closed | CurrentFormAddF | Additivity of $[[\gamma | CurveLipschitz, curveCurrent |
| CurrentFormAddPi | lemma | proof | closed | CurrentFormAddPi | Additivity of $[[\gamma | CurveLipschitz, curveCurrent |
| CurrentResolutionAdditive | lemma | proof | closed | - | Additivity of $[[\gamma | CurveLipschitz, IsGeodesicResolution, curveCurrent |
| CurrentReverse | lemma | proof | closed | - | Reversal negates the current | curveCurrent |
| CurrentTwoFormEstimate | lemma | proof | closed | - | Two-slot perturbation estimate for $[[\gamma | CurrentFormAddF, CurrentFormAddPi, PiBoundsF, PiBoundsPi, curveCurrent, psi, psiTilde |
| Curve | definition | definition | closed | - | $\Theta(E)$, arc-length normal form | Preamble |
| CurveArcEval | lemma | proof | closed | curve-arc-eval | Arc-to-ambient evaluation dictionary | curveArc |
| CurveConcatEndpoints | lemma | proof | closed | - | Concatenation preserves the outer endpoints | curveConcat |
| CurveCurrentBound | lemma | proof | closed | - | Elementary bound on the current of a curve | CurveLipschitz, curveCurrent |
| CurveCurrentMeasurable | lemma | proof | closed | - | Measurability of the current in the curve | CurrentChordEstimate, CurrentResolutionAdditive, CurveCurrentBound, CurveScaledEvalMeasurable, Form1, RestrictCurrentFormula, curveCurrent, curveRestrict |
| CurveEvalJointMeasurable | helper | proof | closed | - | Trajectory evaluation is jointly measurable | CurveLipschitz, CurveMeasurableSpace |
| CurveLenMeasurable | helper | proof | closed | - | Length is measurable | CurveMeasurableSpace |
| CurveLipschitz | lemma | proof | closed | - | Global $1$-Lipschitz extension | Curve |
| CurveMeasurableSpace | lemma | proof | closed | - | $\Theta(E)$ carries the evaluation $\sigma$-algebra | Curve, CurveLipschitz, curveRestrictTot |
| CurveRestrictTotAgrees | helper | proof | closed | - | Total restriction agrees with the proof-carrying one | curveRestrict, curveRestrictTot |
| CurveRestrictTotMeasurable | helper | proof | closed | - | The total restriction map is measurable | CurveEvalJointMeasurable, CurveLenMeasurable, CurveMeasurableSpace, curveRestrictTot |
| CurveScaledEvalMeasurable | helper | proof | closed | - | Evaluation at a length-proportional point is measurable | CurveEvalJointMeasurable, CurveLenMeasurable |
| CutTypeI | lemma | proof | closed | cut-type-I, eq:SameSumTypeI, eq:MorreyTypeI, eq:LengthBoundTypeIgamma, eq:LengthBoundTypeItotal, eq:SmallCountBoundTypeI | Type I cut operation | ArcDeltaEpsNCount, ArcGeodesicResolution, ArcShortWindowEdgeCount, BasicCut, BasicCutClosed, BasicCutCurrent, BasicCutDiscardedEval, BasicCutDiscardedResolutionGeneral, BasicCutLength, BasicCutResolutionGeneral, C1SmallBall, Form1, FullBallLem, GeodesicMorreyLeTwo, GeodesicPairing, IsClosedCurve, IsDeltaEpsN, IsLSI, IsPiecewiseGeodesic, MorreyResolutionAdditive, MorreySubadditive, RestrictFullIsSelf, RestrictLSI, RestrictMeasureFormula, RestrictPiecewiseGeodesic, TypeICutPointExists, curveArc, curveConcat, curveCurrent, curveMeasure, curveRestrict, curveWrapRestrict, dGamma, morreyNorm, smallPieceCount |
| CutTypeII | lemma | proof | closed | cut_II, eq:SameSumTypeII, eq:MorreyTypeII, eq:LengthBoundTypeIIgamma, eq:LengthBoundTypeIItotal, eq:SmallCountBoundTypeII | Type II cut operation | BasicCut, BasicCutClosed, BasicCutCurrent, BasicCutDiscardedResolution, BasicCutLength, BasicCutResolutionAtBreakpoints, C1SmallBall, DeltaEpsNFailureAtBreakpoints, curveCurrent, curveMeasure, smallPieceCount |
| DGammaBallMeasure | helper | proof | closed | - | Circle-distance ball has measure at most $2\rho$ | dGamma |
| DeltaEpsNFailureAtBreakpoints | lemma | proof | closed | eq:exact-n1, eq:total-bound, eq:arc-length | Failure of $(\delta,\epsilon,n)$-ness produces a controlled violating window at breakpoints | BigEdgeWindowPacking, IsDeltaEpsN, IsPiecewiseGeodesic, MinimizingResolutionStrict |
| DiagonalizationGeneral | lemma | proof | closed | DiagonalizationGeneral | Diagonalization at every $1$-form | CurrentContinuousF, CurrentFormAddF, CurrentFormAddPi, CurrentTwoFormEstimate, LipschitzSeparable, MetricCurrent1, PSFamily, PiBoundsF, PiBoundsPi, PsiVanishes, curveCurrent, psi, psiTilde |
| EasyEstimateForMass | lemma | proof | closed | - | Easy estimate for mass | CurveCurrentBound, CurveLipschitz, curveCurrent, curveMeasure, massOfFunctional |
| EtaRepeats | corollary | proof | closed | etaRepeats-psi | $\overline{\eta}_l$ repeats $\overline{\eta}_1$, $\psi$ display | CurveLenMeasurable, CurveRestrictTotAgrees, CurveRestrictTotMeasurable, CurveScaledEvalMeasurable, PSFamily, PsiMeasurable, PsiReindex, curveRestrict, psi |
| EtaRepeatsTilde | corollary | proof | closed | - | $\overline{\eta}_l$ repeats $\overline{\eta}_1$, $\tilde\psi$ display | CurveLenMeasurable, CurveRestrictTotAgrees, CurveRestrictTotMeasurable, CurveScaledEvalMeasurable, EtaRepeats, PSFamily, PsiReindex, PsiReindexTilde, PsiTildeMeasurable, curveRestrict, psiTilde |
| Form1 | definition | definition | closed | - | $\mathcal{D}^1(E)$, metric $1$-forms | Preamble |
| FullBallLem | lemma | proof | closed | full-ball-lem | Full-ball estimate | ArcLocalization, BigEdgeWindowPacking, C1SmallBall, DGammaBallMeasure, IsDeltaEpsN, LargeBallLem, ResolutionCoverBallMeasure, StraddleAtMostOneEdge, morreyNorm |
| GeodesicIsPiecewiseGeodesic | lemma | proof | closed | - | A geodesic pairing's geodesic is a one-edge piecewise geodesic | GeodesicPairing, IsPiecewiseGeodesicWith |
| GeodesicMorreyLeTwo | lemma | proof | closed | - | Ball growth for a geodesic edge | CurveLipschitz, IsGeodesicOn, curveMeasure, morreyNorm |
| GeodesicPairing | definition | definition | closed | - | Geodesic pairing $G_{x,y}$ | IsGeodesicOn |
| GeodesicSampledCurrent | lemma | proof | closed | - | Quantitative convergence of the piecewise-geodesic sampling | CurrentChordEstimate, CurrentConcatAdditive, CurrentResolutionAdditive, CurveLipschitz, RestrictCurrentFormula, curveCurrent, curveRestrict, curveSampling |
| InitialDeltaExists | lemma | proof | closed | - | Existence of a starting scale with no small edges | IsClosedCurve, IsDeltaEpsN, IsPiecewiseGeodesic, StrictResolutionExists, smallPieceCount |
| IsAdmissible | definition | definition | closed | - | Admissible measure for a $1$-dimensional functional | Form1 |
| IsClosedCurve | definition | definition | closed | - | Closed curve | Curve |
| IsDeltaEpsN | definition | definition | closed | - | $(\delta,\epsilon,n)$-curve, $\Xden(\delta,\epsilon,n)$ | IsClosedCurve, IsGeodesicResolution |
| IsGeodesicOn | definition | definition | closed | - | Geodesic on a subinterval | Curve |
| IsGeodesicResolution | definition | definition | closed | - | Resolution into geodesic edges | IsGeodesicOn |
| IsLSI | definition | definition | closed | - | $(\delta,\epsilon)$-large-scale invertibility, $\Xlsi(\delta,\epsilon)$ | IsPiecewiseGeodesic, dGamma |
| IsPiecewiseGeodesic | definition | definition | closed | - | Piecewise geodesic curve, $\Xgeo$ | IsPiecewiseGeodesicWith |
| IsPiecewiseGeodesicWith | definition | definition | closed | - | Piecewise geodesic with $k$ pieces | IsGeodesicResolution |
| LargeBallLem | lemma | proof | closed | large-ball-lem | Large-ball estimate | CurveLipschitz, DGammaBallMeasure, IsLSI, curveMeasure |
| LipschitzSeparable | lemma | proof | closed | - | Lemma A.1, Lipschitz separability, bound idiom | ConeInterpolation, RationalCompatibleValues |
| MassFamilyBound | lemma | proof | closed | - | Ambrosio--Kirchheim mass-supremum formula, easy direction, finite form | MetricCurrent1, massOfFunctional |
| MassPosOfNonzero | lemma | proof | closed | - | Mass of a nonzero functional is nonzero | MetricCurrent1, massOfFunctional |
| MassSupFormula | lemma | proof | open | - | Ambrosio--Kirchheim mass-supremum formula, hard direction, finite form | MetricCurrent1 |
| MetricCurrent1 | definition | definition | closed | - | Metric $1$-current $\mathcal{M}_1(E)$ | massOfFunctional |
| MinimizingResolutionStrict | lemma | proof | closed | - | A minimizing resolution has no degenerate edges | smallPieceCount |
| MorreyResolutionAdditive | lemma | proof | closed | - | Additivity of $\mu_\gamma$ over a resolution | CurveLipschitz, IsGeodesicResolution, curveMeasure |
| MorreySubadditive | lemma | proof | closed | - | Finite subadditivity of the Morrey norm | morreyNorm |
| PSFamily | definition | definition | closed | - | Paolini--Stepanov family for $T$ | CurveMeasurableSpace, ThetaL, curveRestrictTot |
| PaoliniStepanovExists | lemma | proof | open | - | Paolini--Stepanov family, with the bridging mass identity | BoundaryZero, MetricCurrent1, PSFamily |
| PartitionChordSum | lemma | proof | closed | - | Riemann--Stieltjes partition sum with arbitrary sample points | CurrentChordEstimate, CurrentResolutionAdditive, RestrictCurrentFormula, curveCurrent, curveRestrict |
| PiBoundsF | lemma | proof | closed | - | Lemma A.2, $f$-perturbation estimate | CurrentChordEstimate, CurrentResolutionAdditive, PartitionChordSum, RestrictCurrentFormula, curveCurrent, curveRestrict, psiTilde |
| PiBoundsPi | lemma | proof | closed | - | Lemma A.2, $\pi$-perturbation estimate | CurrentChordEstimate, CurrentResolutionAdditive, PartitionChordSum, RestrictCurrentFormula, curveCurrent, curveRestrict, psi |
| Preamble | preamble | preamble | closed | - | - | - |
| PsiMeasurable | lemma | proof | closed | - | Measurability of $\psi$ | CurveLenMeasurable, CurveScaledEvalMeasurable, psi |
| PsiReindex | helper | proof | closed | - | Reindexing identity for $\psi$ | CurveRestrictTotAgrees, curveRestrictTot, psi |
| PsiReindexTilde | helper | proof | closed | - | Reindexing identity for $\tilde\psi$ | CurveRestrictTotAgrees, PsiReindex, curveRestrictTot, psiTilde |
| PsiTildeMeasurable | lemma | proof | closed | - | Measurability of $\tilde\psi$ | CurveLenMeasurable, CurveScaledEvalMeasurable, psiTilde |
| PsiTildeUniformBound | lemma | proof | closed | - | A priori bound on $\tilde\psi$ | psiTilde |
| PsiUniformBound | lemma | proof | closed | - | A priori bound on $\psi$ | psi |
| PsiVanishes | lemma | proof | closed | - | Lemma A.3, $\psi$-vanishing, threshold form | PsiMeasurable, PsiTildeMeasurable, psi, psiTilde |
| RationalCompatibleValues | lemma | proof | closed | - | Compatible rational approximation of a Lipschitz function on a finite set | Preamble |
| ResolutionCoverBallMeasure | helper | proof | closed | - | Covering by finitely many geodesic edges bounds a ball's measure | CurveLipschitz, GeodesicMorreyLeTwo, IsGeodesicResolution, curveMeasure, morreyNorm |
| RestrictCurrentFormula | lemma | proof | closed | - | The current of a restriction, as an un-reparametrized integral | CurrentConcatAdditive, curveCurrent, curveRestrict |
| RestrictDeltaEpsNAtBreakpoints | lemma | proof | closed | - | Restricting to a window between two resolution breakpoints preserves $(\delta,\epsilon,n)$-ness | IsDeltaEpsN, RestrictPiecewiseGeodesic |
| RestrictFullIsSelf | lemma | proof | closed | - | Restricting to the full domain is the identity | curveRestrict |
| RestrictGeodesicResolutionTruncated | lemma | proof | closed | - | A restriction to an arbitrary window inherits a geodesic resolution with only its two end edges truncated | IsGeodesicResolution, curveRestrict |
| RestrictLSI | lemma | proof | closed | - | Large-scale invertibility passes from a window to a non-closed sub-window | IsLSI, IsPiecewiseGeodesic, curveRestrict |
| RestrictMeasureFormula | lemma | proof | closed | - | The measure of a restriction, as a pushforward on the original interval | CurveLipschitz, curveMeasure, curveRestrict |
| RestrictPiecewiseGeodesic | lemma | proof | closed | - | Restricting to a window between two resolution breakpoints stays piecewise geodesic | IsGeodesicResolution, curveRestrict |
| SLLNCurves | lemma | proof | closed | SLLNCurves | Strong law of large numbers for a Paolini--Stepanov family, single stage | CurveCurrentBound, CurveCurrentMeasurable, CurveLenMeasurable, PSFamily, SamplingRealizesAverages, ThetaL |
| SamplingEndpoints | lemma | proof | closed | - | Piecewise-geodesic sampling preserves endpoints | curveSampling |
| SamplingPiecewiseGeodesic | lemma | proof | closed | - | Piecewise-geodesic sampling produces a piecewise geodesic curve | ConcatPiecewiseGeodesic, GeodesicIsPiecewiseGeodesic, IsPiecewiseGeodesic, curveSampling |
| SamplingRealizesAverages | lemma | proof | closed | - | Sampling realizes countably many strong-law averages at once | Preamble |
| ShiftedBreakpointShortEdgeCount | helper | proof | closed | - | Windowed short-edge count transported along an affine reindexing of breakpoints | Preamble |
| ShortWindowAtMostOneLongEdge | helper | proof | closed | - | At most one long edge fits inside a short window | Preamble |
| SplicedBreakpointShortEdgeCount | helper | proof | closed | - | Windowed short-edge count transported across a splice of two affine reindexings | Preamble |
| StraddleAtMostOneEdge | helper | proof | closed | - | A point lies in the interior of at most one edge | Preamble |
| StrictResolutionExists | lemma | proof | closed | - | Strict resolutions exist | IsGeodesicResolution, IsPiecewiseGeodesic, MinimizingResolutionStrict, smallPieceCount |
| SubResolutionShortEdgeCount | lemma | proof | closed | - | Short-edge counts transport exactly along a shifted sub-resolution | Preamble |
| SurgeryEta | corollary | proof | closed | surgery-eta, eq:SurgeryEtaCurrent, eq:SurgeryEtaLength, eq:SurgeryEtaMorrey | Surgery, sharp $\eta$ form | Curve, Form1, GeodesicPairing, IsClosedCurve, IsPiecewiseGeodesic, SurgeryLem, curveCurrent, curveMeasure, morreyNorm |
| SurgeryInduction | lemma | proof | closed | surgery-induction, eq:SurgeryIndCurrent, eq:SurgeryIndLength, eq:SurgeryIndMorrey | Surgery induction | Curve, CutTypeI, CutTypeII, Form1, FullBallLem, GeodesicPairing, IsClosedCurve, IsDeltaEpsN, IsLSI, IsPiecewiseGeodesic, SurgeryStepTypeI, SurgeryStepTypeII, curveCurrent, curveMeasure, morreyNorm, smallPieceCount, surgeryPotential |
| SurgeryLem | lemma | proof | closed | surgery-lem, eq:SurgeryLemCurrent, eq:SurgeryLemLength, eq:SurgeryLemMorrey | Surgery | Curve, Form1, GeodesicPairing, InitialDeltaExists, IsClosedCurve, IsPiecewiseGeodesic, SurgeryInduction, curveCurrent, curveMeasure, morreyNorm, smallPieceCount, surgeryPotential |
| SurgeryStepTypeI | helper | proof | closed | eq:StepI-measure, eq:StepI-length | Amortization step for a Type I cut | surgeryPotential |
| SurgeryStepTypeII | helper | proof | closed | eq:StepII-measure, eq:StepII-length | Amortization step for a Type II cut | surgeryPotential |
| ThetaL | definition | definition | closed | - | $\Theta_l(E)$ | curveCurrent, massOfFunctional |
| TypeICutMinimalPair | lemma | proof | closed | typeI-cut-minimal-pair | The Type~I infimum is attained, at a pair of at most half the total length | CurveLipschitz, dGamma |
| TypeICutPointExists | lemma | proof | closed | typeI-cut-point-exists | Existence of the Type~I cut point | ArcGeodesicResolution, CurveArcEval, CurveLipschitz, IsLSI, TypeICutMinimalPair, curveArc, dGamma |
| curveArc | definition | definition | closed | - | Circular arc $\gamma|_{[t,t' | IsClosedCurve, curveRestrict, curveWrapRestrict |
| curveConcat | definition | definition | closed | - | Concatenation $\gamma_1 * \gamma_2$ | Curve |
| curveCurrent | definition | definition | closed | - | $[[\gamma | Curve, Form1 |
| curveMeasure | definition | definition | closed | - | $\mu_\gamma$, the measure of a curve | Curve |
| curveRestrict | definition | definition | closed | - | Restriction $\gamma|_{[a,b | Curve |
| curveRestrictTot | definition | definition | closed | - | Total restriction $\gamma|^{\mathrm{tot}}_{[a,b | curveRestrict |
| curveSampling | definition | definition | closed | - | Piecewise-geodesic sampling $\gamma^\delta$ | GeodesicPairing, curveConcat |
| curveWrapRestrict | definition | definition | closed | - | Wrap-around restriction $\gamma|_{[t,t' | IsClosedCurve, curveConcat, curveRestrict |
| dGamma | definition | definition | closed | - | Circle distance $d_\gamma$ | Curve, IsClosedCurve |
| massOfFunctional | definition | definition | closed | - | Mass $\mathbb{M}(T)$, as an infimum | IsAdmissible |
| morreyNorm | definition | definition | closed | - | Morrey norm of a measure | Preamble |
| psi | definition | definition | closed | - | $\psi_{m,Q,\epsilon,C}$ | Curve |
| psiTilde | definition | definition | closed | - | $\tilde\psi_{m,Q,\epsilon,C}$ | Curve |
| smallPieceCount | definition | definition | closed | - | Number of small pieces, $\nsmallpieces(\gamma,\delta)$ | IsGeodesicResolution |
| surgeryPotential | definition | definition | closed | surgery-potential | Surgery potential, $\mathrm{surgeryPotential}(\epsilon,\delta,n,L,m)$ | Preamble |

**Total:** 132 nodes | **Closed:** 130 | **Open:** 2
