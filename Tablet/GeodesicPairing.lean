import Tablet.IsGeodesicOn

open Set

-- [TABLET NODE: GeodesicPairing]
/-- A choice, for every ordered pair `(x,y)` of points of `E`, of a geodesic `G x y` of length
`dist x y` from `x` to `y`, such that `G y x` is the reversal of `G x y` (paper eq. (2.5) and the
surrounding discussion, lines 517--526). The paper notes that constructing such a family
simultaneously for all pairs may require the axiom of choice; accordingly this is packaged as a
hypothesis carrier rather than derived from a bare geodesic-space assumption on `E`. -/
structure GeodesicPairing (E : Type*) [MetricSpace E] where
-- BODY
  G : E → E → Curve E
  len_eq : ∀ x y : E, (G x y).len = dist x y
  start_eq : ∀ x y : E, (G x y).toFun 0 = x
  end_eq : ∀ x y : E, (G x y).toFun (G x y).len = y
  isGeodesic : ∀ x y : E, IsGeodesicOn (G x y) 0 (G x y).len
  reversal : ∀ x y : E, ∀ t ∈ Set.Icc (0:ℝ) (dist x y), (G y x).toFun t = (G x y).toFun (dist x y - t)
