import MyLeanRepo.Kakeya.Cinematic.Section5.CenteredTaylorTransportCore

/-!
# Quadratic-certified centered Taylor transport

This target records the concrete Taylor-tail formulas on the same transport
witness used for cinematicity and metric distortion.  It strengthens the
active transport target only by exposing a property of its intended
construction; the compatibility theorem recovers the original statement.
-/

namespace Kakeya.Cinematic

theorem centered_taylor_quadratic_cinematic_transport :
    CenteredTaylorQuadraticCinematicTransportStatement := by
  exact centeredTaylor_quadratic_cinematic_transport

end Kakeya.Cinematic
