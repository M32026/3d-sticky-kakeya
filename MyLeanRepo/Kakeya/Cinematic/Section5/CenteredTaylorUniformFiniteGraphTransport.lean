import MyLeanRepo.Kakeya.Cinematic.Section5.CenteredTaylorFiniteGraphTransport
import MyLeanRepo.Kakeya.Cinematic.Section5.CenteredTaylorUniformFiniteGraphTransportInputs

/-!
# Uniform finite graph transport through centered Taylor extension

This is the same-witness bridge needed by uniform-`C²` globalization.  The
quadratic-certified Taylor witness simultaneously supplies the established
finite graph-transport data and the absolute transported two-jet bound.
-/

noncomputable section

namespace Kakeya.Cinematic

theorem centered_taylor_uniform_finite_graph_transport :
    CenteredTaylorUniformFiniteGraphTransportStatement := by
  intro hquadratic K D C_KT lambda M hK hD hC_KT hlambda hM
    family hfamily hbound I hI_len hI_short delta hdelta h4rho
    F hF_sub hsep hKT
  rcases hquadratic K D hK hD family hfamily I hI_len hI_short with
    ⟨transport, hinj, hcinematic, hjet, hquadraticJet, hmetric⟩
  refine ⟨transport, ?_, ?_, hquadraticJet⟩
  · exact centered_taylor_finite_graph_transport_of_witness
      hK hD hC_KT hlambda hfamily hI_len hI_short hdelta h4rho
      hF_sub hsep hKT transport hinj hcinematic hjet hmetric
  · exact
      hasUniformC2Bound_transportImage_of_centeredQuadraticJetExtension
        hM hbound I transport hquadraticJet

end Kakeya.Cinematic
