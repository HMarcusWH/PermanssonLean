# Paper-to-Lean crosswalk

Formalization snapshot: `c018f79ea4ce46f4f679ad5bca254509778fc53c`. All declarations below were rechecked against that commit.

| Paper item | Lean declaration | Source |
|---|---|---|
| Thm. 3.1 | `joint_process_well_posed` | `PermanssonLean/StrategicWorld/WellPosedness.lean:173` |
| Prop. 3.2 | `enlarged_state_reduction` | `PermanssonLean/StrategicWorld/WellPosedness.lean:185` |
| Prop. 4.1a | `proposition_4_1a` | `PermanssonLean/Regime/PolishDescriptor.lean:303` |
| Prop. 4.2 | `exactInvariant_iff_survivalForever` | `PermanssonLean/Regime/Persistence.lean:261` |
| Thm. 4.2a | `survivalProbability_eq_killedSurvivalMass` | `PermanssonLean/Regime/SurvivalBridge.lean:225` |
| Def. 4.4a | `IsQSDCertifiedQuasiRegime` | `PermanssonLean/Regime/QuasiStationary.lean:49` |
| Prop. 4.4b | `proposition_4_4b` | `PermanssonLean/Regime/QuasiStationary.lean:193` |
| Prop. 5.2 | `constitutiveMargin_perturbation_abs_le` | `PermanssonLean/Regime/Perturbation.lean:199` |
| Cor. 5.3 | `robustUniformPRCertificate` | `PermanssonLean/Regime/UniformPermansson.lean:119` |
| Prop. 5.4 | `proposition_5_4` | `PermanssonLean/Probability/FinitePrefixTV.lean:388` |
| Thm. 6.1 | `paperIEGR_iff_embeddedExactGR` | `PermanssonLean/EGR/RegimeEmbedding.lean:205` |
| Thm. 6.2 | `paperIPermansson_iff_embeddedRelativePR` | `PermanssonLean/EGR/PermanssonTransport.lean:356` |
| Prop. 7.1 | `exactGR_iff_of_inducedKernel_eq` | `PermanssonLean/Regime/RepresentationEquivalence.lean:102` |
| Prop. 7.4a | `frozenFamilyPR_iff_of_signature_match` | `PermanssonLean/Regime/FamilyEquivalence.lean:161` |
| Thm. 7.4b | `quotient_frozenFamilyPR_iff` | `PermanssonLean/Quotient/Preservation.lean:165` |
| Prop. 7.5 | `nuisancePadding_cannot_create_grounded_change` | `PermanssonLean/Regime/NuisancePadding.lean:137` |
| Prop. 8.1 | `proposition_8_1` | `PermanssonLean/Examples/PeriodicExactGR.lean:585` |
